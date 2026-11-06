(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStepAB0 PmStep PmParStep PmParKit PmBSrcKit PmBParKit PmBReset1 PmBUarK PmBUar PmBSrcUar PmBSrcReadK PmBSrcRead1 PmBSrdP1 PmBSrdP2 PmBSrdP3.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBSrcRead () := ([""; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "Stdlib.ZArith.BinInt.Z."], [["1and"; "1eq"; "2Z"; "0HI"; "0L"; "3fill_buffer_spec"; "3src_read_spec"; "3xsgetn_spec"; "0SCFG_P"; "4le"; "4modulo"; "4sub"; "0ar"; "0sp"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMBSRD.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Ltac vis64 OAV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M0) ?a ?v =>
apply (proj2 (L5A.u64_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis32 OAV := lazymatch goal with |- L5.u32_at ?sg (mrestrict ?H ?M0) ?a ?v =>
apply (proj2 (L5A.u32_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Lemma hx160 : ltac2:(TCodec.tc2 tcn__PmBSrcRead "N'2'1&:r1+@%3221z%63721'0&9&;r2+U@%3221+U0%5241+Q0%?221%8231%:261%;225%=221%D246%F3G1A%F26D%H3I1C%B231%C261p0E1pLM1").
Proof. intros sp.
intros A16. pose proof (Z.mod_pos_bound (sp - 160) 32 ltac:(Lia.lia)) as B.
assert (E16 : (sp - 160) mod 32 = 0 \/ (sp - 160) mod 32 = 16).
{ assert (S16 : (sp - 160) mod 16 = 0) by (replace (sp - 160) with (sp + (-10) * 16) by Lia.lia; rewrite Z_mod_plus_full; exact A16).
pose proof (Z.div_mod (sp - 160) 32 ltac:(Lia.lia)) as D. pose proof (Z.div_mod (sp - 160) 16 ltac:(Lia.lia)) as D2. Lia.lia. }
split; [Lia.lia|]. split.
- rewrite Zminus_mod. rewrite Z.mod_mod by Lia.lia. rewrite Z.sub_diag. reflexivity.
- destruct E16 as [E|E]; rewrite E; replace (sp - 160 - 0) with (sp + (-10) * 16) || replace (sp - 160 - 16) with (sp + (-11) * 16); try Lia.lia;
rewrite Z_mod_plus_full; exact A16.
Qed.
Theorem src_read_ok : ltac2:(TCodec.tc2 tcn__PmBSrcRead "<&5v8v4v<v3%544321&7%146543&6%148765p031p061").
Proof.
intros FB XS. unfold PMB.src_read_spec, PMSPA.src_read_spec, PMSPA.src_spec.
intros fx R M model K LBX FF LK Aw cr sp r fb s str sm Wextra HH AM K0 ENT FRM FRS FOK A10 ARGS WX PA IA BASE INCS KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
destruct ARGS as (p & k & A11 & A12 & Hk & DST). destruct WX as (p' & k' & A11' & A12' & Hp' & Hk' & ->).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
rewrite L5SAR.r11 in A11, A11'. rewrite L5SAR.r12 in A12, A12'. unfold PM.CHUNK in Hk.
change (PMSPA.pm_scr 4) with 20480 in *. pose proof RAok as (Hr1 & Hr2).
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
set (LB := PM.parser_own s ++ LBX) in *.
pose proof (PMBSK.src_vis L ar C HI LY HIok LB FF LK cr Aw M model fb (PMSPA.o_is PMB.AD fb) s sp 20480 HH FOK PA ASTK)
as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
pose proof (PMBSK.iss_vis L ar C HI LY HIok LB FF LK cr Aw M model fb str sm sp 20480 HH FOK IA ASTK)
as ((I1 & I8 & IBIG) & IZ & IW & ICE & IAV & AOI & IOS).
set (os := PMSPA.o_src PMB.AD fb) in *. set (ois := PMSPA.o_is PMB.AD fb) in *. set (op := PMSPA.o_p PMB.AD fb) in *.
assert (Eop : op = fb + 464) by (unfold op, PMSPA.o_p; cbn [pa_off_p PMB.AD ADDR_B]; reflexivity).
assert (Eos : os = fb + 488) by (unfold os, PMSPA.o_src, PMSPA.o_p; cbn [pa_off_p PMB.AD ADDR_B]; lia).
assert (Eois : ois = fb + 96) by (unfold ois, PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_B]; reflexivity).
pose proof (PMBSK.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
pose proof (PMBSK.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 20480 176 HH ASTK ltac:(lia)) as (SL176 & SH176 & V3).
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & _).
pose proof (PMBSK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
pose proof FOK as ((rs & Hfb) & F1024).
destruct (WF _ Hfb) as (FB1 & FB2 & _). unfold ff_addr, ff_class, ff_bytes in FB1, FB2. cbn in FB1, FB2.
assert (AOP : PMSPA.aobjA FF op 384) by (apply (PMBSK.aobj_fb FF fb); [exact FOK| lia| lia]).
destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. destruct sm as [g eg sst].
cbn [PM.p_src PM.p_tb PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & PSRC & _ & _ & PC320 & PTB & _). cbn [PM.p_tb] in PTB.
unfold PMSPA.read_dst in DST. cbn [PM.p_tb] in DST.
destruct PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
fold os ois in S240, S248, SD256, S264, S272, S280, S288.
pose proof IA as (H0i & _ & _ & H16i & _ & _ & _ & _ & _ & _ & _ & _ & IOSB & _ & _).
destruct IOSB as (I0 & I32 & I36 & I40 & _ & _ & _ & _ & IST).
cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMB.AD ADDR_B] in *.
replace (ois + 120 + 32) with (ois + 152) in I32 by lia. replace (ois + 120 + 36) with (ois + 156) in I36 by lia.
replace (ois + 120 + 40) with (ois + 160) in I40 by lia.
set (s0 := PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk) in *.
assert (BOWN : incl (PM.parser_own s0) LB) by (unfold LB; apply incl_appl, incl_refl).
assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (apply BOWN; unfold PM.parser_own, PM.src_own, PM.vec_own; cbn; right; left; reflexivity).
assert (ND : NoDup (map fst LB)) by exact (PMBSK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
destruct (WB _ QIN) as ((Q0 & QI & Q16 & _ & Q4 & QAPP) & _). cbn [fst snd] in Q0, QI, Q16, Q4, QAPP.
destruct (WB _ VIN) as ((VB0 & VBI & _ & _ & VB4 & VAPP) & _). cbn [fst snd] in VB0, VBI, VB4, VAPP.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in QI, VBI.
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QAPP, VAPP, FSAPP.
set (MV := mrestrict (ahid Aw model) M) in *.
assert (DF : 0 <= p /\ p + k <= 2 ^ 47 /\ L5.defined M p k /\ aacc M p k /\ app_rng ar p k
/\ (forall a, p <= a < p + k -> in_block LB a \/ in_fframe FF a)
/\ (forall a, p <= a < p + k -> ~ (sp - 20480 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (op <= a < op + 337) /\ ~ (op + 360 <= a < op + 384)
/\ (forall c0 n0 q0, tb = PM.VLong c0 n0 q0 -> ~ (op + 336 <= a < op + 360))
/\ ~ (qc <= a < qc + 16384) /\ ~ (vb <= a < vb + 32 * 2 ^ vk) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1))
/\ ~ (65536 <= a < 6893568))
/\ (p + k <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p)
/\ (k = 16384 -> exists c0 n0 q0, tb = PM.VLong c0 n0 q0 /\ q0 <= p /\ p + k <= q0 + c0 /\ In (q0, c0) LB)
/\ (PMSPA.aobjA FF p k \/ exists q m, In (q, m) LB /\ q <= p /\ p + k <= q + m)
/\ (p + k <= qc \/ qc + 16384 <= p)).
{ assert (TBb : forall c0 n0 q0, tb = PM.VLong c0 n0 q0 -> In (q0, c0) LB).
{ intros c0 n0 q0 E. apply BOWN. unfold s0, PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own. rewrite E. cbn. right. right. left. reflexivity. }
assert (STb : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LB).
{ intros c1 n1 q1 E. apply SOWN. rewrite E. cbn. left. reflexivity. }
destruct FSAPP as (FSA0 & FSAs & FSA47). destruct QAPP as (QA0 & QAs & QA47). destruct VAPP as (VA0 & VAs & VA47).
destruct DST as [(AOD & Hk8 & DD & AD & APi & APo)|[((n0 & ETB) & D1 & D2)|(c0 & n0 & q0 & ETB & D1 & D2)]].
-
pose proof AOD as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
pose proof (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 p k HH QIN AOD) as APQ.
pose proof (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ vb (32 * 2 ^ vk) p k HH VIN AOD) as APV.
split; [clear - X1 Y1 FSI; lia|]. split; [clear - X2 Y2 FSCEIL SLO SHI SPT; lia|]. split; [exact DD|]. split; [exact AD|].
split; [apply (L5SAR.app_rng_fs L ar C HI HIok LB FF LK cr Aw M _ p k HH); clear - X1 X2 Y1 Y2; lia|].
split; [intros a Ha; right; apply (PMBSR1.in_fframe_of_aobjA FF p k a AOD Ha)|].
split; [|split; [unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FSAs as [Z|Z]; [left|right]; clear - Z X1 X2 Y1 Y2; lia|
split; [intros E; clear - E Hk8; lia| split; [left; exact AOD| clear - APQ; Lia.lia]]]].
intros a Ha. split; [clear - Ha X2 Y2 FSCEIL SLO; lia|]. split; [clear - Ha APi; lia|]. split; [clear - Ha APo; lia|]. split; [clear - Ha APo; lia|].
split; [intros c0 n0 q0 _; clear - Ha APo; lia|]. split; [clear - Ha APQ; lia|]. split; [clear - Ha APV; lia|].
split; [|clear - Ha X1 Y1 FSI; lia].
intros c1 n1 q1 E; destruct (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 p k HH (STb c1 n1 q1 E) AOD) as [Z|Z]; clear - Ha Z; lia.
-
unfold PMSPA.o_tb in D1, D2. fold op in D1, D2.
assert (AOD : PMSPA.aobjA FF p k) by (apply (PMBSK.aobj_fb FF fb); [exact FOK| clear - D1 Eop; lia| clear - D2 Eop; lia]).
pose proof (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 p k HH QIN AOD) as APQ.
pose proof (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ vb (32 * 2 ^ vk) p k HH VIN AOD) as APV.
split; [clear - D1 Eop FB1 FSI; lia|]. split; [clear - D2 Eop FB2 FSCEIL SLO SHI SPT; lia|].
split; [apply (L5.defined_sub M op 384); [exact PDEF| clear - D1; lia| clear - D2 Hk; lia]|].
split; [intros a Ha; apply PC320; clear - Ha D1 D2; lia|].
split; [apply (L5SAR.app_rng_fs L ar C HI HIok LB FF LK cr Aw M _ p k HH); clear - D1 D2 Eop FB1 FB2; lia|].
split; [intros a Ha; right; apply (PMBSR1.in_fframe_of_aobjA FF p k a AOD Ha)|].
split; [|split; [unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FSAs as [Z|Z]; [left|right]; clear - Z D1 D2 Eop FB1 FB2; lia|
split; [intros E; clear - E D1 D2; lia| split; [left; exact AOD| clear - APQ; Lia.lia]]]].
intros a Ha. split; [clear - Ha D2 Eop FB2 FSCEIL SLO; lia|]. split; [clear - Ha D1 Eop Eois; lia|]. split; [clear - Ha D1; lia|]. split; [clear - Ha D2; lia|].
split; [intros c0 n1 q0 E; rewrite ETB in E; discriminate E|]. split; [clear - Ha APQ; lia|]. split; [clear - Ha APV; lia|].
split; [|clear - Ha D1 Eop FB1 FSI; lia].
intros c1 n1 q1 E; destruct (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 p k HH (STb c1 n1 q1 E) AOD) as [Z|Z]; clear - Ha Z; lia.
-
pose proof (TBb c0 n0 q0 ETB) as TIN. rewrite ETB in PTB.
pose proof PTB as (_ & _ & _ & _ & _ & _ & _ & _ & TBD & TBC).
destruct (WB _ TIN) as ((T0 & TI & _ & _ & T4 & TAPP) & _). cbn [fst snd] in T0, TI, T4, TAPP.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in TI. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in TAPP. destruct TAPP as (TA0 & TAs & TA47).
assert (NQ : q0 <> qc).
{ intros E. subst q0. unfold LB, s0, PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own in ND. rewrite ETB in ND. cbn in ND.
inversion ND as [|x l NI _]. apply NI. apply PMBSK.elem_of_InA. right. left. reflexivity. }
assert (NV : q0 <> vb).
{ intros E. subst q0. unfold LB, s0, PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own in ND. rewrite ETB in ND. cbn in ND.
inversion ND as [|x l _ ND2]. inversion ND2 as [|x2 l2 NI _]. apply NI. apply PMBSK.elem_of_InA. left. reflexivity. }
pose proof (PMBSK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 qc 16384 HH TIN QIN NQ) as APQ.
pose proof (PMBSK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 vb (32 * 2 ^ vk) HH TIN VIN NV) as APV.
pose proof (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 op 384 HH TIN AOP) as APP.
pose proof (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 ois 272 HH TIN AOI) as API.
split; [clear - D1 T0; lia|]. split; [clear - D2 T4 SLO SHI SPT; lia|].
split; [apply (L5.defined_sub M q0 c0); [exact TBD| clear - D1; lia| clear - D2; lia]|].
split; [intros a Ha; apply TBC; clear - Ha D1 D2; lia|].
split; [apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK cr Aw M _ q0 c0 p k HH TIN); clear - D1 D2; lia|].
split; [intros a Ha; left; apply (PMBSR1.in_block_of LB q0 c0 a TIN); clear - Ha D1 D2; lia|].
split; [|split; [unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TAs as [Z|Z]; [left|right]; clear - Z D1 D2; lia
| split; [intros _; exists c0, n0, q0; split; [exact ETB|]; split; [clear - D1; lia|]; split; [clear - D2; lia| exact TIN]|
split; [right; exists q0, c0; split; [exact TIN|]; split; [exact D1| exact D2]| clear - APQ D1 D2; Lia.lia]]]].
intros a Ha. split; [clear - Ha D1 D2 T4 SLO; lia|]. split; [clear - Ha D1 D2 API; lia|]. split; [clear - Ha D1 D2 APP; lia|]. split; [clear - Ha D1 D2 APP; lia|].
split; [intros c2 n2 q2 _; clear - Ha D1 D2 APP; lia|]. split; [clear - Ha D1 D2 APQ; lia|]. split; [clear - Ha D1 D2 APV; lia|].
split; [|clear - Ha D1 D2 TI T0; lia].
intros c1 n1 q1 E. assert (SIN : In (q1, c1) LBX) by (apply INCS; rewrite E; left; reflexivity).
assert (NS : q0 <> q1) by (apply (PMBSK.fst_neq_appA (PM.parser_own s0) LBX q0 c0 q1 c1); [exact ND| unfold s0, PM.parser_own, PM.vs_own; rewrite ETB; cbn; right; right; left; reflexivity| exact SIN]).
destruct (PMBSK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 q1 c1 HH TIN (STb c1 n1 q1 E) NS) as [Z|Z]; clear - Ha D1 D2 Z; lia. }
destruct DF as (DP0 & DP1 & DDP & DAP & DAPP & DCL & DX & DSH & D16K & DLOC & DQA).
assert (pk : p' = p /\ k' = k).
{ rewrite A11 in A11'. rewrite A12 in A12'. apply (f_equal bv_unsigned) in A11', A12'.
rewrite !L5.unsigned_lit in A11', A12' by (clear - Hp' Hk' DP0 DP1 Hk; lia). split; congruence. }
destruct pk as (-> & ->). clear A11' A12'.
destruct FSAPP as (FSA0 & FSAs & FSA47). destruct QAPP as (QA0 & QAs & QA47). destruct VAPP as (VA0 & VAs & VA47).
assert (TBb : forall c0 n0 q0, tb = PM.VLong c0 n0 q0 -> In (q0, c0) LB).
{ intros c0 n0 q0 E. apply BOWN. unfold s0, PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own. rewrite E. cbn. right. right. left. reflexivity. }
assert (APQO : forall o n, PMSPA.aobjA FF o n -> qc + 16384 <= o \/ o + n <= qc).
{ intros o n AOo. exact (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 o n HH QIN AOo). }
set (WA := PMSPA.W_src PMB.AD fb (PM.SRC qc de rem) ++ [(p, k)]).
assert (OUTWA : forall i, ~ (os + 256 <= i < os + 296) -> ~ (ois + 40 <= i < ois + 48) -> ~ (ois + 152 <= i < ois + 156) ->
~ (qc <= i < qc + 16384) -> ~ (p <= i < p + k) -> L5.outside WA i).
{ intros i N1 N2 N3 N4 N5 r0 Hr. unfold WA, PMSPA.W_src, PMSPA.W_srcf in Hr. cbn [PM.sr_qc app] in Hr. fold os ois in Hr. unfold L5.in_rng.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold PM.CHUNK; clear - N1 N2 N3 N4 N5; lia. }
assert (WAPP : PMKB.wapp WA).
{ unfold WA, PMSPA.W_src, PMSPA.W_srcf. cbn [PM.sr_qc app]. fold os ois. unfold BIGSHADOW_LO, BIGSHADOW_HI in OBIG, IBIG, DSH.
apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - OBIG; Lia.lia|].
apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - IBIG; Lia.lia|].
apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - IBIG; Lia.lia|].
apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK; clear - QAs; Lia.lia|].
apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - DSH; Lia.lia| apply PMKB.wapp_nil]. }
assert (OUTIMG : forall a, 65536 <= a < 6893568 -> L5.outside WA a).
{ intros a Ha. apply OUTWA; [clear - Ha O1; lia| clear - Ha I1; lia| clear - Ha I1; lia| clear - Ha QI; lia|].
intros Y. destruct (DX a Y) as (_ & _ & _ & _ & _ & _ & _ & _ & X9). apply X9. exact Ha. }
assert (PARS : forall (M3 : word -> option byte) (de' rem' : Z),
L5SAR.ek L ar LB FF sp 20480 WA M M3 -> L5SAR.dk L ar LB FF sp 20480 M M3 ->
L5.u64_at RSEGS M3 (os + 264) qc -> L5.u64_at RSEGS M3 (os + 272) 16384 ->
L5.u64_at RSEGS M3 (os + 280) de' -> L5.u64_at RSEGS M3 (os + 288) rem' ->
qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M3 op ois (PMSPA.with_src s0 (PM.SRC qc de' rem'))).
{ intros M3 de' rem' EK DK C264 C272 C280 C288 Q1' Q2' Q3'.
assert (OUTP : forall i, op <= i < op + 384 -> ~ (op + 280 <= i < op + 320) -> ~ (p <= i < p + k) -> L5.outside WA i).
{ intros i Hi N Np. apply OUTWA; [clear - Hi N Eos Eop; lia| clear - Hi Eois Eop; lia| clear - Hi Eois Eop; lia| |exact Np].
destruct (APQO op 384 AOP) as [Z|Z]; clear - Hi Z; lia. }
assert (NPk : forall i, (op <= i < op + 337 \/ op + 360 <= i < op + 384) -> ~ (p <= i < p + k)).
{ intros i Hi Y. destruct (DX i Y) as (_ & _ & X3 & X4 & _). clear - Hi X3 X4. lia. }
assert (VNE : vb <> qc).
{ intros E. subst vb. unfold LB, s0, PM.parser_own, PM.src_own, PM.vec_own in ND. cbn in ND. inversion ND as [|x l NI _]. apply NI. apply PMBSK.elem_of_InA. left. reflexivity. }
apply (PMBSR1.parser_src_tbA M M3 op ois s0 de' rem' PA); cbn [s0 PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; unfold PM.CHUNK.
* clear - Eop FB1 FSI. lia.
* clear - Eop FB2 FSA47. lia.
* apply (PMKB.agA_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB op 280); [apply (PMBSK.aobj_fb FF fb); [exact FOK| clear - Eop; lia| clear - Eop; lia]|].
intros i Hi. apply OUTP; [clear - Hi; lia| clear - Hi; lia| apply NPk; clear - Hi; lia].
* apply (PMKB.agA_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB (op + 320) 17); [apply (PMBSK.aobj_fb FF fb); [exact FOK| clear - Eop; lia| clear - Eop; lia]|].
intros i Hi. apply OUTP; [clear - Hi; lia| clear - Hi; lia| apply NPk; clear - Hi; lia].
* apply (PMKB.agA_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB (op + 360) 24); [apply (PMBSK.aobj_fb FF fb); [exact FOK| clear - Eop; lia| clear - Eop; lia]|].
intros i Hi. apply OUTP; [clear - Hi; lia| clear - Hi; lia| apply NPk; clear - Hi; lia].
* apply (PMKB.agsh_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB (op + 280) 104). apply (PMBSK.aobj_fb FF fb); [exact FOK| clear - Eop; lia| clear - Eop; lia].
* apply (PMBSK.defined_dk L ar LB FF sp 20480 M M3 op 384 DK); [| clear - Eop FB1 FSI; lia| clear - Eop FB2 FSA47; lia| exact PDEF].
intros i Hi. apply PMBSR1.cl_of_bf. right. apply (PMBSR1.in_fframe_of_aobjA FF op 384 i AOP Hi).
* intros c0 n0 q0 E. pose proof (TBb c0 n0 q0 E) as TIN. pose proof PTB as PTB'. rewrite E in PTB'.
destruct PTB' as (_ & _ & _ & _ & _ & _ & _ & _ & TBD & _). destruct (BRB _ TIN) as (T0 & T1). cbn [fst snd] in T0, T1.
split; [|split].
-- apply (PMKB.agA_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB (op + 336) 24); [apply (PMBSK.aobj_fb FF fb); [exact FOK| clear - Eop; lia| clear - Eop; lia]|].
intros i Hi. apply OUTP; [clear - Hi; lia| clear - Hi; lia|]. intros Y. destruct (DX i Y) as (_ & _ & _ & _ & X5 & _). apply (X5 c0 n0 q0 E). clear - Hi; lia.
-- apply (PMBSK.defined_dk L ar LB FF sp 20480 M M3 q0 c0 DK); [| clear - T0; lia| clear - T1; lia| exact TBD].
intros i Hi. apply PMBSR1.cl_of_bf. left. apply (PMBSR1.in_block_of LB q0 c0 i TIN Hi).
-- apply (PMBSK.agsh_blk L ar LB FF sp 20480 WA M M3 q0 c0 EK WAPP TIN); clear - T0 T1; lia.
* apply (PMBSK.defined_dk L ar LB FF sp 20480 M M3 qc 16384 DK); [| clear - Q0; lia| clear - Q4 SLO SHI SPT; lia| exact DCH].
intros i Hi. apply PMBSR1.cl_of_bf. left. apply (PMBSR1.in_block_of LB qc 16384 i QIN Hi).
* apply (PMBSK.agsh_blk L ar LB FF sp 20480 WA M M3 qc 16384 EK WAPP QIN); [clear - Q0; lia| clear - Q4 SLO SHI SPT; lia].
* clear - VB0. lia.
* clear - VB4 SLO SHI SPT. lia.
* apply (PMKB.agA_blk L ar LB FF sp 20480 WA M M3 EK WAPP BRB vb _ VIN). intros i Hi.
destruct (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ vb (32 * 2 ^ vk) os 296 HH VIN AO) as [Z1|Z1];
destruct (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ vb (32 * 2 ^ vk) ois 272 HH VIN AOI) as [Z2|Z2];
destruct (PMBSK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ vb (32 * 2 ^ vk) qc 16384 HH VIN QIN VNE) as [Z3|Z3].
all: apply OUTWA; [clear - Hi Z1; lia| clear - Hi Z2; lia| clear - Hi Z2; lia| clear - Hi Z3; lia|].
all: intros Y; destruct (DX i Y) as (_ & _ & _ & _ & _ & _ & X7 & _); apply X7; exact Hi.
* replace (op + 288) with (os + 264) by (clear - Eop Eos; lia). exact C264.
* replace (op + 296) with (os + 272) by (clear - Eop Eos; lia). exact C272.
* replace (op + 304) with (os + 280) by (clear - Eop Eos; lia). exact C280.
* replace (op + 312) with (os + 288) by (clear - Eop Eos; lia). exact C288.
* exact Q1'.
* exact Q2'.
* exact Q3'. }
assert (AGSHP : forall M0 M1 W, L5SAR.ek L ar LB FF sp 20480 W M0 M1 -> PMKB.wapp W -> PMFA.agsh M0 M1 p k).
{ intros M0 M1 W E WP. destruct DLOC as [AOD|(q & m & Hq & X1 & X2)].
- exact (PMKB.agsh_obj L ar LB FF sp 20480 W M0 M1 E WP FRB p k AOD).
- destruct (BRB _ Hq) as (Y1 & Y2). cbn [fst snd] in Y1, Y2.
intros x Hx. apply (PMBSK.agsh_blk L ar LB FF sp 20480 W M0 M1 q m E WP Hq ltac:(clear - Y1; lia) ltac:(clear - Y2; lia)). clear - Hx X1 X2; lia. }
assert (CLP : forall a sp0 scr0, p <= a < p + k -> aclient L ar LB FF sp0 scr0 a) by (intros a sp0 scr0 Ha; apply PMBSR1.cl_of_bf; exact (DCL a Ha)).
assert (CLPw : forall a sp0 scr0, p <= a < p + k -> aclientw L ar LB FF sp0 scr0 a) by (intros a sp0 scr0 Ha; apply PMBSR1.cl_of_bf; exact (DCL a Ha)).
assert (CLQ : forall a sp0 scr0, qc <= a < qc + 16384 -> aclient L ar LB FF sp0 scr0 a).
{ intros a sp0 scr0 Ha. apply PMBSR1.cl_of_bf. left. exact (PMBSR1.in_block_of LB qc 16384 a QIN Ha). }
assert (QP : 0 <= p < 2 ^ 64 /\ 0 <= k < 2 ^ 64 /\ 4096 <= p <= 140737488338944).
{ split; [clear - DP0 DP1 Hk; lia|]. split; [clear - Hk; lia|].
destruct DLOC as [AOD|(q & m & Hq & Y1 & Y2)].
- pose proof AOD as (f & Hf & Y1 & Y2). destruct (WF f Hf) as (Z1 & Z2 & _). clear - Y1 Y2 Z1 Z2 FSI FSCEIL SLO SHI SPT Hk; lia.
- destruct (WB _ Hq) as ((Z0 & _ & _ & _ & Z4 & _) & _). cbn [fst snd] in Z0, Z4. clear - Z0 Z4 Y1 Y2 SLO SHI SPT Hk; lia. }
destruct QP as (QP0 & QK0 & QPR).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
assert (V3' : L5.writable RSEGS MV (sp - 160) 160) by (apply (L5.writable_sub RSEGS MV (sp - 176) 176); [exact V3| lia| lia]).
cfeed P (PMBSRP1.bsrA_conc fx R MV (fun j => match j with 2%nat => sp | 36%nat => os | 37%nat => p | 38%nat => k | _ => 0 end)) ltac:(first [assumption | unfold PMBSRP1.aligned; assumption | clear - SL176 SHI SPT; lia | clear - O1; lia | clear - Hk; lia]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & T2 & T8 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C160).
set (X := (sp - 160) - (sp - 160) mod 32) in *.
assert (HX : sp - 176 <= X <= sp - 160 /\ X mod 32 = 0 /\ X mod 16 = 0) by (unfold X; exact (hx160 sp A16)).
destruct HX as (HX1 & HX32 & HX16).
destruct (PMBSU.andi_sp Ra (sp - 160) (Z_to_bv 12 4064) ltac:(lia) eq_refl T2) as (T2' & TO).
pose proof (PMBSU.andi_to fxa Ra Mav 0xb069c (ltac:(oW' 0xb069c%Z)) _ _ _ (ltac:(oF' 0xb069c%Z)) eq_refl (ltac:(oD' 0xb069c%Z)) eq_refl ltac:(lia) ltac:(lia)) as MSA.
set (Rat := regupd Ra 2%bv (v_andi (getr Ra 2%bv) (bv_signed (Z_to_bv 12 4064 : bv 12)))) in MSA, T2', TO.
fold X in T2'.
assert (U8 : getr Rat (reg 8) = Z_to_bv 64 sp) by (rewrite (TO 8%nat) by lia; exact T8).
assert (U10 : getr Rat (reg 10) = Z_to_bv 64 os) by (rewrite (TO 10%nat) by lia; rewrite (KSa 10%nat) by inl; exact A10).
assert (U11 : getr Rat (reg 11) = Z_to_bv 64 p) by (rewrite (TO 11%nat) by lia; rewrite (KSa 11%nat) by inl; rewrite <- L5SAR.r11; exact A11).
assert (U12 : getr Rat (reg 12) = Z_to_bv 64 k) by (rewrite (TO 12%nat) by lia; rewrite (KSa 12%nat) by inl; rewrite <- L5SAR.r12; exact A12).
assert (WXa : L5.writable RSEGS Mav X 56).
{ apply (L5.writable_grows RSEGS MV Mav X 56 MGa). apply (L5.writable_sub RSEGS MV (sp - 176) 176); [exact V3| lia| lia]. }
assert (VMa : L5.img_clear Mav 65536 1269760 /\ L5.u64_at RSEGS Mav 1296952 2147450880 /\ L5.u32_at RSEGS Mav 1296960 1).
{ assert (AG1 : forall i, 0 <= i < 1296968 -> Mav (Z_to_bv 64 i) = MV (Z_to_bv 64 i)) by (intros i Hi; apply FRZa; [lia| clear - Hi SL176 SHI SPT; lia]).
split; [intros i Hi; rewrite AG1 by lia; apply V0; exact Hi|].
split; [apply (L5C.u64_at_agree RSEGS MV Mav); [intros i Hi; rewrite AG1 by lia; reflexivity| lia| lia| exact V1]|].
apply (PMF.u32_at_agree RSEGS MV Mav); [intros i Hi; rewrite AG1 by lia; reflexivity| lia| lia| exact V2]. }
destruct VMa as (VMa0 & VMa1 & VMa2).
cfeed P (PMBSRP1.bsrA2_conc fxa Rat Mav (fun j => match j with 2%nat => sp | 36%nat => os | 37%nat => p | 38%nat => k | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBSRP1.aligned; assumption | clear - SL176 SHI SPT HX1; lia | clear - O1; lia | clear - Hk; lia | clear - HX1 SL176 SHI SPT; lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1b & T9b & T10b & T11b & T12b & T19b & T22b & T27b & C24X).
assert (MS01 : msteps RSEGS (L5A.st fx R 0xb065c MV) (L5A.st fx1 R1 0x5d670 M1v))
by (eapply msteps_trans; [exact MSa| eapply msteps_trans; [exact MSA| exact MS1]]).
assert (MG01 : mem_grows MV M1v) by (intros x Hx; apply MG1; apply MGa; exact Hx).
assert (SVa : forall a v, sp - 104 <= a -> a + 8 <= sp -> L5.u64_at RSEGS Mav a v -> L5.u64_at RSEGS M1v a v).
{ intros a v Ha1 Ha2 Y. apply (L5C.u64_at_agree RSEGS Mav M1v); [intros i Hi; apply FRZ1; [clear - Hi Ha1 Ha2 SL176 SHI SPT; lia| clear - Hi Ha1 Ha2 HX1; lia]| clear - Ha1 SL176 SPT; lia| clear - Ha2 SHI SPT; lia| exact Y]. }
unfold PMSPA.cfg. cbn [pa_src_read PMB.AD ADDR_B].
apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb065c R1 0x5d670 M1v (fun a => X <= a < sp) K HH AM MS01 MG01).
{ intros a Ha N. rewrite FRZ1 by (first [exact Ha| intros Y; apply N; clear - Y HX1; lia]). apply FRZa; [exact Ha| intros Y; apply N; clear - Y HX1; lia]. }
{ intros a Ha Wa. split; [|intros Y; clear - Wa Y SL176 SPT HX1; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL176 SHI SPT HX1; lia| intros Y; clear - Y; lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict (ahid Aw model) M1 = M1v) in VIS1.
assert (NCS0 : forall a, X <= a < sp -> ~ aclient L ar LB FF sp 20480 a).
{ intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 20480 a HH SPT Hc) as [Y|Y].
- clear - Xa Y HX1; lia.
- clear - Xa Y SL176 HX1; lia. }
assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [] M M1).
{ apply (L5SAR.ek_piece L ar LB FF sp 20480 [] M M1 (fun a => X <= a < sp) FR1). intros a Ha Hc _ Y. apply (NCS0 a); [exact Y| exact Hc]. }
assert (DK01 : L5SAR.dk L ar LB FF sp 20480 M M1) by (apply L5SAR.dk_grows; exact MGM1).
assert (SV1 : forall a v, X <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v Ha1 Ha2 Y. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a v (VISs a 8 ltac:(clear - Ha1 SL176 SPT HX1; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL176 SPT HX1; lia) ltac:(clear - Ha2 SHI SPT; lia))).
rewrite VIS1. exact Y. }
assert (OWN1 : PMBSU.own13 sp R M1).
{ unfold PMBSU.own13. split; [apply SV1; [clear - HX1; lia| clear; lia| apply SVa; [clear; lia| clear; lia| exact C8]]|].
split; [apply SV1; [clear - HX1; lia| clear; lia| apply SVa; [clear; lia| clear; lia| exact C16]]|].
split; [apply SV1; [clear - HX1; lia| clear; lia| apply SVa; [clear; lia| clear; lia| exact C24]]|].
split; [apply SV1; [clear - HX1; lia| clear; lia| apply SVa; [clear; lia| clear; lia| exact C32]]|].
split; [apply SV1; [clear - HX1; lia| clear; lia| apply SVa; [clear; lia| clear; lia| exact C40]]|].
split; [apply SV1; [clear - HX1; lia| clear; lia| apply SVa; [clear; lia| clear; lia| exact C48]]|].
split; [apply SV1; [clear - HX1; lia| clear; lia| apply SVa; [clear; lia| clear; lia| exact C56]]|].
split; [apply SV1; [clear - HX1; lia| clear; lia| apply SVa; [clear; lia| clear; lia| exact C64]]|].
split; [apply SV1; [clear - HX1; lia| clear; lia| apply SVa; [clear; lia| clear; lia| exact C72]]|].
split; [apply SV1; [clear - HX1; lia| clear; lia| apply SVa; [clear; lia| clear; lia| exact C80]]|].
split; [apply SV1; [clear - HX1; lia| clear; lia| apply SVa; [clear; lia| clear; lia| exact C88]]|].
split; [apply SV1; [clear - HX1; lia| clear; lia| apply SVa; [clear; lia| clear; lia| exact C96]]|].
apply SV1; [clear - HX1; lia| clear; lia| apply SVa; [clear; lia| clear; lia| exact C104]]. }
assert (C24' : L5.u64_at RSEGS M1 (X + 24) p) by (apply SV1; [clear; lia| clear - HX1; lia| exact C24X]).
clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 C160 SVa.
assert (FRk1 : ff_room 1 FF LK) by (apply (PMBUAR.ff_room_of 4 FF LK 1 FRM); [clear; lia| right; left; reflexivity]).
change 0x5d670 with (PMB.SM_PC 1).
apply (PMBUAR.uar_sm L ar C HI LY HIok 1 LB [] FF LK cr Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R)
fx1 R1 M M1 model model1 K 0xb06d4 ltac:(right; left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
{ rewrite L5K.rl2. rewrite (KS1 2%nat) by inl. exact T2'. }
{ rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite (TO 4%nat) by lia. rewrite (KSa 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
{ rewrite L5K.rl1. exact T1b. }
{ reflexivity. }
{ clear; lia. }
{ exact HX16. }
{ clear - HX1; lia. } { clear - HX1; lia. } { clear; lia. } { clear; lia. }
{ intros a Ha. exact Ha. }
{ intros Ma Mb OWa AGa. apply (PMBSU.own13_agree sp R Ma Mb ltac:(clear - SL176 SPT; lia) ltac:(clear - SHI SPT; lia) OWa AGa). }
{ exact FRk1. }
{ intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. change (128 - 8) with 120 in *.
pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 1) with 128 in *.
pose proof (L5SAR.ek_trans L ar LB FF sp 20480 [] M M1 M2 EK01 EK12f) as EK02f.
pose proof (L5SAR.dk_trans L ar LB FF sp 20480 M M1 M2 DK01 DK12f) as DK02f.
assert (PA2 : PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M2 op ois s0).
{ apply (PMKB.parser_keepA RSEGS PMB.AD L ar LB FF sp 20480 [] M M2 EK02f PMKB.wapp_nil FRB BRB _ _ _ AOP);
[exact BOWN| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA]. }
assert (IA2 : PM.iss_at RSEGS PMB.AD PMSPA.accA M2 ois str (PM.STRM g eg sst)).
{ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 [] M M2 EK02f PMKB.wapp_nil FRB BRB ois str _ AOI); [exact SOWN| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]. }
assert (BASE2 : PMSTA.base_okA RSEGS PMB.AD M2) by (apply (PMBSK.base_keep L ar C LY LB FF sp 20480 [] M M2 EK02f); [intros a _ r0 []| exact BASE]).
assert (HH2 : ri_inv HI LB ((F, 1, X + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
set (FF' := (F, 1, X + 32) :: FF) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMBUAR.frame_okA_push FF fb F 1 (X + 32) FOK).
set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
pose proof (PMBSK.src_vis L ar C HI LY HIok LB FF' LK2 cr Aw M2 model2 fb ois s0 sp 20480 HH2 FOK' PA2 ASTK2)
as ((_ & _ & _) & OZ2 & OW2 & _ & OAV2 & AO2 & _ & _). fold os MV2 in OZ2, OW2, OAV2, AO2.
pose proof (PMBSK.mach_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 HH2 BASE2) as (W0 & W1 & W2). fold MV2 in W0, W1, W2.
pose proof (PMBSK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 20480 176 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2). fold MV2 in SWR2.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK2 cr Aw M2 model2 HH2) as (_ & VISs2 & _).
assert (CLos : forall i, 0 <= i < 296 -> aclient L ar ([] ++ LB) FF 0 0 (os + i)).
{ intros i Hi. destruct AO as (f & Hf & X1 & X2). unfold aclient, aclient_g. do 3 right; left. exists f. split; [exact Hf|]. clear - X1 X2 Hi; lia. }
destruct (APART os 296 0 0 CLos ltac:(clear; lia)) as (AoF & AoSF & AoFL).
assert (CLsh : forall i, 0 <= i < 37 -> aclient L ar ([] ++ LB) FF 0 0 (os / 8 + SB + i)).
{ intros i Hi. destruct AO as (f & Hf & X1 & X2). unfold aclient, aclient_g. do 5 right; left. exists f. split; [exact Hf|].
unfold in_shadow_of, S.
assert (D1 : ff_addr f / 8 <= os / 8) by (apply Z.div_le_mono; clear - X1; lia).
assert (D2 : (os + i * 8) / 8 = os / 8 + i) by (apply Z.div_add; clear; lia).
assert (D3 : (os + i * 8) / 8 <= (ff_addr f + ff_bytes (ff_class f) - 1) / 8) by (apply Z.div_le_mono; clear - X2 Hi; lia).
clear - D1 D2 D3 Hi. lia. }
destruct (APART (os / 8 + SB) 37 0 0 CLsh ltac:(clear; lia)) as (_ & AsoSF & _).
unfold SB in AsoSF.
destruct (APART p k 0 0 ltac:(intros i Hi; apply CLP; clear - Hi; lia) ltac:(clear - Hk; lia)) as (ApF & ApSF & ApFL).
unfold SB in ApSF.
assert (QQ0 : 0 <= sp < 2 ^ 64 /\ 0 <= os < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= X < 2 ^ 64 /\ 0 <= qc < 2 ^ 64)
by (clear - SL176 SHI SPT O1 GFR GFLR HX1 Q0 Q4; lia).
destruct QQ0 as (Q0a & Q0b & Q0c & Q0d & Q0e & Q0f).
assert (QX : 140735332487168 <= X <= 140737488355168) by (clear - SL176 SHI SPT HX1; lia).
assert (QXa : X mod 32 = 0) by exact HX32.
assert (QXo : X + 56 <= os \/ os + 296 <= X) by (clear - OCE SL176 HX1; lia).
assert (QXF : X + 56 <= F \/ F + 128 <= X) by (clear - GFCEIL SL176 HX1; lia).
assert (QXfl : X + 56 <= fl \/ fl + 1 <= X) by (clear - GFLR SL176 HX1; lia).
assert (QFR : 6893568 <= F <= 140737488355200) by (clear - GFR; lia).
assert (QFI : F + 128 <= 65536 \/ 65536 + 1204224 <= F) by (clear - GFR; lia).
assert (QFL : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
assert (QoF : os + 296 <= F \/ F + 128 <= os) by exact AoF.
assert (QoFL : os + 296 <= fl \/ fl + 1 <= os) by exact AoFL.
assert (QoSF : ((os / 8) + 2147450880) + 37 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= ((os / 8) + 2147450880)) by exact AsoSF.
assert (FLCv : L5.u64_at RSEGS MV2 (F + 120) fl) by (replace (F + 120) with (F + 128 - 8) by (clear; lia); exact FLC).
assert (SV2 : forall a v, X <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS MV2 a v).
{ intros a v Ha1 Ha2 Y. apply (proj2 (L5A.u64_at_vis H2 M2 a v (VISs2 a 8 ltac:(clear - Ha1 SL176 SPT HX1; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL176 SPT HX1; lia) ltac:(clear - Ha2 SHI SPT; lia))).
apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AGF; clear - Ha1 Ha2 Hi; lia| clear - Ha1 SL176 SPT HX1; lia| clear - Ha2 SHI SPT; lia| exact Y]. }
assert (C24v : L5.u64_at RSEGS MV2 (X + 24) p) by (apply SV2; [clear; lia| clear - HX1; lia| exact C24']).
assert (WX2 : L5.writable RSEGS MV2 X 56) by (apply (L5.writable_sub RSEGS MV2 (sp - 176) 176); [exact SWR2| clear - HX1; lia| clear - HX1; lia]).
pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PSRC2 & _).
destruct PSRC2 as (_ & _ & SD2 & S264b & S272b & S280b & S288b & _ & _ & _ & _ & _ & _ & _). cbn [PM.p_src s0 PM.sr_qc PM.sr_de PM.sr_rem] in SD2, S264b, S272b, S280b, S288b.
fold os in SD2, S264b, S272b, S280b, S288b. unfold PM.CHUNK in S272b.
assert (VS264 : L5.u64_at RSEGS MV2 (os + 264) qc) by (apply (proj2 (L5A.u64_at_vis _ M2 (os + 264) qc ltac:(apply OAV2; clear; lia) ltac:(clear - O1; lia) ltac:(clear - O1; lia))); exact S264b).
assert (VS272 : L5.u64_at RSEGS MV2 (os + 272) 16384) by (apply (proj2 (L5A.u64_at_vis _ M2 (os + 272) _ ltac:(apply OAV2; clear; lia) ltac:(clear - O1; lia) ltac:(clear - O1; lia))); exact S272b).
assert (VS280 : L5.u64_at RSEGS MV2 (os + 280) de) by (apply (proj2 (L5A.u64_at_vis _ M2 (os + 280) de ltac:(apply OAV2; clear; lia) ltac:(clear - O1; lia) ltac:(clear - O1; lia))); exact S280b).
assert (VS288 : L5.u64_at RSEGS MV2 (os + 288) rem) by (apply (proj2 (L5A.u64_at_vis _ M2 (os + 288) rem ltac:(apply OAV2; clear; lia) ltac:(clear - O1; lia) ltac:(clear - O1; lia))); exact S288b).
assert (VD256 : L5.defined MV2 (os + 256) 8) by (apply (proj2 (L5A.defined_vis _ M2 (os + 256) 8 ltac:(apply OAV2; clear; lia))); exact SD2).
assert (R2c : forall j, In j L5SAR.cs_all -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj; apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj)).
assert (B2R : getr R2 (reg 2) = Z_to_bv 64 X) by (rewrite (R2c 2%nat) by inl; rewrite (KS1 2%nat) by inl; exact T2').
assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; rewrite (KS1 8%nat) by inl; exact U8).
assert (B9R : getr R2 (reg 9) = Z_to_bv 64 X) by (rewrite (R2c 9%nat) by inl; exact T9b).
assert (B19R : getr R2 (reg 19) = Z_to_bv 64 os) by (rewrite (R2c 19%nat) by inl; exact T19b).
assert (B22R : getr R2 (reg 22) = Z_to_bv 64 k) by (rewrite (R2c 22%nat) by inl; exact T22b).
assert (B27R : getr R2 (reg 27) = Z_to_bv 64 2147450880) by (rewrite (R2c 27%nat) by inl; exact T27b).
assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
assert (B34 : forall j, In j [3; 4]%nat -> getr R2 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (R2c j) by (destruct Hj as [<-|[<-|[]]]; inl). rewrite (KS1 j) by (destruct Hj as [<-|[<-|[]]]; inl).
rewrite (TO j) by (destruct Hj as [<-|[<-|[]]]; lia). apply KSa. destruct Hj as [<-|[<-|[]]]; inl. }
assert (EXITP : forall (fx7 : FPState) R7 M7 model7 LK7 Aw7 (de' rem' g' st' d : Z),
PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M7 model7 LK7 cr Aw7 ->
getr R7 (reg 2) = Z_to_bv 64 X -> getr R7 (reg 8) = Z_to_bv 64 sp -> getr R7 (reg 9) = Z_to_bv 64 X ->
getr R7 (reg 22) = Z_to_bv 64 d -> getr R7 (reg 25) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R7 (reg 26) = Z_to_bv 64 F ->
getr R7 (reg 3) = getr R (reg 3) -> getr R7 (reg 4) = getr R (reg 4) ->
L5.u64_at RSEGS M7 (X + 16) F ->
L5.u64_at RSEGS M7 (os + 264) qc -> L5.u64_at RSEGS M7 (os + 272) 16384 -> L5.u64_at RSEGS M7 (os + 280) de' -> L5.u64_at RSEGS M7 (os + 288) rem' ->
qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
PM.iss_at RSEGS PMB.AD PMSPA.accA M7 ois str (PM.STRM g' eg st') ->
g <= g' <= eg -> (sst = 2 -> st' = 2) ->
0 <= d <= k -> (rem + (eg - g)) - (rem' + (eg - g')) = d ->
(1 <= rem -> 1 <= d) -> (d = 0 -> rem' = 0 /\ st' = 2) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx7 R7 0xb0b3c M7 model7) K).
{ intros fx7 R7 M7 model7 LK7 Aw7 de' rem' g' st' d BI7 G72 G78 G79 G722 G725 G726 G73 G74 S16 C264 C272 C280 C288 Q1' Q2' Q3' IA7 Hg Hst2 Hd Hcons HR1 HR0.
assert (DD7 : L5.defined M7 p d).
{ pose proof BI7 as (_ & _ & _ & _ & _ & _ & _ & DK7' & _).
apply (L5.defined_sub M7 p k); [| clear; lia| clear - Hd; lia].
apply (PMBSK.defined_dk L ar LB FF sp 20480 M M7 p k DK7'); [intros i Hi; apply CLP; exact Hi| clear - DP0; lia| clear - DP1; lia| exact DDP]. }
set (H7 := ahid Aw7 model7) in *. set (MV7 := mrestrict H7 M7) in *.
destruct (PMBUK.vis_facts L ar C HI LYa HIok M model LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr [] G
WA [] M7 model7 LK7 cr Aw7 BI7) as ((WS7 & _ & _ & _ & _) & OWN7 & (FD7 & FW7 & FSW7 & FLC7 & FLW7) & (FLCc7 & FLV7 & VF7 & VS7 & VSH7)).
change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. fold H7 MV7 in WS7, OWN7, FD7, FW7, FSW7, FLC7, FLW7.
replace (F + 128 - 8) with (F + 120) in FLC7 by (clear; lia).
assert (WSE7 : L5.writable RSEGS MV7 (sp - 160) 160) by (apply (L5.writable_sub RSEGS MV7 X (sp - X)); [exact WS7| clear - HX1; lia| clear; lia]).
assert (WSX7 : L5.writable RSEGS MV7 X 56) by (apply (L5.writable_sub RSEGS MV7 X (sp - X)); [exact WS7| clear; lia| clear - HX1; lia]).
assert (S16v : L5.u64_at RSEGS MV7 (X + 16) F).
{ apply (proj2 (L5A.u64_at_vis H7 M7 (X + 16) F (L5A.avis_sub H7 X (sp - X) (X + 16) 8 VS7 ltac:(clear; lia) ltac:(clear - HX1; lia)) ltac:(clear - Q0e; lia) ltac:(clear - QX; lia))). exact S16. }
pose proof OWN7 as (Y8 & Y16 & Y24 & Y32 & Y40 & Y48 & Y56 & Y64 & Y72 & Y80 & Y88 & Y96 & Y104).
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
pose proof (bv_unsigned_in_range 64 (getr R (reg 27))) as B27.
change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27.
assert (QsF : (sp - 104) + 104 <= F \/ F + 128 <= (sp - 104)) by (clear - GFCEIL SL176; lia).
assert (QsFL : (sp - 104) + 104 <= fl \/ fl + 1 <= (sp - 104)) by (clear - GFLR SL176; lia).
assert (QsSF : (sp - 104) + 104 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= (sp - 104)).
{ right. pose proof GFR as (GF1 & GF2 & _). assert (D2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - GF2; lia). clear - D2 SL176 SPT; lia. }
assert (Qd : 0 <= d < 2 ^ 64) by (clear - Hd Hk; lia).
cfeed P (PMBSRP3.bsrR_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => os | 41%nat => d | 47%nat => F | 48%nat => fl | 50%nat => X
| 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
| 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
| 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
| 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26))
| 76%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PMBSRP3.aligned; assumption | clear - SL176 SHI SPT; lia]).
destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & E1 & E2 & E8 & E9 & E10 & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _).
assert (R8ra : getr R8 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra).
pose proof (PMK.ret_to RSEGS fx8 R8 M8v 0xb0c10 (ltac:(oW' 0xb0c10%Z)) r (ltac:(oF' 0xb0c10%Z)) eq_refl (ltac:(oD' 0xb0c10%Z)) R8ra Hr1 Hr2) as MSr.
apply (PMBUK.retire_core L ar C HI LYa HIok M model LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr [] G
WA [] M7 model7 LK7 cr Aw7 fx7 fx8 R7 0xb0b3c R8 r M8v K BI7 (msteps_trans _ _ _ _ MS8 MSr) MG8).
{ intros a Ha Nw. unfold PMBUK.Wret in Nw. change (ff_bytes 1) with 128 in Nw. change (128 / 8) with 16 in Nw.
apply FRZ8; [exact Ha| intros Y; apply Nw; left; left; clear - Y; lia| intros Y; apply Nw; left; right; unfold SB; clear - Y; lia| intros Y; apply Nw; right; clear - Y; lia]. }
{ exact FL0. }
intros Mf modelf FZf AHf MRTf AMf HHf.
pose proof BI7 as (HH7 & _ & _ & INCA7 & INCL7 & _ & EK7 & DK7 & _).
assert (EKf : L5SAR.ek L ar LB FF 0 0 [] M7 Mf).
{ apply (PMBUAR.wret_ek L ar C HI LY HIok LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr []
LB LK7 cr Aw7 M7 Mf _ [] (fun _ => False) G HH7 (fun a Y => match Y with end)).
intros a Ha N. apply FZf; [exact Ha| intros Y; apply N; left; exact Y]. }
pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH7) as BRB7.
assert (PA7 : PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M7 op ois (PMSPA.with_src s0 (PM.SRC qc de' rem'))) by (apply PARS; assumption).
apply (KONT fx8 R8 Mf modelf LK7 Aw7 (PM.SRC qc de' rem') (PM.STRM g' eg st')).
- apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
repeat (destruct Hj as [<-|Hj]; [first [ rewrite E2; exact (eq_sym Rsp) | rewrite E8; apply Z_to_bv_bv_unsigned | rewrite E9; apply Z_to_bv_bv_unsigned
| rewrite E18; apply Z_to_bv_bv_unsigned | rewrite E19; apply Z_to_bv_bv_unsigned | rewrite E20; apply Z_to_bv_bv_unsigned
| rewrite E21; apply Z_to_bv_bv_unsigned | rewrite E22; apply Z_to_bv_bv_unsigned | rewrite E23; apply Z_to_bv_bv_unsigned
| rewrite E24; apply Z_to_bv_bv_unsigned | rewrite E25; apply Z_to_bv_bv_unsigned | rewrite E26; apply Z_to_bv_bv_unsigned
| rewrite E27; apply Z_to_bv_bv_unsigned
| rewrite (KS8 _) by inl; first [exact G73 | exact G74] ] |]).
destruct Hj.
- apply (PMKB.parser_keepA RSEGS PMB.AD L ar LB FF 0 0 [] M7 Mf EKf PMKB.wapp_nil FRB BRB7 _ _ _ AOP); [exact BOWN| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA7].
- apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF 0 0 [] M7 Mf EKf PMKB.wapp_nil FRB BRB7 ois str _ AOI); [exact SOWN| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA7].
- unfold PMSPA.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|].
split; [clear - Hg; lia|]. split; [exact Hst2| clear - Hcons Hd; lia].
- unfold PMSPA.read_res, PMSPA.consumed, PM.unread. cbn [PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. exists p, k, d.
rewrite L5SAR.r11, L5SAR.r12, L5K.rl10. split; [exact A11|]. split; [exact A12|]. split; [clear - DP0 DP1 Hk; lia|]. split; [unfold PM.CHUNK; clear - Hk; lia|].
split; [exact E10|]. split; [exact Hd|]. split; [exact Hcons|].
split; [|split; [exact HR1| exact HR0]].
intros i Hi. rewrite FZf; [exact (DD7 i Hi)| clear - Hi QP0 DP1 Hd; lia|].
unfold PMBUK.Wret. change (ff_bytes 1) with 128. change (128 / 8) with 16. unfold SB.
intros [[Y|Y]|Y]; clear - Y Hi Hd ApF ApSF ApFL; lia.
- exact AHf.
- exact MRTf.
- exact INCL7.
- exact INCA7.
- exact AMf.
- exact HHf. }
assert (APT : forall q m, In (q, m) LB -> q + m <= os \/ os + 296 <= q).
{ intros q m Hq. exact (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m os 296 HH Hq AO). }
assert (WSW : PMKB.wapp [(os + 256, 40)]).
{ apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct OBIG as [Y|Y]; [right; clear - Y; lia| left; clear - Y; lia]| apply PMKB.wapp_nil]. }
assert (OUTIS : forall i, ois <= i < ois + 272 -> L5.outside [(os + 256, 40)] i).
{ intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Hi Eos Eois. lia. }
assert (OUTBLK : forall c0 n0 p0, str = PM.VLong c0 n0 p0 -> forall i, p0 <= i < p0 + c0 -> L5.outside [(os + 256, 40)] i).
{ intros c0 n0 p0 E i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. assert (TIN : In (p0, c0) LB) by (apply SOWN; rewrite E; left; reflexivity).
destruct (APT p0 c0 TIN) as [Y|Y]; clear - Y Hi; lia. }
assert (EKWA : forall Ma Mb, L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] Ma Mb -> L5SAR.ek L ar LB FF sp 20480 WA Ma Mb).
{ intros Ma Mb E. apply (L5SAR.ek_W L ar LB FF sp 20480 WA [(os + 256, 40)] Ma Mb E). intros a O r0 [<-|[]] Y. apply (O (os + 256, 40)); [unfold WA, PMSPA.W_src, PMSPA.W_srcf; cbn [PM.sr_qc app]; left; reflexivity| exact Y]. }
pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
assert (DF2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - GF2; lia).
set (W3 := fun a => (X <= a < X + 56) \/ (F <= a < F + 24) \/ (F + 32 <= a < F + 40) \/ ((F / 8) + 2147450880 <= a < (F / 8) + 2147450880 + 16) \/ (os + 256 <= a < os + 296)).
assert (W3ok : forall a, 0 <= a < 2 ^ 64 -> W3 a -> aclientw L ar LB FF' 0 0 a /\ ~ (0x10000 <= a < 0x693000)).
{ intros a Ha Wa. split.
- destruct Wa as [Y|[Y|[Y|[Y|Y]]]].
+ unfold aclientw, aclient_g. right; left. split; [clear - Y SL176 SHI SPT HX1; lia| intros Z1; clear - Z1; lia].
+ apply (L5SAR.fframe_client L ar LB FF' 0 0 F 1 (X + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - Y; lia].
+ apply (L5SAR.fframe_client L ar LB FF' 0 0 F 1 (X + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - Y; lia].
+ apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 1 (X + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Y; lia.
+ unfold aclientw, aclient_g. do 3 right; left. destruct AO as (f & Hf & Y1 & Y2). exists f. split; [right; exact Hf|]. clear - Y Y1 Y2; lia.
- destruct Wa as [Y|[Y|[Y|[Y|Y]]]]; clear - Y GFR DF1 SL176 SPT HX1 O1; lia. }
assert (EKW3 : forall Ma Mb, (forall a, 0 <= a < 2 ^ 64 -> ~ W3 a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] Ma Mb).
{ intros Ma Mb FZ. apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] Ma Mb W3 FZ). intros a Ha Hc Ho Wa.
destruct Wa as [Y|[Y|[Y|[Y|Y]]]].
- apply (NCS0 a); [clear - Y HX1; lia| exact Hc].
- apply (GNCF a); [left; change (ff_bytes 1) with 128; clear - Y; lia| exact Hc].
- apply (GNCF a); [left; change (ff_bytes 1) with 128; clear - Y; lia| exact Hc].
- apply (GNCF a); [right; change (ff_bytes 1) with 128; unfold S; rewrite (proj1 (proj2 GF8)); unfold SB; clear - Y; lia| exact Hc].
- apply (Ho (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
assert (BRUN : forall (fx3 : FPState) R3 M3v (pc3 de' rem' : Z),
msteps RSEGS (L5A.st fx1 R2 0xb06d4 MV2) (L5A.st fx3 R3 pc3 M3v) -> mem_grows MV2 M3v ->
(forall i, 0 <= i < 2 ^ 64 -> ~ W3 i -> M3v (Z_to_bv 64 i) = MV2 (Z_to_bv 64 i)) ->
L5.u64_at RSEGS M3v (os + 264) qc -> L5.u64_at RSEGS M3v (os + 272) 16384 -> L5.u64_at RSEGS M3v (os + 280) de' -> L5.u64_at RSEGS M3v (os + 288) rem' ->
qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
(forall M3 model3, PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M3 model3 LK2 cr Aw ->
mrestrict H2 M3 = M3v -> mem_grows M2 M3 -> (forall i, 0 <= i < 2 ^ 64 -> ~ W3 i -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i)) ->
PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M3 op ois (PMSPA.with_src s0 (PM.SRC qc de' rem')) ->
PM.iss_at RSEGS PMB.AD PMSPA.accA M3 ois str (PM.STRM g eg sst) -> PMSTA.base_okA RSEGS PMB.AD M3 ->
srealizes RSEGS SCFG (@L5A.cfg fx3 R3 pc3 M3 model3) K) ->
srealizes RSEGS SCFG (@L5A.cfg fx1 R2 0xb06d4 M2 model2) K).
{ intros fx3 R3 M3v pc3 de' rem' MS3 MG3 FRZ3 Y264 Y272 Y280 Y288 Hd1 Hd2 Hd3 KB.
apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xb06d4 R3 pc3 M3v W3 K HH2 AM2 MS3 MG3 FRZ3 W3ok).
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3) by exact (EKW3 M2 M3 FR3).
assert (EK03 : L5SAR.ek L ar LB FF sp 20480 WA M M3).
{ apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M M2 M3); [| apply EKWA; exact EK23].
apply (L5SAR.ek_W L ar LB FF sp 20480 _ [] M M2 EK02f). intros a _ r0 []. }
assert (DK03 : L5SAR.dk L ar LB FF sp 20480 M M3) by (apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK02f); apply L5SAR.dk_grows; exact MGM3).
assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
{ intros a v Ha Hb Y. rewrite <- VIS3 in Y. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply OAV2; clear - Ha Hb; lia) ltac:(clear - Ha O1; lia) ltac:(clear - Hb O1; lia))). exact Y. }
assert (BI3 : PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M3 model3 LK2 cr Aw).
{ unfold PMBUK.binv. split; [exact HH3|]. split; [exact AM3|].
split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3)|].
split; [exact EK03|]. split; [exact DK03|].
split.
{ apply (PMBSU.own13_agree sp R M1 M3 ltac:(clear - SL176 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold PMBSU.ocell13 in Ha.
rewrite FR3; [apply AGF; clear - Ha HX1; lia| clear - Ha SL176 SHI SPT; lia|].
intros [Y|[Y|[Y|[Y|Y]]]]; clear - Y Ha HX1 GFCEIL SL176 SPT OCE DF2; lia. }
change (ff_bytes 1 / 8) with 16. apply (L5.defined_grows M2 M3 _ _ MGM3).
apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 16 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
apply (KB M3 model3 BI3 VIS3 MGM3 FR3).
- apply PARS; [exact EK03| exact DK03| apply TO3; [clear; lia| clear; lia| assumption]..| assumption| assumption| assumption].
- apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 _ M2 M3 EK23 WSW FRB BRB ois str _ AOI); [exact SOWN| exact OUTIS| exact OUTBLK| exact IA2].
- apply (PMBSK.base_keep L ar C LY LB FF sp 20480 _ M2 M3 EK23); [| exact BASE2].
intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha O1. lia. }
assert (DCL' : forall a, p <= a < p + k -> in_block LB a \/ in_fframe FF' a).
{ intros a Ha. destruct (DCL a Ha) as [Y|(f & Hf & Y)]; [left; exact Y| right; exists f; split; [right; exact Hf| exact Y]]. }
assert (STKX : forall Mc, L5CA.astk ar Mc sp 20480 -> forall scr, 0 <= scr <= 20480 - 176 -> L5CA.astk ar Mc X scr).
{ intros Mc AS scr Hs. pose proof (L5SAR.astk_sub ar Mc Mc sp 20480 (sp - X) scr AS (fun _ Y => Y)) as AS'.
replace (sp - (sp - X)) with X in AS' by (clear; lia). apply AS'; [clear - HX1; lia| clear - Hs; lia| clear - HX1 Hs; lia| exact HX16]. }
assert (MEMCALL : forall (fx3 : FPState) R3 M3 model3 LK3 Aw3 (ra dst src n : Z),
PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M3 model3 LK3 cr Aw3 ->
getr R3 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R3 (reg 2) = Z_to_bv 64 X -> getr R3 (reg 4) = getr R (reg 4) ->
getr R3 (reg 10) = Z_to_bv 64 dst -> getr R3 (reg 11) = Z_to_bv 64 src -> getr R3 (reg 12) = Z_to_bv 64 n ->
p <= dst -> dst + n <= p + k -> 0 <= n -> qc <= src -> src + n <= qc + 16384 ->
(forall (fx4 : FPState) R4 M4 model4, regs_preserved R3 R4 -> L5.defined M4 dst n ->
PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M4 model4 LK3 cr Aw3 ->
L5CA.ahpres L ar ([] ++ LB) FF' X 2560 [(dst, n)] M3 M4 ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx4 R4 ra M4 model4) K) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx3 R3 0x7760c M3 model3) K).
{ intros fx3 R3 M3 model3 LK3 Aw3 ra dst src n BI3 Ga1 RA Ga2 Ga4 Ga10 Ga11 Ga12 Hd1 Hd2 Hn Hs1 Hs2 KM.
pose proof BI3 as (HH3 & AM3 & MRT3 & INCA3 & INCL3 & ASTK3 & EK3 & DK3 & OWN3 & SHD3).
apply (PMBSRK.memcpy_call L ar C HI LY HIok fx3 R3 M3 model3 K ([] ++ LB) FF' LK3 cr Aw3 X ra dst src n HH3 AM3 K0 Ga1 RA Ga2).
{ rewrite Ga4. exact Rtp. }
{ exact Ga10. } { exact Ga11. } { exact Ga12. }
{ clear - Hn Hd1 Hd2 Hk; lia. }
{ apply (STKX M3 ASTK3); clear; lia. }
{ intros a Ha. apply (PMFA.accA_agree M M3 p k (AGSHP M M3 WA EK3 WAPP) DAP a). clear - Ha Hd1 Hd2 Hn; lia. }
{ intros i Hi. apply PMBSR1.cl_of_bf. apply DCL'. clear - Hi Hd1 Hd2; lia. }
{ apply (L5.defined_sub M3 p k); [| clear - Hd1; lia| clear - Hd2 Hn; lia].
apply (PMBSK.defined_dk L ar LB FF sp 20480 M M3 p k DK3); [intros i Hi; apply CLP; exact Hi| clear - DP0; lia| clear - DP1; lia| exact DDP]. }
{ clear - DP0 Hd1; lia. }
{ clear - DP1 Hd2; lia. }
{ unfold app_rng in DAPP |- *. clear - DAPP Hd1 Hd2 Hn. Lia.lia. }
{ intros a Ha. apply (PMFA.accA_agree M M3 qc 16384); [apply (PMBSK.agsh_blk L ar LB FF sp 20480 _ M M3 qc 16384 EK3 WAPP QIN); clear - Q0 Q4 SLO SHI SPT; lia| exact ACH| clear - Ha Hs1 Hs2 Hn; lia]. }
{ clear - Q0 Hs1; lia. }
{ clear - Q4 SLO SHI SPT Hs2; lia. }
{ apply (L5SAR.app_rng_block L ar C HI HIok ([] ++ LB) FF' LK3 cr Aw3 M3 _ qc 16384 src n HH3 QIN); clear - Hs1 Hs2 Hn; lia. }
{ intros i Hi. apply PMBSR1.cl_of_bf. left. exact (PMBSR1.in_block_of LB qc 16384 (src + i) QIN ltac:(clear - Hi Hs1 Hs2; lia)). }
{ apply (L5.defined_sub M3 qc 16384); [| clear - Hs1; lia| clear - Hs2 Hn; lia].
apply (PMBSK.defined_dk L ar LB FF sp 20480 M M3 qc 16384 DK3); [intros i Hi; apply CLQ; exact Hi| clear - Q0; lia| clear - Q4 SLO SHI SPT; lia| exact DCH]. }
{ clear - DQA Hd1 Hd2 Hs1 Hs2 Hn. Lia.lia. }
intros fx4 R4 M4 model4 RP4 DEF4 HP4 MRT4 AM4 HH4.
apply (KM fx4 R4 M4 model4 RP4 DEF4); [| exact HP4].
apply (PMBUK.binv_callee L ar C HI HIok M model LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr [] G
WA WA [] [] [] M3 model3 LK3 cr Aw3 M4 model4 LK3 cr Aw3 2560 [(dst, n)] BI3 HP4 HH4 AM4 MRT4 (incl_refl _) (incl_refl _)); [clear; lia| clear - HX1; lia| | | intros a Y; exact Y].
- intros rr a Hin Hr. destruct Hin as [<-|[]]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold PMBSU.ocell13. change (ff_bytes 1 / 8) with 16. split.
+ intros Y. destruct (DX a ltac:(clear - Hr Hd1 Hd2; lia)) as (X1 & _). apply X1. clear - Y; lia.
+ intros Y. unfold SB in Y. clear - Y Hr Hd1 Hd2 ApSF; lia.
- intros a _ O r0 [<-|[]] Y. apply (O (p, k)); [unfold WA; apply in_or_app; right; left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; clear - Y Hd1 Hd2; lia]. }
pose proof (PMBSK.iss_size_ltA M ois str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ.
assert (OUTWS : forall a, (X <= a < sp \/ F <= a < F + 128 \/ F / 8 + SB <= a < F / 8 + SB + 16) -> L5.outside (PMSPA.W_src PMB.AD fb (PM.SRC qc qc 0)) a).
{ intros a Ha r0 Hr. unfold PMSPA.W_src, PMSPA.W_srcf in Hr. cbn [app PM.p_src PM.sr_qc] in Hr. fold os ois in Hr. unfold L5.in_rng, SB in *.
pose proof (proj2 (APART qc 16384 0 0 ltac:(intros i Hi; left; exists (qc, 16384); split; [exact QIN| cbn [fst snd]; clear - Hi; lia]) ltac:(clear; lia))) as (AqSF & _).
pose proof (proj1 (APART qc 16384 0 0 ltac:(intros i Hi; left; exists (qc, 16384); split; [exact QIN| cbn [fst snd]; clear - Hi; lia]) ltac:(clear; lia))) as AqF.
destruct (APART ois 272 0 0 ltac:(intros i Hi; destruct AOI as (f & Hf & Z1 & Z2); unfold aclient, aclient_g; do 3 right; left; exists f; split; [exact Hf| clear - Z1 Z2 Hi; lia]) ltac:(clear; lia)) as (AiF & AiSF & _).
unfold SB in AqSF, AiSF.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PM.CHUNK.
- destruct OBIG as [Y|Y]; clear - Ha Y OCE SL176 SPT DF1 DF2 QoF HX1; lia.
- destruct IBIG as [Y|Y]; clear - Ha Y ICE SL176 SPT DF1 DF2 AiF AiSF HX1; lia.
- destruct IBIG as [Y|Y]; clear - Ha Y ICE SL176 SPT DF1 DF2 AiF AiSF HX1; lia.
- destruct QAs as [Y|Y]; clear - Ha Y Q4 SL176 SPT DF1 DF2 AqF AqSF HX1; lia. }
assert (FILLCALL : forall (fx3 : FPState) R3 M3 model3 LK3 Aw3,
PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M3 model3 LK3 cr Aw3 ->
getr R3 (reg 1) = Z_to_bv 64 723116 -> getr R3 (reg 2) = Z_to_bv 64 X -> getr R3 (reg 3) = getr R (reg 3) -> getr R3 (reg 4) = getr R (reg 4) ->
getr R3 (reg 10) = Z_to_bv 64 os -> getr R3 (reg 11) = Z_to_bv 64 qc -> getr R3 (reg 12) = Z_to_bv 64 16384 ->
PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M3 op ois (PMSPA.with_src s0 (PM.SRC qc qc 0)) ->
PM.iss_at RSEGS PMB.AD PMSPA.accA M3 ois str (PM.STRM g eg sst) -> PMSTA.base_okA RSEGS PMB.AD M3 ->
(forall (fx4 : FPState) R4 M4 model4 LK4 Aw4 (c g4 st4 : Z), regs_preserved R3 R4 -> getr R4 (reg 10) = Z_to_bv 64 c ->
0 <= c <= 16384 -> g4 = g + c -> g4 <= eg -> (sst = 2 -> st4 = 2) -> (c = 0 -> st4 = 2) ->
PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M4 model4 LK4 cr Aw4 ->
L5CA.ahpres L ar ([] ++ LB) FF' X 18432 (PMSPA.W_src PMB.AD fb (PM.SRC qc qc 0)) M3 M4 ->
PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M4 op ois (PMSPA.with_src s0 (PM.SRC qc qc 0)) ->
PM.iss_at RSEGS PMB.AD PMSPA.accA M4 ois str (PM.STRM g4 eg st4) -> PMSTA.base_okA RSEGS PMB.AD M4 ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx4 R4 723116 M4 model4) K) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx3 R3 0xb0e58 M3 model3) K).
{ intros fx3 R3 M3 model3 LK3 Aw3 BI3 Ga1 Ga2 Ga3 Ga4 Ga10 Ga11 Ga12 PA3 IA3 BASE3 KF.
pose proof BI3 as (HH3 & AM3 & MRT3 & INCA3 & INCL3 & ASTK3 & EK3 & DK3 & OWN3 & SHD3).
assert (STK3 : shadow_zero M3 (X - 18432) (18432 / 8)).
{ change (18432 / 8) with 2304.
assert (M8a : (sp - 20480) mod 8 = 0) by (apply PMKB.mod16_8'; replace (sp - 20480) with (sp + (-1280) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
assert (M8b : (X - 18432) mod 8 = 0) by (apply PMKB.mod16_8'; replace (X - 18432) with (X + (-1152) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact HX16).
apply (PMKB.stksh_keepA L ar LB FF sp 20480 WA M M3 EK3 WAPP (X - 18432) 2304); [clear - HX1 SL176 SPT; lia| clear - HX1 SLO; lia| clear - HX1 SHI SPT; lia| exact M8b| clear; lia|].
apply (PMKB.shadow_zero_sub M (sp - 20480) 2560); [exact M8a| exact M8b| clear - HX1; lia| clear - HX1; lia| clear; lia| exact STKSH]. }
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF3 & _).
unfold PMB.fill_buffer_spec, PMSPA.fill_buffer_spec, PMSPA.src_spec in FB.
apply (FB fx3 R3 M3 model3 K LBX FF' LK3 Aw3 cr X 723116 fb (PMSPA.with_src s0 (PM.SRC qc qc 0)) str (PM.STRM g eg sst) [] HH3 AM3 K0).
{ split; [rewrite L5K.rl1; exact Ga1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; exact Ga2|].
split; [rewrite L5K.rl3; rewrite Ga3; exact Rgp|]. split; [rewrite L5K.rl4; rewrite Ga4; exact Rtp|].
change (PMSPA.pm_scr 3) with 18432. split; [|exact STK3]. apply (STKX M3 ASTK3); clear; lia. }
{ apply (PMBUAR.ffroomA_push 4 3 FF LK LK3 _ FRM INCL3); [exact NDF3| clear; lia]. }
{ apply (PMBUAR.ffrsA_push FF sp X F 1 (X + 32) FRS); clear - HX1; lia. }
{ exact FOK'. }
{ unfold PMSPA.o_src. fold os. rewrite L5K.rl10. exact Ga10. }
{ split; [rewrite L5SAR.r11; exact Ga11| rewrite L5SAR.r12; exact Ga12]. }
{ reflexivity. }
{ exact PA3. }
{ exact IA3. }
{ exact BASE3. }
{ exact INCS. }
intros fx4 R4 M4 model4 LK4 Aw4 src4 sm4 RP4 PA4 IA4 STEP4 RES4 HP4 MRT4 INCLK4 INCAw4 AM4 HH4.
change (PMSPA.pm_scr 3) with 18432 in HP4. rewrite app_nil_r in HP4.
destruct RES4 as (E4 & c & A10c & Hc & G4c & RS0 & RS2). subst src4. unfold PM.CHUNK in Hc. rewrite L5K.rl10 in A10c.
destruct sm4 as [g4 eg4 st4]. cbn [PM.sm_g PM.sm_eg PM.sm_st] in *.
pose proof STEP4 as (_ & EG4 & _ & _ & _). cbn [PM.sm_eg] in EG4. subst eg4.
assert (BI4 : PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M4 model4 LK4 cr Aw4).
{ apply (PMBUK.binv_callee L ar C HI HIok M model LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr [] G
WA WA [] [] [] M3 model3 LK3 cr Aw3 M4 model4 LK4 cr Aw4 18432 (PMSPA.W_src PMB.AD fb (PM.SRC qc qc 0)) BI3 HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
[clear; lia| clear - HX1; lia| | | intros a Y; exact Y].
- intros rr a Hin Hr. split.
+ intros Y. exact (OUTWS a ltac:(unfold PMBSU.ocell13 in Y; clear - Y HX1; lia) rr Hin Hr).
+ intros Y. exact (OUTWS a ltac:(change (ff_bytes 1 / 8) with 16 in Y; clear - Y; lia) rr Hin Hr).
- intros a _ O r0 Hr Y. apply (O r0); [unfold WA; apply in_or_app; left; exact Hr| exact Y]. }
pose proof (L5SAR.ek_callee L ar LB [] FF' [] X 18432 X 18432 _ _ M3 M4 HP4 ltac:(clear; lia) ltac:(clear; lia) (fun a _ Y => Y)) as EK34.
pose proof (PMBSK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ qc 16384 HH QIN) as QIMG.
assert (BASE4 : PMSTA.base_okA RSEGS PMB.AD M4).
{ apply (PMBSK.base_keep L ar C LY LB FF' X 18432 _ M3 M4 EK34); [| exact BASE3].
intros a Ha r0 Hr. unfold PMSPA.W_src, PMSPA.W_srcf in Hr. cbn [app PM.p_src PMSPA.with_src s0 PM.sr_qc] in Hr. fold os ois in Hr. unfold L5.in_rng.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PM.CHUNK; destruct QIMG as [Y|Y]; clear - Ha O1 I1 Y; lia. }
apply (KF fx4 R4 M4 model4 LK4 Aw4 c g4 st4 RP4 A10c Hc G4c).
- destruct IST as [ST0|ST2]; [destruct (RS0 ST0) as (CE & _); unfold PM.CHUNK in CE; rewrite G4c, CE; clear - SZ; destruct (Z.min_spec 16384 (eg - g)) as [[X1 X2]|[X1 X2]]; rewrite X2; lia
| destruct (RS2 ST2) as (CE & _); rewrite G4c, CE; clear - SZ; lia].
- intros Y. exact (proj2 (RS2 Y)).
- intros CZ. destruct IST as [ST0|ST2]; [destruct (RS0 ST0) as (_ & SE); rewrite SE, CZ; reflexivity| exact (proj2 (RS2 ST2))].
- exact BI4.
- exact HP4.
- exact PA4.
- exact IA4.
- exact BASE4. }
assert (STATEV : forall Mc modelc LKc Awc (de' rem' k32 : Z),
PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] Mc modelc LKc cr Awc ->
PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA Mc op ois (PMSPA.with_src s0 (PM.SRC qc de' rem')) -> PMSTA.base_okA RSEGS PMB.AD Mc ->
L5.u64_at RSEGS Mc (X + 8) (F + 32) -> L5.u64_at RSEGS Mc (X + 16) F -> L5.u64_at RSEGS Mc (X + 24) p -> L5.u64_at RSEGS Mc (X + 48) F ->
L5.u64_at RSEGS Mc (F + 32) k32 -> L5.u8_at RSEGS Mc ((F / 8) + 2147450884) 0 -> L5.u8_at RSEGS Mc ((F / 8) + 2147450888) 248 ->
(L5.img_clear (mrestrict (ahid Awc modelc) Mc) 65536 1269760 /\ L5.u64_at RSEGS (mrestrict (ahid Awc modelc) Mc) 1296952 2147450880
/\ L5.u32_at RSEGS (mrestrict (ahid Awc modelc) Mc) 1296960 1)
/\ (L5.writable RSEGS (mrestrict (ahid Awc modelc) Mc) X 56 /\ L5.u64_at RSEGS (mrestrict (ahid Awc modelc) Mc) (X + 24) p
/\ L5.u64_at RSEGS (mrestrict (ahid Awc modelc) Mc) (X + 8) (F + 32) /\ L5.u64_at RSEGS (mrestrict (ahid Awc modelc) Mc) (X + 16) F
/\ L5.u64_at RSEGS (mrestrict (ahid Awc modelc) Mc) (X + 48) F)
/\ (L5KA.zeros_at (mrestrict (ahid Awc modelc) Mc) (((os + 8) / 8) + 2147450880) 36 /\ L5.writable RSEGS (mrestrict (ahid Awc modelc) Mc) os 296
/\ L5.u64_at RSEGS (mrestrict (ahid Awc modelc) Mc) (os + 264) qc /\ L5.u64_at RSEGS (mrestrict (ahid Awc modelc) Mc) (os + 272) 16384
/\ L5.defined (mrestrict (ahid Awc modelc) Mc) (os + 256) 8 /\ L5.u64_at RSEGS (mrestrict (ahid Awc modelc) Mc) (os + 280) de'
/\ L5.u64_at RSEGS (mrestrict (ahid Awc modelc) Mc) (os + 288) rem' /\ (forall a n, os <= a -> a + n <= os + 296 -> L5A.avis (ahid Awc modelc) a n))
/\ (L5.defined (mrestrict (ahid Awc modelc) Mc) F 128 /\ L5.writable RSEGS (mrestrict (ahid Awc modelc) Mc) F 128
/\ L5.writable RSEGS (mrestrict (ahid Awc modelc) Mc) ((F / 8) + 2147450880) 16 /\ L5.u64_at RSEGS (mrestrict (ahid Awc modelc) Mc) (F + 120) fl
/\ L5.writable RSEGS (mrestrict (ahid Awc modelc) Mc) fl 1 /\ L5.u64_at RSEGS (mrestrict (ahid Awc modelc) Mc) (F + 32) k32
/\ L5.u8_at RSEGS (mrestrict (ahid Awc modelc) Mc) ((F / 8) + 2147450884) 0 /\ L5.u8_at RSEGS (mrestrict (ahid Awc modelc) Mc) ((F / 8) + 2147450888) 248)).
{ intros Mc modelc LKc Awc de' rem' k32 BIc PAc BASEc Y8 Y16 Y24 Y48 Y32 Z4 Z8.
set (Hc := ahid Awc modelc). set (MVc := mrestrict Hc Mc).
destruct (PMBUK.vis_facts L ar C HI LYa HIok M model LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr [] G
WA [] Mc modelc LKc cr Awc BIc) as ((WSc & _ & _ & _ & _) & _ & (FDc & FWc & FSWc & FLCc & FLWc) & (_ & _ & VFc & VSc & VSHc)).
change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. fold Hc MVc in WSc, FDc, FWc, FSWc, FLCc, FLWc.
replace (F + 128 - 8) with (F + 120) in FLCc by (clear; lia).
pose proof BIc as (HHc & _ & _ & _ & _ & ASTKc & _).
pose proof (PMBSK.src_vis L ar C HI LY HIok LB FF' LKc cr Awc Mc modelc fb ois _ sp 20480 HHc FOK' PAc ASTKc) as ((_ & _ & _) & OZc & OWc & _ & OAVc & _ & _ & _).
fold os MVc in OZc, OWc, OAVc.
pose proof (PMBSK.mach_vis L ar C HI LY HIok _ _ LKc cr Awc Mc modelc HHc BASEc) as (Wc0 & Wc1 & Wc2). fold MVc in Wc0, Wc1, Wc2.
pose proof PAc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PSRCc & _).
destruct PSRCc as (_ & _ & SDc & S264c & S272c & S280c & S288c & _). cbn [PM.p_src PMSPA.with_src s0 PM.sr_qc PM.sr_de PM.sr_rem] in SDc, S264c, S272c, S280c, S288c.
fold os in SDc, S264c, S272c, S280c, S288c. unfold PM.CHUNK in S272c.
assert (WVX : forall a v, X <= a -> a + 8 <= X + 56 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MVc a v).
{ intros a v Ha Hb Y. apply (proj2 (L5A.u64_at_vis Hc Mc a v (L5A.avis_sub Hc X (sp - X) a 8 VSc ltac:(clear - Ha; lia) ltac:(clear - Hb HX1; lia)) ltac:(clear - Ha Q0e; lia) ltac:(clear - Hb QX; lia))). exact Y. }
assert (WVF : forall a v, F <= a -> a + 8 <= F + 128 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MVc a v).
{ intros a v Ha Hb Y. apply (proj2 (L5A.u64_at_vis Hc Mc a v (L5A.avis_sub Hc F 128 a 8 VFc ltac:(clear - Ha; lia) ltac:(clear - Hb; lia)) ltac:(clear - Ha Q0c; lia) ltac:(clear - Hb QFR; lia))). exact Y. }
assert (WVS : forall a v, F / 8 + 2147450880 <= a -> a + 1 <= F / 8 + 2147450880 + 16 -> L5.u8_at RSEGS Mc a v -> L5.u8_at RSEGS MVc a v).
{ intros a v Ha Hb Y. apply (proj2 (L5A.u8_at_vis Hc Mc a v (L5A.avis_sub Hc (F / 8 + SB) 16 a 1 VSHc ltac:(unfold SB; clear - Ha; lia) ltac:(unfold SB; clear - Hb; lia)) ltac:(clear - Ha DF1; lia) ltac:(clear - Hb DF2; lia))). exact Y. }
assert (WVO : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MVc a v).
{ intros a v Ha Hb Y. apply (proj2 (L5A.u64_at_vis _ Mc a v ltac:(apply OAVc; clear - Ha Hb; lia) ltac:(clear - Ha O1; lia) ltac:(clear - Hb O1; lia))). exact Y. }
split; [split; [exact Wc0| split; [exact Wc1| exact Wc2]]|].
split.
{ split; [apply (L5.writable_sub RSEGS MVc X (sp - X)); [exact WSc| clear; lia| clear - HX1; lia]|].
split; [apply WVX; [clear; lia| clear; lia| exact Y24]|]. split; [apply WVX; [clear; lia| clear; lia| exact Y8]|].
split; [apply WVX; [clear; lia| clear; lia| exact Y16]| apply WVX; [clear; lia| clear; lia| exact Y48]]. }
split.
{ split; [exact OZc|]. split; [exact OWc|].
split; [apply WVO; [clear; lia| clear; lia| exact S264c]|]. split; [apply WVO; [clear; lia| clear; lia| exact S272c]|].
split; [apply (proj2 (L5A.defined_vis _ Mc (os + 256) 8 ltac:(apply OAVc; clear; lia))); exact SDc|].
split; [apply WVO; [clear; lia| clear; lia| exact S280c]|]. split; [apply WVO; [clear; lia| clear; lia| exact S288c]| exact OAVc]. }
split; [exact FDc|]. split; [exact FWc|]. split; [exact FSWc|]. split; [exact FLCc|]. split; [exact FLWc|].
split; [apply WVF; [clear; lia| clear; lia| exact Y32]|].
split; [apply WVS; [clear; lia| clear; lia| exact Z4]| apply WVS; [clear; lia| clear; lia| exact Z8]]. }
assert (CKEEP : forall Mc Mc' scr W, L5CA.ahpres L ar ([] ++ LB) FF' X scr W Mc Mc' -> 0 <= scr ->
(forall a, (X <= a < X + 56 \/ (F + 32 <= a < F + 120) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16)) -> L5.outside W a) ->
(forall a v, (X <= a /\ a + 8 <= X + 56 \/ F + 32 <= a /\ a + 8 <= F + 120) -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS Mc' a v)
/\ (forall a v, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16 -> L5.u8_at RSEGS Mc a v -> L5.u8_at RSEGS Mc' a v)).
{ intros Mc Mc' scr W HP Hs OUT.
assert (KP : forall a, (X <= a < X + 56 \/ (F + 32 <= a < F + 120) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16)) -> Mc' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
{ intros a Ha. apply (proj1 HP). split; [clear - Ha QX QFR DF1 DF2; lia|]. split; [|exact (OUT a Ha)].
destruct Ha as [Y|[Y|Y]].
- apply L5SAR.stack_client; [clear - Y SL176 SHI SPT HX1; lia| clear - Y; lia].
- apply (L5SAR.fframe_client L ar LB FF' X scr F 1 (X + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - Y; lia].
- apply (L5SAR.fframe_shadow_client L ar LB FF' X scr F 1 (X + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Y; lia. }
split.
- intros a v Ha Y. apply (L5C.u64_at_agree RSEGS Mc Mc'); [intros i Hi; apply KP; clear - Ha Hi; lia| clear - Ha Q0e Q0c; lia| clear - Ha QX QFR; lia| exact Y].
- intros a v Ha Y. apply (L5C.u8_at_agree RSEGS Mc Mc'); [intros i Hi; apply KP; clear - Ha Hi; lia| clear - Ha DF1; lia| clear - Ha DF2; lia| exact Y]. }
set (W5 := fun a => (F + 64 <= a < F + 72) \/ ((F / 8) + 2147450880 + 8 <= a < (F / 8) + 2147450880 + 9) \/ (os + 256 <= a < os + 296) \/ (ois + 152 <= a < ois + 156)).
assert (W5ok : forall a, 0 <= a < 2 ^ 64 -> W5 a -> aclientw L ar ([] ++ LB) FF' 0 0 a /\ ~ (0x10000 <= a < 0x693000)).
{ intros a Ha Wa. split.
- destruct Wa as [Y|[Y|[Y|Y]]].
+ apply (L5SAR.fframe_client L ar LB FF' 0 0 F 1 (X + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - Y; lia].
+ apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 1 (X + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Y; lia.
+ unfold aclientw, aclient_g. do 3 right; left. destruct AO as (f & Hf & Z1 & Z2). exists f. split; [right; exact Hf|]. clear - Y Z1 Z2; lia.
+ unfold aclientw, aclient_g. do 3 right; left. destruct AOI as (f & Hf & Z1 & Z2). exists f. split; [right; exact Hf|]. clear - Y Z1 Z2; lia.
- destruct Wa as [Y|[Y|[Y|Y]]]; clear - Y GFR DF1 O1 I1; lia. }
assert (CRUN : forall (fx4 : FPState) R4 M4 model4 LK4 Aw4 (fx5 : FPState) R5 M5v (pc4 pc5 : Z) (Wp : Z -> Prop),
PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M4 model4 LK4 cr Aw4 ->
(forall a, Wp a -> W5 a) ->
msteps RSEGS (L5A.st fx4 R4 pc4 (mrestrict (ahid Aw4 model4) M4)) (L5A.st fx5 R5 pc5 M5v) -> mem_grows (mrestrict (ahid Aw4 model4) M4) M5v ->
(forall i, 0 <= i < 2 ^ 64 -> ~ Wp i -> M5v (Z_to_bv 64 i) = mrestrict (ahid Aw4 model4) M4 (Z_to_bv 64 i)) ->
(forall M5 model5, PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M5 model5 LK4 cr Aw4 ->
mrestrict (ahid Aw4 model4) M5 = M5v -> mem_grows M4 M5 -> (forall i, 0 <= i < 2 ^ 64 -> ~ Wp i -> M5 (Z_to_bv 64 i) = M4 (Z_to_bv 64 i)) ->
srealizes RSEGS SCFG (@L5A.cfg fx5 R5 pc5 M5 model5) K) ->
srealizes RSEGS SCFG (@L5A.cfg fx4 R4 pc4 M4 model4) K).
{ intros fx4 R4 M4 model4 LK4 Aw4 fx5 R5 M5v pc4 pc5 Wp BI4 WPS MS5 MG5 FRZ5 KC.
pose proof BI4 as (HH4 & AM4 & _).
apply (L5SAR.apiece L ar C HI LYa HIok ([] ++ LB) FF' LK4 cr Aw4 M4 model4 fx4 fx5 R4 pc4 R5 pc5 M5v Wp K HH4 AM4 MS5 MG5 FRZ5).
{ intros a Ha Wa. exact (W5ok a Ha (WPS a Wa)). }
intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
apply (KC M5 model5); [| exact VIS5| exact MGM5| exact FR5].
apply (PMBUK.binv_pieceW L ar HI M model LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr [] G
WA [] M4 model4 LK4 cr Aw4 M5 model5 Wp BI4 HH5 AM5 MRT5 MGM5 FR5).
intros a Wa. change (ff_bytes 1) with 128. change (128 / 8) with 16. unfold PMBSU.ocell13, SB.
destruct (WPS a Wa) as [Y|[Y|[Y|Y]]].
- split; [clear - Y GFCEIL SL176; lia| right; left; clear - Y; lia].
- split; [clear - Y DF2 SL176 SPT; lia| right; right; left; clear - Y; lia].
- split; [clear - Y OCE SL176; lia| right; right; right]. intros Ho. apply (Ho (os + 256, 40)); [unfold WA, PMSPA.W_src, PMSPA.W_srcf; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia].
- split; [clear - Y ICE OCE SL176; lia| right; right; right]. intros Ho. apply (Ho (ois + 152, 4)); [unfold WA, PMSPA.W_src, PMSPA.W_srcf; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
assert (EKC : forall Ma Mb (Wl : list L5.range) (Wp : Z -> Prop), (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
(forall a, Wp a -> F <= a < F + 128 \/ F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16 \/ ~ L5.outside Wl a) -> L5SAR.ek L ar LB FF sp 20480 Wl Ma Mb).
{ intros Ma Mb Wl Wp FZ WPS. apply (L5SAR.ek_piece L ar LB FF sp 20480 Wl Ma Mb Wp FZ). intros a Ha Hc Ho Wa.
destruct (WPS a Wa) as [Y|[Y|Y]].
- apply (GNCF a); [left; change (ff_bytes 1) with 128; clear - Y; lia| exact Hc].
- apply (GNCF a); [right; change (ff_bytes 1) with 128; unfold S; rewrite (proj1 (proj2 GF8)); unfold SB; clear - Y; lia| exact Hc].
- exact (Y Ho). }
assert (TRANS : forall (Ma Mb : word -> option byte) (Wq : Z -> Prop), (forall i, 0 <= i < 2 ^ 64 -> ~ Wq i -> Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)) ->
(forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ Wq i) -> forall i, a <= i < a + n -> Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i))).
{ intros Ma Mb Wq FZ a n H0 H1 NW i Hi. apply FZ; [clear - H0 H1 Hi; lia| apply NW; exact Hi]. }
assert (DAV : forall a, p <= a < p + k -> ~ (X <= a < sp) /\ ~ (F <= a < F + 128) /\ ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16)
/\ ~ (os <= a < os + 296) /\ ~ (ois <= a < ois + 272)).
{ intros a Ha. destruct (DX a Ha) as (X1 & X2 & X3 & _). split; [clear - X1 HX1 SL176; lia|]. split; [clear - Ha ApF; lia|]. split; [clear - Ha ApSF; lia|].
split; [clear - X3 Eos Eop; lia| exact X2]. }
assert (OKEEP : forall Mc Mc' dst n, L5CA.ahpres L ar ([] ++ LB) FF' X 2560 [(dst, n)] Mc Mc' -> p <= dst -> dst + n <= p + k ->
forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS Mc' a v).
{ intros Mc Mc' dst n HP Hd1 Hd2 a v Ha Hb Y. apply (L5C.u64_at_agree RSEGS Mc Mc'); [| clear - Ha O1; lia| clear - Hb O1; lia| exact Y].
intros i Hi. apply (proj1 HP). split; [clear - Ha Hb Hi O1; lia|]. split.
- apply PMBSR1.cl_of_bf. right. destruct (PMBSR1.in_fframe_of_aobjA FF os 296 i AO ltac:(clear - Ha Hb Hi; lia)) as (f & Hf & Z1). exists f. split; [right; exact Hf| exact Z1].
- intros r0 [<-|[]] Y2. unfold L5.in_rng in Y2. cbn [fst snd] in Y2. destruct (DAV i ltac:(clear - Y2 Hd1 Hd2; lia)) as (_ & _ & _ & Z4 & _). apply Z4. clear - Ha Hb Hi; lia. }
assert (CKM : forall a, (X <= a < X + 56 \/ (F + 32 <= a < F + 120) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16)) ->
forall dst n, p <= dst -> dst + n <= p + k -> L5.outside [(dst, n)] a).
{ intros a Ha dst n Hd1 Hd2 r0 [<-|[]] Y. unfold L5.in_rng in Y. cbn [fst snd] in Y.
destruct (DAV a ltac:(clear - Y Hd1 Hd2; lia)) as (Z1 & Z2 & Z3 & _). destruct Ha as [Y1|[Y1|Y1]]; [apply Z1; clear - Y1 HX1; lia| apply Z2; clear - Y1; lia| apply Z3; exact Y1]. }
assert (CPART : forall (fx4 : FPState) R4 M4 model4 LK4 Aw4 (len1 c g4 st4 : Z),
PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M4 model4 LK4 cr Aw4 ->
getr R4 (reg 2) = Z_to_bv 64 X -> getr R4 (reg 8) = Z_to_bv 64 sp -> getr R4 (reg 9) = Z_to_bv 64 X -> getr R4 (reg 10) = Z_to_bv 64 c ->
getr R4 (reg 18) = Z_to_bv 64 (((os + 288) / 8) + 2147450880) -> getr R4 (reg 19) = Z_to_bv 64 os -> getr R4 (reg 20) = Z_to_bv 64 len1 ->
getr R4 (reg 21) = Z_to_bv 64 (((os + 280) / 8) + 2147450880) -> getr R4 (reg 22) = Z_to_bv 64 (os + 280) -> getr R4 (reg 23) = Z_to_bv 64 (os + 288) ->
getr R4 (reg 25) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R4 (reg 26) = Z_to_bv 64 F -> getr R4 (reg 27) = Z_to_bv 64 2147450880 ->
getr R4 (reg 3) = getr R (reg 3) -> getr R4 (reg 4) = getr R (reg 4) ->
L5.u64_at RSEGS M4 (X + 8) (F + 32) -> L5.u64_at RSEGS M4 (X + 16) F -> L5.u64_at RSEGS M4 (X + 24) p -> L5.u64_at RSEGS M4 (X + 48) F ->
L5.u64_at RSEGS M4 (F + 32) k -> L5.u8_at RSEGS M4 ((F / 8) + 2147450884) 0 -> L5.u8_at RSEGS M4 ((F / 8) + 2147450888) 248 ->
PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M4 op ois (PMSPA.with_src s0 (PM.SRC qc qc 0)) ->
PM.iss_at RSEGS PMB.AD PMSPA.accA M4 ois str (PM.STRM g4 eg st4) -> PMSTA.base_okA RSEGS PMB.AD M4 ->
len1 = rem -> len1 < k -> 0 <= c <= 16384 -> g4 = g + c -> g4 <= eg -> (sst = 2 -> st4 = 2) -> (c = 0 -> st4 = 2) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx4 R4 723116 M4 model4) K).
{ intros fx4 R4 M4 model4 LK4 Aw4 len1 c g4 st4 BI4 Y2 Y8 Y9 Y10 Y18 Y19 Y20 Y21 Y22 Y23 Y25 Y26 Y27 Y3 Y4 X8 X16 X24 X48 F32 SH4 SH8 PA4 IA4 BASE4 Hl1 Hl1k Hc Hg4 Hg4e Hst4 Hc0.
destruct (STATEV M4 model4 LK4 Aw4 qc 0 k BI4 PA4 BASE4 X8 X16 X24 X48 F32 SH4 SH8)
as ((U0 & U1 & U2) & (UX & UX24 & UX8 & UX16 & UX48) & (UOZ & UOW & U264 & U272 & UD256 & U280 & U288 & OAV4) & (UFD & UFW & UFSW & UFL & UFLW & UF32 & US4 & US8)).
set (MV4 := mrestrict (ahid Aw4 model4) M4) in *.
assert (UF32' : L5.u64_at RSEGS MV4 (F + 32) ((k - len1) + len1)) by (replace ((k - len1) + len1) with k by (clear; lia); exact UF32).
assert (Hl0 : 0 <= len1 <= 16383) by (clear - Hl1 G2 Hl1k Hk; lia).
assert (Hkl : 1 <= k - len1 <= 16384) by (clear - Hl0 Hl1k Hk; lia).
assert (TO5 : forall (M5 : word -> option byte) a v, os <= a -> a + 8 <= os + 296 ->
L5.u64_at RSEGS (mrestrict (ahid Aw4 model4) M5) a v -> L5.u64_at RSEGS M5 a v).
{ intros M5 a v Ha Hb Y. apply (proj1 (L5A.u64_at_vis _ M5 a v ltac:(apply OAV4; clear - Ha Hb; lia) ltac:(clear - Ha O1; lia) ltac:(clear - Hb O1; lia))). exact Y. }
assert (EKO : forall Ma Mb, (forall i, 0 <= i < 2 ^ 64 -> ~ (os + 256 <= i < os + 296) -> Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)) -> L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] Ma Mb).
{ intros Ma Mb FZ. apply (EKC Ma Mb [(os + 256, 40)] (fun a => os + 256 <= a < os + 296) FZ). intros a Y. right; right. intros Ho.
apply (Ho (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
unfold PMSPA.cfg.
destruct (Z.eq_dec c 0) as [CZ|CNZ].
-
subst c.
cfeed P (PMBSRP2.bsrF0_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 34%nat => qc | 36%nat => os | 37%nat => p | 39%nat => len1 | 40%nat => k - len1
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBSRP2.aligned; assumption | clear - Hl0 Hkl QPR Q0a Q0b Q0c Q0d Q0e Q0f; lia]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z11 & Z22 & Z288 & Z264 & Z272 & ZD256 & Z280).
apply (CRUN fx4 R4 M4 model4 LK4 Aw4 fx5 R5 M5v 723116 0xb0b3c (fun a => os + 256 <= a < os + 296) BI4); [intros a Y; right; right; left; exact Y| exact MS5| exact MG5| |].
{ intros i Hi N. apply FRZ5; [exact Hi| intros Y; apply N; clear - Y; lia]. }
intros M5 model5 BI5 VIS5 MGM5 FR5.
assert (TO5' : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M5v a v -> L5.u64_at RSEGS M5 a v).
{ intros a v Ha Hb Y. rewrite <- VIS5 in Y. exact (TO5 M5 a v Ha Hb Y). }
apply (EXITP fx5 R5 M5 model5 LK4 Aw4 qc 0 g4 st4 len1 BI5).
+ rewrite (KS5 2%nat) by inl. exact Y2.
+ rewrite (KS5 8%nat) by inl. exact Y8.
+ rewrite (KS5 9%nat) by inl. exact Y9.
+ exact Z22.
+ rewrite (KS5 25%nat) by inl. exact Y25.
+ rewrite (KS5 26%nat) by inl. exact Y26.
+ rewrite (KS5 3%nat) by inl. exact Y3.
+ rewrite (KS5 4%nat) by inl. exact Y4.
+ apply (L5C.u64_at_agree RSEGS M4 M5); [intros i Hi; apply FR5; [clear - Hi QX; lia| clear - Hi QXo; lia]| clear - Q0e; lia| clear - QX; lia| exact X16].
+ apply TO5'; [clear; lia| clear; lia| exact Z264].
+ apply TO5'; [clear; lia| clear; lia| exact Z272].
+ apply TO5'; [clear; lia| clear; lia| exact Z280].
+ apply TO5'; [clear; lia| clear; lia| exact Z288].
+ clear; lia.
+ clear; lia.
+ clear; lia.
+ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 _ M4 M5 (EKO M4 M5 FR5) WSW FRB BRB ois str _ AOI); [exact SOWN| exact OUTIS| exact OUTBLK| exact IA4].
+ clear - Hg4 Hg4e; lia.
+ exact Hst4.
+ clear - Hl0 Hl1k; lia.
+ clear - Hl1 Hg4; lia.
+ clear - Hl1; lia.
+ intros _. split; [reflexivity| apply Hc0; reflexivity].
-
set (len2 := Z.min c (k - len1)).
assert (L2R : 1 <= len2 <= k - len1 /\ len2 <= c /\ (len2 = k - len1 \/ len2 = c)).
{ unfold len2. clear - CNZ Hc Hkl. destruct (Z.min_spec c (k - len1)) as [[X1 X2]|[X1 X2]]; rewrite X2; lia. }
set (VC := fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 36%nat => os | 37%nat => p | 39%nat => len1 | 40%nat => k - len1
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end).
assert (HEADC : exists fx5 R5 M5v, msteps RSEGS (L5A.st fx4 R4 723116 MV4) (L5A.st fx5 R5 0x7760c M5v) /\ mem_grows MV4 M5v
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ ((F + 64 <= i < F + 72) \/ ((F / 8) + 2147450880 + 8 <= i < (F / 8) + 2147450880 + 9) \/ (os + 256 <= i < os + 296)) ->
M5v (Z_to_bv 64 i) = MV4 (Z_to_bv 64 i))
/\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat -> getr R5 (reg x) = getr R4 (reg x))
/\ getr R5 (reg 1) = Z_to_bv 64 723244 /\ getr R5 (reg 10) = Z_to_bv 64 (p + len1) /\ getr R5 (reg 11) = Z_to_bv 64 qc
/\ getr R5 (reg 12) = Z_to_bv 64 len2 /\ getr R5 (reg 24) = Z_to_bv 64 len2
/\ L5.u8_at RSEGS M5v ((F / 8) + 2147450888) 248
/\ L5.u64_at RSEGS M5v (os + 288) c /\ L5.u64_at RSEGS M5v (os + 280) qc /\ L5.u64_at RSEGS M5v (os + 264) qc
/\ L5.u64_at RSEGS M5v (os + 272) 16384).
{ destruct (Z_le_gt_dec c (k - len1)) as [CLE|CGT].
- assert (E2 : len2 = c) by (unfold len2; clear - CLE; lia).
assert (Cr1 : 1 <= c <= 16384) by (clear - CNZ Hc; lia).
assert (Cr2 : 0 <= -1 * c + (k - len1) <= 16383) by (clear - CNZ Hc CLE Hkl; lia).
pose proof (PMBSRP2.bsrFge_conc fx4 R4 MV4 VC) as P. unfold VC in P. cbn beta iota in P.
L5SAR.feed P ltac:(first [assumption | unfold PMBSRP2.aligned; assumption | clear - Hl0 Hkl Hc QPR Q0a Q0b Q0c Q0d Q0e Q0f Q0 Q4 SLO SHI SPT; lia]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & T1 & T10 & T11 & T12 & T24 & S8' & Gv64 & Gv288 & Gv264 & Gv272 & Gvd256 & Gv280 & _).
exists fx5, R5, M5v. split; [exact MS5|]. split; [exact MG5|].
split; [intros i Hi N; apply FRZ5; [exact Hi| intros Y; apply N; left; clear - Y; lia| intros Y; apply N; right; left; clear - Y; lia| intros Y; apply N; right; right; clear - Y; lia]|].
split; [intros x Hx; apply KS5; revert x Hx; apply (PMBSR1.sub_in PMBSRP2.KS_bsrFge); vm_compute; reflexivity|].
rewrite E2. split; [exact T1|]. split; [exact T10|]. split; [exact T11|]. split; [exact T12|]. split; [exact T24|].
split; [exact S8'|]. split; [exact Gv288|]. split; [exact Gv280|]. split; [exact Gv264| exact Gv272].
- assert (E2 : len2 = k - len1) by (unfold len2; clear - CGT; lia).
assert (Cr1 : 2 <= c <= 16384) by (clear - CGT Hc Hkl; lia).
assert (Cr2 : 1 <= c - (k - len1) <= 16383) by (clear - CGT Hc Hkl; lia).
assert (Cr3 : 1 <= k - len1 <= 16383) by (clear - CGT Hc Hkl; lia).
pose proof (PMBSRP2.bsrFlt_conc fx4 R4 MV4 VC) as P. unfold VC in P. cbn beta iota in P.
L5SAR.feed P ltac:(first [assumption | unfold PMBSRP2.aligned; assumption | clear - Hl0 Hkl Hc Cr1 Cr2 Cr3 QPR Q0a Q0b Q0c Q0d Q0e Q0f; lia]).
destruct P as (fx5a & R5a & M5a & MG5a & _ & FRZ5a & MS5a & KS5a & T11a & T12a & Gv64a & S8a & Gv288a & Gv264a & Gv272a & Gvd256a & Gv280a & _).
set (Wt := fun i => (F + 64 <= i < F + 72) \/ ((F / 8) + 2147450880 + 8 <= i < (F / 8) + 2147450880 + 9) \/ (os + 256 <= i < os + 296)).
assert (FZa : forall i, 0 <= i < 2 ^ 64 -> ~ Wt i -> M5a (Z_to_bv 64 i) = MV4 (Z_to_bv 64 i)).
{ intros i Hi N. apply FRZ5a; [exact Hi| intros Y; apply N; left; clear - Y; lia| intros Y; apply N; right; left; clear - Y; lia| intros Y; apply N; right; right; clear - Y; lia]. }
pose proof (TRANS MV4 M5a Wt FZa) as TRa.
assert (Ta0 : L5.img_clear M5a 65536 1269760).
{ intros i Hi. rewrite (TRa 65536 1204224 ltac:(clear; lia) ltac:(clear; lia)) by (first [clear - Hi; lia | intros j Hj; unfold Wt; clear - Hj DF1 DF2 QFR O1; lia]). apply U0; exact Hi. }
assert (Ta1 : L5.u64_at RSEGS M5a 1296952 2147450880).
{ apply (L5C.u64_at_agree RSEGS MV4 M5a); [intros i Hi; apply (TRa 1296952 8); [clear; lia| clear; lia| intros j Hj; unfold Wt; clear - Hj DF1 DF2 QFR O1; lia| exact Hi]| clear; lia| clear; lia| exact U1]. }
assert (Ta2 : L5.u32_at RSEGS M5a 1296960 1).
{ apply (PMF.u32_at_agree RSEGS MV4 M5a); [intros i Hi; apply (TRa 1296960 4); [clear; lia| clear; lia| intros j Hj; unfold Wt; clear - Hj DF1 DF2 QFR O1; lia| exact Hi]| clear; lia| clear; lia| exact U2]. }
assert (TXa : forall a v, X <= a -> a + 8 <= X + 56 -> L5.u64_at RSEGS MV4 a v -> L5.u64_at RSEGS M5a a v).
{ intros a v Ha Hb Y. apply (L5C.u64_at_agree RSEGS MV4 M5a); [intros i Hi; apply (TRa a 8); [clear - Ha Q0e; lia| clear - Hb QX; lia| intros j Hj; unfold Wt; clear - Hj Ha Hb QXF QXo DF1 DF2 QX QFR; lia| exact Hi]| clear - Ha Q0e; lia| clear - Hb QX; lia| exact Y]. }
assert (Taoz : L5KA.zeros_at M5a (((os + 8) / 8) + 2147450880) 36).
{ apply (L5KA.zeros_at_agree1 MV4 M5a); [| exact UOZ]. intros i Hi. apply (TRa (((os + 8) / 8) + 2147450880) 36); [| | | exact Hi].
- pose proof (Z.div_pos (os + 8) 8 ltac:(clear - O1; lia) ltac:(clear; lia)) as Hq. clear - Hq; lia.
- assert (Hq : (os + 8) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; clear - O1; lia). clear - Hq; lia.
- intros j Hj. assert (E8 : (os + 8) / 8 = os / 8 + 1) by (rewrite <- (Z.div_add os 1 8) by lia; f_equal; lia). rewrite E8 in Hj.
assert (D3 : os / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; clear - O1; lia).
assert (D4 : 0 <= os / 8) by (apply Z.div_pos; clear - O1; lia).
unfold Wt. destruct QoSF as [Ya1|Ya1]; destruct GFBIG as [Ya2|Ya2]; destruct OBIG as [Ya3|Ya3]; clear - Hj Ya1 Ya2 Ya3 D3 D4 QX QFR O1 DF1 DF2; lia. }
assert (Tafl : L5.u64_at RSEGS M5a (F + 120) fl).
{ apply (L5C.u64_at_agree RSEGS MV4 M5a); [intros i Hi; apply (TRa (F + 120) 8); [clear - QFR; lia| clear - QFR; lia| intros j Hj; unfold Wt; destruct GFBIG as [Ya2|Ya2]; clear - Hj Ya2 DF1 DF2 QX QFR QoF; lia| exact Hi]| clear - QFR; lia| clear - QFR; lia| exact UFL]. }
assert (Taf32 : L5.u64_at RSEGS M5a (F + 32) ((k - len1) + len1)).
{ apply (L5C.u64_at_agree RSEGS MV4 M5a); [intros i Hi; apply (TRa (F + 32) 8); [clear - QFR; lia| clear - QFR; lia| intros j Hj; unfold Wt; destruct GFBIG as [Ya2|Ya2]; clear - Hj Ya2 DF1 DF2 QX QFR QoF; lia| exact Hi]| clear - QFR; lia| clear - QFR; lia| exact UF32']. }
assert (Taz64 : L5KA.zeros_at M5a (((F + 64) / 8) + 2147450880) 1).
{ replace ((F + 64) / 8) with (F / 8 + 8) by (rewrite <- (Z.div_add F 8 8) by lia; f_equal; lia).
intros i Hi. replace i with 0 by (clear - Hi; lia). rewrite Z.add_0_r. replace (F / 8 + 8 + 2147450880) with ((F / 8) + 2147450888) by (clear; lia).
apply (L5ADHR.byte_of_u8 M5a _ 0 S8a); [right| ]; clear - DF1 DF2; lia. }
assert (TwX : L5.writable RSEGS M5a X 56) by exact (L5.writable_grows RSEGS MV4 M5a X 56 MG5a UX).
assert (Twos : L5.writable RSEGS M5a os 296) by exact (L5.writable_grows RSEGS MV4 M5a os 296 MG5a UOW).
assert (TdF : L5.defined M5a F 128) by exact (L5.defined_grows MV4 M5a F 128 MG5a UFD).
assert (TwF : L5.writable RSEGS M5a F 128) by exact (L5.writable_grows RSEGS MV4 M5a F 128 MG5a UFW).
assert (TwS : L5.writable RSEGS M5a ((F / 8) + 2147450880) 16) by exact (L5.writable_grows RSEGS MV4 M5a _ 16 MG5a UFSW).
assert (Twl : L5.writable RSEGS M5a fl 1) by exact (L5.writable_grows RSEGS MV4 M5a fl 1 MG5a UFLW).
assert (Ta24 : L5.u64_at RSEGS M5a (X + 24) p) by (apply TXa; [clear; lia| clear; lia| exact UX24]).
assert (Ta8 : L5.u64_at RSEGS M5a (X + 8) (F + 32)) by (apply TXa; [clear; lia| clear; lia| exact UX8]).
assert (Ta16 : L5.u64_at RSEGS M5a (X + 16) F) by (apply TXa; [clear; lia| clear; lia| exact UX16]).
assert (Ta48 : L5.u64_at RSEGS M5a (X + 48) F) by (apply TXa; [clear; lia| clear; lia| exact UX48]).
assert (Ya : forall x, In x [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat -> getr R5a (reg x) = getr R4 (reg x)).
{ intros x Hx. apply KS5a. revert x Hx. apply (PMBSR1.sub_in PMBSRP2.KS_bsrFlt). vm_compute. reflexivity. }
pose proof (PMBSRP2.bsrFlt2_conc fx5a R5a M5a VC) as P. unfold VC in P. cbn beta iota in P.
L5SAR.feed P ltac:(first [assumption | unfold PMBSRP2.aligned; assumption | rewrite (Ya _) by inl; assumption
| clear - Hl0 Hkl Hc Cr1 Cr2 Cr3 QPR Q0a Q0b Q0c Q0d Q0e Q0f Q0 Q4 SLO SHI SPT; lia]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & T1 & T10 & T11 & T24 & S8' & Gv264 & Gv272 & Gvd256 & Gv280 & Gv288 & Gv64 & _).
exists fx5, R5, M5v. split; [eapply msteps_trans; [exact MS5a| exact MS5]|]. split; [intros x Hx; apply MG5; apply MG5a; exact Hx|].
split; [intros i Hi N; rewrite FRZ5; [apply FZa; [exact Hi| exact N]| exact Hi| intros Y; apply N; left; clear - Y; lia| intros Y; apply N; right; left; clear - Y; lia| intros Y; apply N; right; right; clear - Y; lia]|].
split; [intros x Hx; rewrite (KS5 x) by (revert x Hx; apply (PMBSR1.sub_in PMBSRP2.KS_bsrFlt2); vm_compute; reflexivity); apply Ya; revert x Hx; apply (PMBSR1.sub_in [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat); vm_compute; reflexivity|].
rewrite E2. split; [exact T1|]. split; [exact T10|]. split; [exact T11|]. split; [rewrite (KS5 12%nat) by inl; exact T12a|]. split; [exact T24|].
split; [exact S8'|]. split; [exact Gv288|]. split; [exact Gv280|]. split; [exact Gv264| exact Gv272]. }
destruct HEADC as (fx5 & R5 & M5v & MS5 & MG5 & FRZ5 & KS5 & T1 & T10 & T11 & T12 & T24 & S8' & V5288 & V5280 & V5264 & V5272).
apply (CRUN fx4 R4 M4 model4 LK4 Aw4 fx5 R5 M5v 723116 0x7760c
(fun i => (F + 64 <= i < F + 72) \/ ((F / 8) + 2147450880 + 8 <= i < (F / 8) + 2147450880 + 9) \/ (os + 256 <= i < os + 296)) BI4);
[intros a [Y|[Y|Y]]; [left; exact Y| right; left; exact Y| right; right; left; exact Y]| exact MS5| exact MG5| exact FRZ5|].
intros M5 model5 BI5 VIS5 MGM5 FR5.
assert (FR5' : forall a, (X <= a < X + 56 \/ F + 32 <= a < F + 64 \/ F + 72 <= a < F + 120 \/ a = (F / 8) + 2147450884) -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
{ intros a Ha. apply FR5; [clear - Ha QX QFR DF1 DF2; lia|]. intros [Y|[Y|Y]]; destruct Ha as [Z1|[Z1|[Z1|Z1]]]; clear - Y Z1 QXF QXo QoF QoSF DF1 DF2 QFR QX O1 GFBIG OBIG; lia. }
assert (T5X : forall a v, (X <= a /\ a + 8 <= X + 56 \/ F + 32 <= a /\ a + 8 <= F + 64) -> L5.u64_at RSEGS M4 a v -> L5.u64_at RSEGS M5 a v).
{ intros a v Ha Y. apply (L5C.u64_at_agree RSEGS M4 M5); [intros i Hi; apply FR5'; clear - Ha Hi; lia| clear - Ha Q0e Q0c; lia| clear - Ha QX QFR; lia| exact Y]. }
assert (T5O : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M5v a v -> L5.u64_at RSEGS M5 a v).
{ intros a v Ha Hb Y. rewrite <- VIS5 in Y. exact (TO5 M5 a v Ha Hb Y). }
destruct (PMBUK.vis_facts L ar C HI LYa HIok M model LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr [] G
WA [] M4 model4 LK4 cr Aw4 BI4) as (_ & _ & _ & (_ & _ & _ & _ & VSH4)). change (ff_bytes 1 / 8) with 16 in VSH4.
assert (T5S8 : L5.u8_at RSEGS M5 ((F / 8) + 2147450888) 248).
{ rewrite <- VIS5 in S8'. apply (proj1 (L5A.u8_at_vis (ahid Aw4 model4) M5 ((F / 8) + 2147450888) 248 (L5A.avis_sub (ahid Aw4 model4) (F / 8 + SB) 16 ((F / 8) + 2147450888) 1 VSH4 ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) ltac:(clear - DF1; lia) ltac:(clear - DF2; lia))). exact S8'. }
assert (T5S4 : L5.u8_at RSEGS M5 ((F / 8) + 2147450884) 0).
{ apply (L5C.u8_at_agree RSEGS M4 M5); [intros i Hi; apply FR5'; clear - Hi; lia| clear - DF1; lia| clear - DF2; lia| exact SH4]. }
apply (MEMCALL fx5 R5 M5 model5 LK4 Aw4 723244 (p + len1) qc len2 BI5).
{ exact T1. }
{ split; [clear; lia| reflexivity]. }
{ rewrite (KS5 2%nat) by inl. exact Y2. }
{ rewrite (KS5 4%nat) by inl. exact Y4. }
{ exact T10. } { exact T11. } { exact T12. }
{ clear - Hl0; lia. } { clear - L2R Hl0; lia. } { clear - L2R; lia. } { clear; lia. } { clear - L2R Hkl Hl0 Hk; lia. }
intros fx6 R6 M6 model6 RP6 DEF6 BI6 HP6.
assert (R6c : forall j, In j L5SAR.cs_all -> getr R6 (reg j) = getr R5 (reg j)) by (intros j Hj; exact (L5SAR.cs_of_preserved R5 R6 j RP6 Hj)).
destruct (CKEEP M5 M6 2560 [(p + len1, len2)] HP6 ltac:(clear; lia) ltac:(intros a Ha; apply (CKM a Ha); clear - L2R Hl0; lia)) as (K6a & K6b).
assert (O6 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M5 a v -> L5.u64_at RSEGS M6 a v)
by (intros a v Ha Hb Y; apply (OKEEP M5 M6 (p + len1) len2 HP6 ltac:(clear - Hl0; lia) ltac:(clear - L2R Hl0; lia) a v Ha Hb Y)).
pose proof BI6 as (HH6 & _ & _ & _ & _ & _ & EK6 & DK6 & _).
assert (U6264 : L5.u64_at RSEGS M6 (os + 264) qc) by (apply O6; [clear; lia| clear; lia| apply T5O; [clear; lia| clear; lia| exact V5264]]).
assert (U6272 : L5.u64_at RSEGS M6 (os + 272) 16384) by (apply O6; [clear; lia| clear; lia| apply T5O; [clear; lia| clear; lia| exact V5272]]).
assert (U6280 : L5.u64_at RSEGS M6 (os + 280) qc) by (apply O6; [clear; lia| clear; lia| apply T5O; [clear; lia| clear; lia| exact V5280]]).
assert (U6288 : L5.u64_at RSEGS M6 (os + 288) c) by (apply O6; [clear; lia| clear; lia| apply T5O; [clear; lia| clear; lia| exact V5288]]).
assert (PA6 : PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M6 op ois (PMSPA.with_src s0 (PM.SRC qc qc c)))
by (apply PARS; [exact EK6| exact DK6| exact U6264| exact U6272| exact U6280| exact U6288| clear; lia| clear - Hc; lia| clear - Hc; lia]).
pose proof (L5SAR.ek_callee L ar LB [] FF [(F, 1, X + 32)] sp 20480 X 2560 [(p + len1, len2)] [(p + len1, len2)] M5 M6 HP6 ltac:(clear - HX1; lia) ltac:(clear - HX1; lia) (fun a _ Y => Y)) as EK56.
assert (WSP : PMKB.wapp [(p + len1, len2)]).
{ apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - DSH L2R Hl0; Lia.lia| apply PMKB.wapp_nil]. }
assert (NDP : forall a, ~ (p <= a < p + k) -> ~ (p + len1 <= a < p + len1 + len2)) by (intros a N Y; apply N; clear - Y L2R Hl0; lia).
assert (EK45 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M4 M5).
{ apply (EKC M4 M5 [(os + 256, 40)] _ FR5). intros a [Y|[Y|Y]]; [left; clear - Y; lia| right; left; clear - Y; lia| right; right; intros Ho; apply (Ho (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]]. }
assert (IA5 : PM.iss_at RSEGS PMB.AD PMSPA.accA M5 ois str (PM.STRM g4 eg st4)).
{ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 _ M4 M5 EK45 WSW FRB BRB ois str _ AOI); [exact SOWN| exact OUTIS| exact OUTBLK| exact IA4]. }
assert (IA6 : PM.iss_at RSEGS PMB.AD PMSPA.accA M6 ois str (PM.STRM g4 eg st4)).
{ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 _ M5 M6 EK56 WSP FRB BRB ois str _ AOI SOWN); [| |exact IA5].
- intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX i Y) as (_ & X2 & _). apply X2. exact Hi.
- intros c1 n1 q1 E i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX i Y) as (_ & _ & _ & _ & _ & _ & _ & Dx8 & _). apply (Dx8 c1 n1 q1 E). exact Hi. }
assert (BASE5 : PMSTA.base_okA RSEGS PMB.AD M5).
{ apply (PMBSK.base_keep L ar C LY LB FF sp 20480 _ M4 M5 EK45); [| exact BASE4].
intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha O1. lia. }
assert (BASE6 : PMSTA.base_okA RSEGS PMB.AD M6).
{ apply (PMBSK.base_keep L ar C LY LB FF sp 20480 _ M5 M6 EK56); [| exact BASE5].
intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX a Y) as (_ & _ & _ & _ & _ & _ & _ & _ & X9). apply X9. exact Ha. }
destruct (STATEV M6 model6 LK4 Aw4 qc c k BI6 PA6 BASE6) as ((W60 & W61 & W62) & (W6X & W6X24 & W6X8 & W6X16 & W6X48) & (W6OZ & W6OW & W6264 & W6272 & W6D256 & W6280 & W6288 & OAV6)
& (W6FD & W6FW & W6FSW & W6FL & W6FLW & _ & _ & _)).
{ apply K6a; [left; clear; lia| apply T5X; [left; clear; lia| exact X8]]. }
{ apply K6a; [left; clear; lia| apply T5X; [left; clear; lia| exact X16]]. }
{ apply K6a; [left; clear; lia| apply T5X; [left; clear; lia| exact X24]]. }
{ apply K6a; [left; clear; lia| apply T5X; [left; clear; lia| exact X48]]. }
{ apply K6a; [right; clear; lia| apply T5X; [right; clear; lia| exact F32]]. }
{ apply K6b; [clear; lia| exact T5S4]. }
{ apply K6b; [clear; lia| exact T5S8]. }
set (MV6 := mrestrict (ahid Aw4 model6) M6) in *.
assert (R65 : forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat -> getr R6 (reg x) = getr R4 (reg x)).
{ intros x Hx. rewrite (R6c x) by (revert x Hx; apply (PMBSR1.sub_in L5SAR.cs_all); vm_compute; reflexivity). apply KS5. exact Hx. }
assert (Dr1 : 1 <= c <= 16384) by (clear - CNZ Hc; lia).
assert (Dr2 : 0 <= c - len2 <= 16383) by (clear - L2R Hc Hkl; lia).
assert (Dr4 : 1 <= len2 <= 16384) by (clear - L2R Hkl; lia).
assert (Dr5 : 4096 <= qc <= 140737488338944) by (clear - Q0 Q4 SLO SHI SPT; lia).
cfeed P (PMBSRP2.bsrM2_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 36%nat => os | 37%nat => p | 39%nat => len1 | 40%nat => len2
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBSRP2.aligned; assumption
| rewrite (R65 _) by inl; assumption | rewrite (R6c 24%nat) by inl; exact T24
| clear - Hl0 Dr1 Dr2 Dr4 Dr5 QPR Q0a Q0b Q0c Q0d Q0e Q0f; lia]).
destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Z10 & Z12 & Z22 & Z288 & Z280 & Z264 & Z272).
apply (CRUN fx6 R6 M6 model6 LK4 Aw4 fx7 R7 M7v 723244 0xb0b3c (fun a => os + 256 <= a < os + 296) BI6); [intros a Y; right; right; left; exact Y| exact MS7| exact MG7| |].
{ intros i Hi N. apply FRZ7; [exact Hi| intros Y; apply N; clear - Y; lia]. }
intros M7 model7 BI7 VIS7 MGM7 FR7.
assert (TO7 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M7v a v -> L5.u64_at RSEGS M7 a v).
{ intros a v Ha Hb Y. rewrite <- VIS7 in Y. apply (proj1 (L5A.u64_at_vis _ M7 a v ltac:(apply OAV6; clear - Ha Hb; lia) ltac:(clear - Ha O1; lia) ltac:(clear - Hb O1; lia))). exact Y. }
assert (R76 : forall x, In x [2; 3; 4; 8; 9; 25; 26]%nat -> getr R7 (reg x) = getr R4 (reg x)).
{ intros x Hx. rewrite (KS7 x) by (revert x Hx; apply (PMBSR1.sub_in PMBSRP2.KS_bsrM2); vm_compute; reflexivity). apply R65. revert x Hx. apply (PMBSR1.sub_in [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat). vm_compute. reflexivity. }
apply (EXITP fx7 R7 M7 model7 LK4 Aw4 (qc + len2) (c - len2) g4 st4 (len1 + len2) BI7).
+ rewrite (R76 2%nat) by inl. exact Y2.
+ rewrite (R76 8%nat) by inl. exact Y8.
+ rewrite (R76 9%nat) by inl. exact Y9.
+ exact Z22.
+ rewrite (R76 25%nat) by inl. exact Y25.
+ rewrite (R76 26%nat) by inl. exact Y26.
+ rewrite (R76 3%nat) by inl. exact Y3.
+ rewrite (R76 4%nat) by inl. exact Y4.
+ apply (L5C.u64_at_agree RSEGS M6 M7); [intros i Hi; apply FR7; [clear - Hi QX; lia| clear - Hi QXo; lia]| clear - Q0e; lia| clear - QX; lia|].
apply K6a; [left; clear; lia| apply T5X; [left; clear; lia| exact X16]].
+ apply TO7; [clear; lia| clear; lia| exact Z264].
+ apply TO7; [clear; lia| clear; lia| exact Z272].
+ apply TO7; [clear; lia| clear; lia| exact Z280].
+ apply TO7; [clear; lia| clear; lia| exact Z288].
+ clear - Dr4; lia.
+ clear - Dr2; lia.
+ clear - Hc Dr4 Dr2; lia.
+ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 _ M6 M7 (EKO M6 M7 FR7) WSW FRB BRB ois str _ AOI); [exact SOWN| exact OUTIS| exact OUTBLK| exact IA6].
+ clear - Hg4 Hg4e Hc; lia.
+ exact Hst4.
+ clear - L2R Hl0; lia.
+ clear - Hl1 Hg4; lia.
+ intros _. clear - Dr4 Hl0; lia.
+ intros Y. exfalso. clear - Y Dr4 Hl0; lia.
}
assert (FILLTHEN : forall (fx3 : FPState) R3 M3 model3 LK3 Aw3 (len1 : Z),
PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M3 model3 LK3 cr Aw3 ->
getr R3 (reg 1) = Z_to_bv 64 723116 -> getr R3 (reg 2) = Z_to_bv 64 X -> getr R3 (reg 8) = Z_to_bv 64 sp -> getr R3 (reg 9) = Z_to_bv 64 X ->
getr R3 (reg 10) = Z_to_bv 64 os -> getr R3 (reg 11) = Z_to_bv 64 qc -> getr R3 (reg 12) = Z_to_bv 64 16384 ->
getr R3 (reg 18) = Z_to_bv 64 (((os + 288) / 8) + 2147450880) -> getr R3 (reg 19) = Z_to_bv 64 os -> getr R3 (reg 20) = Z_to_bv 64 len1 ->
getr R3 (reg 21) = Z_to_bv 64 (((os + 280) / 8) + 2147450880) -> getr R3 (reg 22) = Z_to_bv 64 (os + 280) -> getr R3 (reg 23) = Z_to_bv 64 (os + 288) ->
getr R3 (reg 25) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R3 (reg 26) = Z_to_bv 64 F -> getr R3 (reg 27) = Z_to_bv 64 2147450880 ->
getr R3 (reg 3) = getr R (reg 3) -> getr R3 (reg 4) = getr R (reg 4) ->
L5.u64_at RSEGS M3 (X + 8) (F + 32) -> L5.u64_at RSEGS M3 (X + 16) F -> L5.u64_at RSEGS M3 (X + 24) p -> L5.u64_at RSEGS M3 (X + 48) F ->
L5.u64_at RSEGS M3 (F + 32) k -> L5.u8_at RSEGS M3 ((F / 8) + 2147450884) 0 -> L5.u8_at RSEGS M3 ((F / 8) + 2147450888) 248 ->
PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M3 op ois (PMSPA.with_src s0 (PM.SRC qc qc 0)) ->
PM.iss_at RSEGS PMB.AD PMSPA.accA M3 ois str (PM.STRM g eg sst) -> PMSTA.base_okA RSEGS PMB.AD M3 ->
len1 = rem -> len1 < k ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx3 R3 0xb0e58 M3 model3) K).
{ intros fx3 R3 M3 model3 LK3 Aw3 len1 BI3 Y1 Y2 Y8 Y9 Y10 Y11 Y12 Y18 Y19 Y20 Y21 Y22 Y23 Y25 Y26 Y27 Y3 Y4 X8 X16 X24 X48 F32 SH4 SH8 PA3 IA3 BASE3 Hl1 Hl1k.
apply (FILLCALL fx3 R3 M3 model3 LK3 Aw3 BI3 Y1 Y2 Y3 Y4 Y10 Y11 Y12 PA3 IA3 BASE3).
intros fx4 R4 M4 model4 LK4 Aw4 c g4 st4 RP4 A10c Hc Hg4 Hg4e Hst4 Hc0 BI4 HP4 PA4 IA4 BASE4.
assert (R4c : forall j, In j L5SAR.cs_all -> getr R4 (reg j) = getr R3 (reg j)) by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
destruct (CKEEP M3 M4 18432 _ HP4 ltac:(clear; lia)) as (K4a & K4b).
{ intros a Ha. apply OUTWS. unfold SB. destruct Ha as [Y|[Y|Y]]; [left; clear - Y HX1; lia| right; left; clear - Y; lia| right; right; clear - Y; lia]. }
apply (CPART fx4 R4 M4 model4 LK4 Aw4 len1 c g4 st4 BI4).
- rewrite (R4c 2%nat) by inl. exact Y2.
- rewrite (R4c 8%nat) by inl. exact Y8.
- rewrite (R4c 9%nat) by inl. exact Y9.
- exact A10c.
- rewrite (R4c 18%nat) by inl. exact Y18.
- rewrite (R4c 19%nat) by inl. exact Y19.
- rewrite (R4c 20%nat) by inl. exact Y20.
- rewrite (R4c 21%nat) by inl. exact Y21.
- rewrite (R4c 22%nat) by inl. exact Y22.
- rewrite (R4c 23%nat) by inl. exact Y23.
- rewrite (R4c 25%nat) by inl. exact Y25.
- rewrite (R4c 26%nat) by inl. exact Y26.
- rewrite (R4c 27%nat) by inl. exact Y27.
- rewrite (R4c 3%nat) by inl. exact Y3.
- rewrite (R4c 4%nat) by inl. exact Y4.
- apply K4a; [left; clear; lia| exact X8].
- apply K4a; [left; clear; lia| exact X16].
- apply K4a; [left; clear; lia| exact X24].
- apply K4a; [left; clear; lia| exact X48].
- apply K4a; [right; clear; lia| exact F32].
- apply K4b; [clear; lia| exact SH4].
- apply K4b; [clear; lia| exact SH8].
- exact PA4.
- exact IA4.
- exact BASE4.
- exact Hl1.
- exact Hl1k.
- exact Hc.
- exact Hg4.
- exact Hg4e.
- exact Hst4.
- exact Hc0. }
assert (M1C : forall (fx4 : FPState) R4 M4 model4 (len1 : Z),
PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M4 model4 LK2 cr Aw ->
getr R4 (reg 2) = Z_to_bv 64 X -> getr R4 (reg 8) = Z_to_bv 64 sp -> getr R4 (reg 9) = Z_to_bv 64 X ->
getr R4 (reg 18) = Z_to_bv 64 (((os + 288) / 8) + 2147450880) -> getr R4 (reg 19) = Z_to_bv 64 os -> getr R4 (reg 20) = Z_to_bv 64 len1 ->
getr R4 (reg 21) = Z_to_bv 64 (((os + 280) / 8) + 2147450880) -> getr R4 (reg 22) = Z_to_bv 64 k -> getr R4 (reg 23) = Z_to_bv 64 (os + 288) ->
getr R4 (reg 24) = Z_to_bv 64 (os + 280) ->
getr R4 (reg 25) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R4 (reg 26) = Z_to_bv 64 F -> getr R4 (reg 27) = Z_to_bv 64 2147450880 ->
getr R4 (reg 3) = getr R (reg 3) -> getr R4 (reg 4) = getr R (reg 4) ->
L5.u64_at RSEGS M4 (X + 8) (F + 32) -> L5.u64_at RSEGS M4 (X + 16) F -> L5.u64_at RSEGS M4 (X + 24) p -> L5.u64_at RSEGS M4 (X + 48) F ->
L5.u64_at RSEGS M4 (F + 32) k -> L5.u8_at RSEGS M4 ((F / 8) + 2147450884) 0 -> L5.u8_at RSEGS M4 ((F / 8) + 2147450888) 248 ->
L5.u64_at RSEGS M4 (os + 264) qc -> L5.u64_at RSEGS M4 (os + 272) 16384 -> L5.u64_at RSEGS M4 (os + 280) de -> L5.u64_at RSEGS M4 (os + 288) rem ->
PM.iss_at RSEGS PMB.AD PMSPA.accA M4 ois str (PM.STRM g eg sst) -> PMSTA.base_okA RSEGS PMB.AD M4 ->
1 <= rem -> len1 = Z.min k rem ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx4 R4 722916 M4 model4) K).
{ intros fx4 R4 M4 model4 len1 BI4 Y2 Y8 Y9 Y18 Y19 Y20 Y21 Y22 Y23 Y24 Y25 Y26 Y27 Y3 Y4 X8 X16 X24 X48 F32 SH4 SH8 C264 C272 C280 C288 IA4 BASE4 Hrm1 Hl1.
pose proof BI4 as (_ & _ & _ & _ & _ & _ & EK4 & DK4 & _).
assert (PA4 : PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M4 op ois (PMSPA.with_src s0 (PM.SRC qc de rem))) by (apply PARS; assumption).
destruct (STATEV M4 model4 LK2 Aw de rem k BI4 PA4 BASE4 X8 X16 X24 X48 F32 SH4 SH8)
as ((U0 & U1 & U2) & (UX & UX24 & UX8 & UX16 & UX48) & (UOZ & UOW & U264 & U272 & UD256 & U280 & U288 & OAV4) & (UFD & UFW & UFSW & UFL & UFLW & UF32 & US4 & US8)).
set (MV4 := mrestrict (ahid Aw model4) M4) in *.
assert (EKO : forall Ma Mb, (forall i, 0 <= i < 2 ^ 64 -> ~ (os + 256 <= i < os + 296) -> Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)) -> L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] Ma Mb).
{ intros Ma Mb FZ. apply (EKC Ma Mb [(os + 256, 40)] (fun a => os + 256 <= a < os + 296) FZ). intros a Y. right; right. intros Ho.
apply (Ho (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
assert (QDE : 4096 <= de <= 140737488338944) by (clear - G1 G2 G3 Q0 Q4 SLO SHI SPT; lia).
set (VS := fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end).
unfold PMSPA.cfg.
destruct (Z.eq_dec len1 k) as [LK1|LNK].
-
assert (Rr1 : 1 <= rem <= 16384) by (clear - Hrm1 G3 G1; lia).
assert (Rr2 : 0 <= rem - k <= 16383) by (clear - Hl1 LK1 Rr1 Hk; rewrite LK1 in Hl1; destruct (Z.min_spec k rem) as [[X1 X2]|[X1 X2]]; lia).
rewrite LK1 in Y20.
pose proof (PMBSRP2.bsrM1eq_conc fx4 R4 MV4 VS) as P. unfold VS in P. cbn beta iota in P.
L5SAR.feed P ltac:(first [assumption | unfold PMBSRP2.aligned; assumption | clear - Rr1 Rr2 Hk QDE QPR Q0a Q0b Q0c Q0d Q0e Q0f; lia]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z10 & Z12 & Z288 & Z280 & Z264 & Z272).
apply (CRUN fx4 R4 M4 model4 LK2 Aw fx5 R5 M5v 722916 0xb0b3c (fun a => os + 256 <= a < os + 296) BI4); [intros a Y; right; right; left; exact Y| exact MS5| exact MG5| |].
{ intros i Hi N. apply FRZ5; [exact Hi| intros Y; apply N; clear - Y; lia]. }
intros M5 model5 BI5 VIS5 MGM5 FR5.
assert (TO5 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M5v a v -> L5.u64_at RSEGS M5 a v).
{ intros a v Ha Hb Y. rewrite <- VIS5 in Y. apply (proj1 (L5A.u64_at_vis _ M5 a v ltac:(apply OAV4; clear - Ha Hb; lia) ltac:(clear - Ha O1; lia) ltac:(clear - Hb O1; lia))). exact Y. }
apply (EXITP fx5 R5 M5 model5 LK2 Aw (de + k) (rem - k) g sst k BI5).
+ rewrite (KS5 2%nat) by inl. exact Y2.
+ rewrite (KS5 8%nat) by inl. exact Y8.
+ rewrite (KS5 9%nat) by inl. exact Y9.
+ rewrite (KS5 22%nat) by inl. exact Y22.
+ rewrite (KS5 25%nat) by inl. exact Y25.
+ rewrite (KS5 26%nat) by inl. exact Y26.
+ rewrite (KS5 3%nat) by inl. exact Y3.
+ rewrite (KS5 4%nat) by inl. exact Y4.
+ apply (L5C.u64_at_agree RSEGS M4 M5); [intros i Hi; apply FR5; [clear - Hi QX; lia| clear - Hi QXo; lia]| clear - Q0e; lia| clear - QX; lia| exact X16].
+ apply TO5; [clear; lia| clear; lia| exact Z264].
+ apply TO5; [clear; lia| clear; lia| exact Z272].
+ apply TO5; [clear; lia| clear; lia| exact Z280].
+ apply TO5; [clear; lia| clear; lia| exact Z288].
+ clear - G1 Hk; lia.
+ clear - Rr2; lia.
+ clear - G3 Hk; lia.
+ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 _ M4 M5 (EKO M4 M5 FR5) WSW FRB BRB ois str _ AOI); [exact SOWN| exact OUTIS| exact OUTBLK| exact IA4].
+ clear - SZ; lia.
+ intros Y; exact Y.
+ clear - Hk; lia.
+ clear; lia.
+ intros _; clear - Hk; lia.
+ intros Y. exfalso. clear - Y Hk; lia.
-
assert (LR : len1 = rem /\ rem < k) by (clear - Hl1 LNK; destruct (Z.min_spec k rem) as [[X1 X2]|[X1 X2]]; lia).
destruct LR as (LR1 & LR2).
assert (Rr1 : 1 <= rem <= 16383) by (clear - Hrm1 LR2 Hk; lia).
assert (Rr2 : 2 <= k <= 16384) by (clear - Hrm1 LR2 Hk; lia).
assert (Rr3 : 1 <= -1 * rem + k <= 16383) by (clear - Hrm1 LR2 Hk; lia).
rewrite LR1 in Y20.
pose proof (PMBSRP2.bsrM1ne_conc fx4 R4 MV4 VS) as P. unfold VS in P. cbn beta iota in P.
L5SAR.feed P ltac:(first [assumption | unfold PMBSRP2.aligned; assumption | clear - Rr1 Rr2 Rr3 Hk QDE QPR Q0a Q0b Q0c Q0d Q0e Q0f; lia]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z10 & Z11 & Z12 & Z13 & Z22 & Z280 & Z288 & Z264 & Z272).
apply (CRUN fx4 R4 M4 model4 LK2 Aw fx5 R5 M5v 722916 0xb0e58 (fun a => os + 256 <= a < os + 296) BI4); [intros a Y; right; right; left; exact Y| exact MS5| exact MG5| |].
{ intros i Hi N. apply FRZ5; [exact Hi| intros Y; apply N; clear - Y; lia]. }
intros M5 model5 BI5 VIS5 MGM5 FR5.
assert (TO5 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M5v a v -> L5.u64_at RSEGS M5 a v).
{ intros a v Ha Hb Y. rewrite <- VIS5 in Y. apply (proj1 (L5A.u64_at_vis _ M5 a v ltac:(apply OAV4; clear - Ha Hb; lia) ltac:(clear - Ha O1; lia) ltac:(clear - Hb O1; lia))). exact Y. }
assert (T5X : forall a v, (X <= a /\ a + 8 <= X + 56 \/ F <= a /\ a + 8 <= F + 128) -> L5.u64_at RSEGS M4 a v -> L5.u64_at RSEGS M5 a v).
{ intros a v Ha Y. apply (L5C.u64_at_agree RSEGS M4 M5); [intros i Hi; apply FR5; [clear - Ha Hi QX QFR; lia| clear - Ha Hi QXo QoF; lia]| clear - Ha Q0e Q0c; lia| clear - Ha QX QFR; lia| exact Y]. }
assert (T5S : forall a v, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16 -> L5.u8_at RSEGS M4 a v -> L5.u8_at RSEGS M5 a v).
{ intros a v Ha Y. apply (L5C.u8_at_agree RSEGS M4 M5); [intros i Hi; apply FR5; [clear - Ha Hi DF1 DF2; lia| destruct OBIG as [Yo|Yo]; clear - Ha Hi Yo DF1 DF2; lia]| clear - Ha DF1; lia| clear - Ha DF2; lia| exact Y]. }
pose proof BI5 as (_ & _ & _ & _ & _ & _ & EK5 & DK5 & _).
assert (C5264 : L5.u64_at RSEGS M5 (os + 264) qc) by (apply TO5; [clear; lia| clear; lia| exact Z264]).
assert (C5272 : L5.u64_at RSEGS M5 (os + 272) 16384) by (apply TO5; [clear; lia| clear; lia| exact Z272]).
assert (C5280 : L5.u64_at RSEGS M5 (os + 280) qc) by (apply TO5; [clear; lia| clear; lia| exact Z280]).
assert (C5288 : L5.u64_at RSEGS M5 (os + 288) 0) by (apply TO5; [clear; lia| clear; lia| exact Z288]).
assert (KSB : forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%nat -> getr R5 (reg x) = getr R4 (reg x)).
{ intros x Hx. apply KS5. revert x Hx. apply (PMBSR1.sub_in PMBSRP2.KS_bsrM1ne). vm_compute. reflexivity. }
apply (FILLTHEN fx5 R5 M5 model5 LK2 Aw len1 BI5 Z1).
+ rewrite (KSB 2%nat) by inl. exact Y2.
+ rewrite (KSB 8%nat) by inl. exact Y8.
+ rewrite (KSB 9%nat) by inl. exact Y9.
+ exact Z10.
+ exact Z11.
+ exact Z12.
+ rewrite (KSB 18%nat) by inl. exact Y18.
+ rewrite (KSB 19%nat) by inl. exact Y19.
+ rewrite (KSB 20%nat) by inl. rewrite LR1. exact Y20.
+ rewrite (KSB 21%nat) by inl. exact Y21.
+ exact Z22.
+ rewrite (KSB 23%nat) by inl. exact Y23.
+ rewrite (KSB 25%nat) by inl. exact Y25.
+ rewrite (KSB 26%nat) by inl. exact Y26.
+ rewrite (KSB 27%nat) by inl. exact Y27.
+ rewrite (KSB 3%nat) by inl. exact Y3.
+ rewrite (KSB 4%nat) by inl. exact Y4.
+ apply T5X; [left; clear; lia| exact X8].
+ apply T5X; [left; clear; lia| exact X16].
+ apply T5X; [left; clear; lia| exact X24].
+ apply T5X; [left; clear; lia| exact X48].
+ apply T5X; [right; clear; lia| exact F32].
+ apply T5S; [clear; lia| exact SH4].
+ apply T5S; [clear; lia| exact SH8].
+ apply PARS; [exact EK5| exact DK5| exact C5264| exact C5272| exact C5280| exact C5288| clear; lia| clear; lia| clear; lia].
+ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 _ M4 M5 (EKO M4 M5 FR5) WSW FRB BRB ois str _ AOI); [exact SOWN| exact OUTIS| exact OUTBLK| exact IA4].
+ apply (PMBSK.base_keep L ar C LY LB FF sp 20480 _ M4 M5 (EKO M4 M5 FR5)); [| exact BASE4].
intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha O1. lia.
+ exact LR1.
+ rewrite LR1. exact LR2. }
assert (LX : forall (M3 : word -> option byte) a v, X <= a -> a + 8 <= X + 56 -> L5.u64_at RSEGS (mrestrict H2 M3) a v -> L5.u64_at RSEGS M3 a v).
{ intros M3 a v Ha Hb Y. apply (proj1 (L5A.u64_at_vis H2 M3 a v (VISs2 a 8 ltac:(clear - Ha SL176 SPT HX1; lia) ltac:(clear - Hb SHI SPT HX1; lia)) ltac:(clear - Ha Q0e; lia) ltac:(clear - Hb QX; lia))). exact Y. }
assert (LF : forall (M3 : word -> option byte) a v, F <= a -> a + 8 <= F + 128 -> L5.u64_at RSEGS (mrestrict H2 M3) a v -> L5.u64_at RSEGS M3 a v).
{ intros M3 a v Ha Hb Y. apply (proj1 (L5A.u64_at_vis H2 M3 a v (L5A.avis_sub H2 F 128 a 8 VF ltac:(clear - Ha; lia) ltac:(clear - Hb; lia)) ltac:(clear - Ha Q0c; lia) ltac:(clear - Hb QFR; lia))). exact Y. }
assert (LS : forall (M3 : word -> option byte) a v, F / 8 + 2147450880 <= a -> a + 1 <= F / 8 + 2147450880 + 16 -> L5.u8_at RSEGS (mrestrict H2 M3) a v -> L5.u8_at RSEGS M3 a v).
{ intros M3 a v Ha Hb Y. apply (proj1 (L5A.u8_at_vis H2 M3 a v (L5A.avis_sub H2 (F / 8 + SB) 16 a 1 VSH ltac:(unfold SB; clear - Ha; lia) ltac:(unfold SB; clear - Hb; lia)) ltac:(clear - Ha DF1; lia) ltac:(clear - Hb DF2; lia))). exact Y. }
assert (LO : forall (M3 : word -> option byte) a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS (mrestrict H2 M3) a v -> L5.u64_at RSEGS M3 a v).
{ intros M3 a v Ha Hb Y. apply (proj1 (L5A.u64_at_vis H2 M3 a v ltac:(apply OAV2; clear - Ha Hb; lia) ltac:(clear - Ha O1; lia) ltac:(clear - Hb O1; lia))). exact Y. }
assert (AFTER1 : forall (R3 : bvmap 5 word) (M3 : word -> option byte) (fx4 : FPState) R4 M4 model4 (len1 : Z),
PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M4 model4 LK2 cr Aw ->
L5CA.ahpres L ar ([] ++ LB) FF' X 2560 [(p, len1)] M3 M4 -> regs_preserved R3 R4 -> 1 <= len1 <= k ->
getr R3 (reg 2) = Z_to_bv 64 X -> getr R3 (reg 8) = Z_to_bv 64 sp -> getr R3 (reg 9) = Z_to_bv 64 X ->
getr R3 (reg 18) = Z_to_bv 64 (((os + 288) / 8) + 2147450880) -> getr R3 (reg 19) = Z_to_bv 64 os -> getr R3 (reg 20) = Z_to_bv 64 len1 ->
getr R3 (reg 21) = Z_to_bv 64 (((os + 280) / 8) + 2147450880) -> getr R3 (reg 22) = Z_to_bv 64 k -> getr R3 (reg 23) = Z_to_bv 64 (os + 288) ->
getr R3 (reg 24) = Z_to_bv 64 (os + 280) ->
getr R3 (reg 25) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R3 (reg 26) = Z_to_bv 64 F -> getr R3 (reg 27) = Z_to_bv 64 2147450880 ->
getr R3 (reg 3) = getr R (reg 3) -> getr R3 (reg 4) = getr R (reg 4) ->
L5.u64_at RSEGS M3 (X + 8) (F + 32) -> L5.u64_at RSEGS M3 (X + 16) F -> L5.u64_at RSEGS M3 (X + 24) p -> L5.u64_at RSEGS M3 (X + 48) F ->
L5.u64_at RSEGS M3 (F + 32) k -> L5.u8_at RSEGS M3 ((F / 8) + 2147450884) 0 -> L5.u8_at RSEGS M3 ((F / 8) + 2147450888) 248 ->
L5.u64_at RSEGS M3 (os + 264) qc -> L5.u64_at RSEGS M3 (os + 272) 16384 -> L5.u64_at RSEGS M3 (os + 280) de -> L5.u64_at RSEGS M3 (os + 288) rem ->
PM.iss_at RSEGS PMB.AD PMSPA.accA M3 ois str (PM.STRM g eg sst) -> PMSTA.base_okA RSEGS PMB.AD M3 ->
1 <= rem -> len1 = Z.min k rem ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx4 R4 722916 M4 model4) K).
{ intros R3 M3 fx4 R4 M4 model4 len1 BI4 HP4 RP4 Hl Y2 Y8 Y9 Y18 Y19 Y20 Y21 Y22 Y23 Y24 Y25 Y26 Y27 Y3 Y4 X8 X16 X24 X48 F32 SH4 SH8 C264 C272 C280 C288 IA3 BASE3 Hrm1 Hl1.
assert (R4c : forall j, In j L5SAR.cs_all -> getr R4 (reg j) = getr R3 (reg j)) by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
destruct (CKEEP M3 M4 2560 [(p, len1)] HP4 ltac:(clear; lia) ltac:(intros a Ha; apply (CKM a Ha); clear - Hl; lia)) as (K4a & K4b).
pose proof (L5SAR.ek_callee L ar LB [] FF [(F, 1, X + 32)] sp 20480 X 2560 [(p, len1)] [(p, len1)] M3 M4 HP4 ltac:(clear - HX1; lia) ltac:(clear - HX1; lia) (fun a _ Y => Y)) as EK34.
assert (WSP : PMKB.wapp [(p, len1)]).
{ apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - DSH Hl; Lia.lia| apply PMKB.wapp_nil]. }
assert (NDP : forall a, ~ (p <= a < p + k) -> ~ (p <= a < p + len1)) by (intros a N Y; apply N; clear - Y Hl; lia).
apply (M1C fx4 R4 M4 model4 len1 BI4).
- rewrite (R4c 2%nat) by inl. exact Y2.
- rewrite (R4c 8%nat) by inl. exact Y8.
- rewrite (R4c 9%nat) by inl. exact Y9.
- rewrite (R4c 18%nat) by inl. exact Y18.
- rewrite (R4c 19%nat) by inl. exact Y19.
- rewrite (R4c 20%nat) by inl. exact Y20.
- rewrite (R4c 21%nat) by inl. exact Y21.
- rewrite (R4c 22%nat) by inl. exact Y22.
- rewrite (R4c 23%nat) by inl. exact Y23.
- rewrite (R4c 24%nat) by inl. exact Y24.
- rewrite (R4c 25%nat) by inl. exact Y25.
- rewrite (R4c 26%nat) by inl. exact Y26.
- rewrite (R4c 27%nat) by inl. exact Y27.
- rewrite (R4c 3%nat) by inl. exact Y3.
- rewrite (R4c 4%nat) by inl. exact Y4.
- apply K4a; [left; clear; lia| exact X8].
- apply K4a; [left; clear; lia| exact X16].
- apply K4a; [left; clear; lia| exact X24].
- apply K4a; [left; clear; lia| exact X48].
- apply K4a; [right; clear; lia| exact F32].
- apply K4b; [clear; lia| exact SH4].
- apply K4b; [clear; lia| exact SH8].
- apply (OKEEP M3 M4 p len1 HP4 ltac:(clear; lia) ltac:(clear - Hl; lia)); [clear; lia| clear; lia| exact C264].
- apply (OKEEP M3 M4 p len1 HP4 ltac:(clear; lia) ltac:(clear - Hl; lia)); [clear; lia| clear; lia| exact C272].
- apply (OKEEP M3 M4 p len1 HP4 ltac:(clear; lia) ltac:(clear - Hl; lia)); [clear; lia| clear; lia| exact C280].
- apply (OKEEP M3 M4 p len1 HP4 ltac:(clear; lia) ltac:(clear - Hl; lia)); [clear; lia| clear; lia| exact C288].
- apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 _ M3 M4 EK34 WSP FRB BRB ois str _ AOI SOWN); [| |exact IA3].
+ intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX i Y) as (_ & Dx2 & _). apply Dx2. exact Hi.
+ intros c1 n1 q1 E i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX i Y) as (_ & _ & _ & _ & _ & _ & _ & Dx8 & _). apply (Dx8 c1 n1 q1 E). exact Hi.
- apply (PMBSK.base_keep L ar C LY LB FF sp 20480 _ M3 M4 EK34); [| exact BASE3].
intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX a Y) as (_ & _ & _ & _ & _ & _ & _ & _ & Dx9). apply Dx9. exact Ha.
- exact Hrm1.
- exact Hl1. }
assert (QDE : 4096 <= de <= 140737488338944) by (clear - G1 G2 G3 Q0 Q4 SL176 SHI SPT; lia).
destruct (Z_le_gt_dec 1 rem) as [REM1|REM0].
{
destruct (Z_le_gt_dec rem k) as [RK|RK].
-
cfeed P (PMBSRP1.bsrB1ge_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBSRP1.aligned; assumption | clear - REM1 RK Hk QDE QPR G1 G2 G3 Q0a Q0b Q0c Q0d Q0e Q0f; lia]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T12 & _ & _ & _ & _ & T18 & T20 & T21 & T23 & T24 & T25 & T26 & SX8 & SX16 & SX48 & SF32
& _ & _ & _ & SH8 & _ & _ & _ & _ & _ & _ & _ & SH4 & _ & _ & _ & SX24 & Sb264 & Sb272 & SbD256 & Sb280 & Sb288 & _).
apply (BRUN fx3 R3 M3v 0x7760c de rem MS3 MG3); [intros i Hi N; apply FRZ3; [exact Hi|..]; intros Y; apply N; unfold W3; clear - Y; lia
| exact Sb264| exact Sb272| exact Sb280| exact Sb288| exact G1| exact G2| exact G3|].
intros M3 model3 BI3 VIS3 MGM3 FR3 PA3 IA3 BASE3.
rewrite <- VIS3 in SX8, SX16, SX48, SX24, SF32, SH8, SH4, Sb264, Sb272, Sb280, Sb288.
apply (MEMCALL fx3 R3 M3 model3 LK2 Aw 722916 p de rem BI3 T1).
{ split; [clear; lia| reflexivity]. }
{ rewrite (KS3 2%nat) by inl. exact B2R. }
{ rewrite (KS3 4%nat) by inl. apply B34. right; left; reflexivity. }
{ exact T10. } { exact T11. } { exact T12. }
{ clear; lia. } { clear - RK; lia. } { clear - REM1; lia. } { exact G1. } { exact G3. }
intros fx4 R4 M4 model4 RP4 DEF4 BI4 HP4.
apply (AFTER1 R3 M3 fx4 R4 M4 model4 rem BI4 HP4 RP4 ltac:(clear - REM1 RK; lia)).
+ rewrite (KS3 2%nat) by inl. exact B2R.
+ rewrite (KS3 8%nat) by inl. exact B8R.
+ rewrite (KS3 9%nat) by inl. exact B9R.
+ exact T18.
+ rewrite (KS3 19%nat) by inl. exact B19R.
+ exact T20.
+ exact T21.
+ rewrite (KS3 22%nat) by inl. exact B22R.
+ exact T23.
+ exact T24.
+ exact T25.
+ exact T26.
+ rewrite (KS3 27%nat) by inl. exact B27R.
+ rewrite (KS3 3%nat) by inl. apply B34. left; reflexivity.
+ rewrite (KS3 4%nat) by inl. apply B34. right; left; reflexivity.
+ apply LX; [clear; lia| clear; lia| exact SX8].
+ apply LX; [clear; lia| clear; lia| exact SX16].
+ apply LX; [clear; lia| clear; lia| exact SX24].
+ apply LX; [clear; lia| clear; lia| exact SX48].
+ apply LF; [clear; lia| clear; lia| exact SF32].
+ apply LS; [clear; lia| clear; lia| exact SH4].
+ apply LS; [clear; lia| clear; lia| exact SH8].
+ apply LO; [clear; lia| clear; lia| exact Sb264].
+ apply LO; [clear; lia| clear; lia| exact Sb272].
+ apply LO; [clear; lia| clear; lia| exact Sb280].
+ apply LO; [clear; lia| clear; lia| exact Sb288].
+ exact IA3.
+ exact BASE3.
+ exact REM1.
+ clear - RK. destruct (Z.min_spec k rem) as [[Z1 Z2]|[Z1 Z2]]; lia.
-
cfeed P (PMBSRP1.bsrB1lt_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBSRP1.aligned; assumption | clear - REM1 RK Hk QDE QPR G1 G2 G3 Q0a Q0b Q0c Q0d Q0e Q0f; lia]).
destruct P as (fx3a & R3a & M3a & MG3a & _ & FRZ3a & MS3a & KS3a & T10a & T11a & T12a & _ & _ & _ & _ & T18a & T23a & T25a & T26a & SX8 & SX16 & SX48 & SF32
& _ & _ & _ & SH8 & _ & _ & _ & _ & _ & _ & _ & SH4 & _ & _ & _ & SX24 & Sb264 & Sb272 & Sbd256 & Sb280 & Sb288 & _).
assert (FZ3a : forall i, 0 <= i < 2 ^ 64 -> ~ W3 i -> M3a (Z_to_bv 64 i) = MV2 (Z_to_bv 64 i)).
{ intros i Hi N. apply FRZ3a; [exact Hi|..]; intros Y; apply N; unfold W3; clear - Y; lia. }
pose proof (TRANS MV2 M3a W3 FZ3a) as TR3.
assert (T3img : L5.img_clear M3a 65536 1269760).
{ intros i Hi. rewrite (TR3 65536 1204224 ltac:(clear; lia) ltac:(clear; lia)) by (first [clear - Hi; lia | intros j Hj; unfold W3; clear - Hj DF1 DF2 QX QFR O1; lia]). apply W0; exact Hi. }
assert (T3sb : L5.u64_at RSEGS M3a 1296952 2147450880).
{ apply (L5C.u64_at_agree RSEGS MV2 M3a); [intros i Hi; apply (TR3 1296952 8); [clear; lia| clear; lia| intros j Hj; unfold W3; clear - Hj DF1 DF2 QX QFR O1; lia| exact Hi]| clear; lia| clear; lia| exact W1]. }
assert (T3uar : L5.u32_at RSEGS M3a 1296960 1).
{ apply (PMF.u32_at_agree RSEGS MV2 M3a); [intros i Hi; apply (TR3 1296960 4); [clear; lia| clear; lia| intros j Hj; unfold W3; clear - Hj DF1 DF2 QX QFR O1; lia| exact Hi]| clear; lia| clear; lia| exact W2]. }
assert (T3oz : L5KA.zeros_at M3a (((os + 8) / 8) + 2147450880) 36).
{ apply (L5KA.zeros_at_agree1 MV2 M3a); [| exact OZ2]. intros i Hi. apply (TR3 (((os + 8) / 8) + 2147450880) 36); [| | | exact Hi].
- pose proof (Z.div_pos (os + 8) 8 ltac:(clear - O1; lia) ltac:(clear; lia)) as Hq. clear - Hq; lia.
- assert (Hq : (os + 8) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; clear - O1; lia). clear - Hq; lia.
- intros j Hj. assert (E8 : (os + 8) / 8 = os / 8 + 1) by (rewrite <- (Z.div_add os 1 8) by lia; f_equal; lia). rewrite E8 in Hj.
assert (D3 : os / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; clear - O1; lia).
assert (D4 : 0 <= os / 8) by (apply Z.div_pos; clear - O1; lia).
unfold W3. destruct QoSF as [Ya1|Ya1]; destruct GFBIG as [Ya2|Ya2]; destruct OBIG as [Ya3|Ya3]; clear - Hj Ya1 Ya2 Ya3 D3 D4 QX QFR O1 DF1 DF2; lia. }
assert (T3fl : L5.u64_at RSEGS M3a (F + 120) fl).
{ apply (L5C.u64_at_agree RSEGS MV2 M3a); [intros i Hi; apply (TR3 (F + 120) 8); [clear - QFR; lia| clear - QFR; lia| intros j Hj; unfold W3; destruct GFBIG as [Ya2|Ya2]; clear - Hj Ya2 DF1 DF2 QX QFR QXF QoF; lia| exact Hi]| clear - QFR; lia| clear - QFR; lia| exact FLCv]. }
assert (T3z32 : L5KA.zeros_at M3a (((F + 32) / 8) + 2147450880) 1).
{ replace ((F + 32) / 8) with (F / 8 + 4) by (rewrite <- (Z.div_add F 4 8) by lia; f_equal; lia).
intros i Hi. replace i with 0 by (clear - Hi; lia). rewrite Z.add_0_r. replace (F / 8 + 4 + 2147450880) with ((F / 8) + 2147450884) by (clear; lia).
apply (L5ADHR.byte_of_u8 M3a _ 0 SH4); [right| ]; clear - DF1 DF2; lia. }
assert (T3wX : L5.writable RSEGS M3a X 56) by exact (L5.writable_grows RSEGS MV2 M3a X 56 MG3a WX2).
assert (T3wo : L5.writable RSEGS M3a os 296) by exact (L5.writable_grows RSEGS MV2 M3a os 296 MG3a OW2).
assert (T3dF : L5.defined M3a F 128) by exact (L5.defined_grows MV2 M3a F 128 MG3a FDEF).
assert (T3wF : L5.writable RSEGS M3a F 128) by exact (L5.writable_grows RSEGS MV2 M3a F 128 MG3a FW).
assert (T3wS : L5.writable RSEGS M3a ((F / 8) + 2147450880) 16) by exact (L5.writable_grows RSEGS MV2 M3a _ 16 MG3a FSHW).
assert (T3wl : L5.writable RSEGS M3a fl 1) by exact (L5.writable_grows RSEGS MV2 M3a fl 1 MG3a FLW).
assert (Ya : forall x, In x [2; 3; 4; 8; 9; 19; 22; 27]%nat -> getr R3a (reg x) = getr R2 (reg x)).
{ intros x Hx. apply KS3a. revert x Hx. apply (PMBSR1.sub_in PMBSRP1.KS_bsrB1lt). vm_compute. reflexivity. }
assert (Y2a : getr R3a (reg 2) = Z_to_bv 64 X) by (rewrite (Ya 2%nat) by inl; exact B2R).
assert (Y8a : getr R3a (reg 8) = Z_to_bv 64 sp) by (rewrite (Ya 8%nat) by inl; exact B8R).
assert (Y9a : getr R3a (reg 9) = Z_to_bv 64 X) by (rewrite (Ya 9%nat) by inl; exact B9R).
assert (Y19a : getr R3a (reg 19) = Z_to_bv 64 os) by (rewrite (Ya 19%nat) by inl; exact B19R).
assert (Y22a : getr R3a (reg 22) = Z_to_bv 64 k) by (rewrite (Ya 22%nat) by inl; exact B22R).
assert (Y27a : getr R3a (reg 27) = Z_to_bv 64 2147450880) by (rewrite (Ya 27%nat) by inl; exact B27R).
cfeed P (PMBSRP1.bsrB1lt2_conc fx3a R3a M3a (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBSRP1.aligned; assumption | clear - REM1 RK Hk QDE QPR G1 G2 G3 Q0a Q0b Q0c Q0d Q0e Q0f; lia]).
destruct P as (fx3 & R3 & M3v & MG3b & _ & FRZ3b & MS3b & KS3b & T1 & T10 & T11 & T12 & T20 & T21 & T24 & Sc264 & Sc272 & Scd256 & Sc280 & Sc288).
assert (FZ3b : forall i, 0 <= i < 2 ^ 64 -> ~ (os + 256 <= i < os + 296) -> M3v (Z_to_bv 64 i) = M3a (Z_to_bv 64 i)).
{ intros i Hi N. apply FRZ3b; [exact Hi| intros Y; apply N; clear - Y; lia]. }
assert (TB : forall a v, (X <= a /\ a + 8 <= X + 56 \/ F <= a /\ a + 8 <= F + 128) -> L5.u64_at RSEGS M3a a v -> L5.u64_at RSEGS M3v a v).
{ intros a v Ha Y. apply (L5C.u64_at_agree RSEGS M3a M3v); [intros i Hi; apply FZ3b; [clear - Ha Hi QX QFR; lia| clear - Ha Hi QXo QoF; lia]| clear - Ha Q0e Q0c; lia| clear - Ha QX QFR; lia| exact Y]. }
assert (TBs : forall a v, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16 -> L5.u8_at RSEGS M3a a v -> L5.u8_at RSEGS M3v a v).
{ intros a v Ha Y. apply (L5C.u8_at_agree RSEGS M3a M3v); [intros i Hi; apply FZ3b; [clear - Ha Hi DF1 DF2; lia| destruct OBIG as [Yo|Yo]; clear - Ha Hi Yo DF1 DF2; lia]| clear - Ha DF1; lia| clear - Ha DF2; lia| exact Y]. }
assert (KSb : forall x, In x [2; 3; 4; 8; 9; 18; 19; 22; 23; 25; 26; 27]%nat -> getr R3 (reg x) = getr R3a (reg x)).
{ intros x Hx. apply KS3b. revert x Hx. apply (PMBSR1.sub_in PMBSRP1.KS_bsrB1lt2). vm_compute. reflexivity. }
apply (BRUN fx3 R3 M3v 0x7760c de rem (msteps_trans _ _ _ _ MS3a MS3b) (fun x Hx => MG3b x (MG3a x Hx))).
{ intros i Hi N. rewrite FZ3b; [apply FZ3a; [exact Hi| exact N]| exact Hi| intros Y; apply N; unfold W3; clear - Y; lia]. }
{ exact Sc264. } { exact Sc272. } { exact Sc280. } { exact Sc288. } { exact G1. } { exact G2. } { exact G3. }
intros M3 model3 BI3 VIS3 MGM3 FR3 PA3 IA3 BASE3.
apply (MEMCALL fx3 R3 M3 model3 LK2 Aw 722916 p de k BI3 T1).
{ split; [clear; lia| reflexivity]. }
{ rewrite (KSb 2%nat) by inl. exact Y2a. }
{ rewrite (KSb 4%nat) by inl. rewrite (Ya 4%nat) by inl. apply B34. right; left; reflexivity. }
{ exact T10. } { exact T11. } { exact T12. }
{ clear; lia. } { clear; lia. } { clear - Hk; lia. } { exact G1. } { clear - G3 RK; lia. }
intros fx4 R4 M4 model4 RP4 DEF4 BI4 HP4.
apply (AFTER1 R3 M3 fx4 R4 M4 model4 k BI4 HP4 RP4 ltac:(clear - Hk; lia)).
+ rewrite (KSb 2%nat) by inl. exact Y2a.
+ rewrite (KSb 8%nat) by inl. exact Y8a.
+ rewrite (KSb 9%nat) by inl. exact Y9a.
+ rewrite (KSb 18%nat) by inl. exact T18a.
+ rewrite (KSb 19%nat) by inl. exact Y19a.
+ exact T20.
+ exact T21.
+ rewrite (KSb 22%nat) by inl. exact Y22a.
+ rewrite (KSb 23%nat) by inl. exact T23a.
+ exact T24.
+ rewrite (KSb 25%nat) by inl. exact T25a.
+ rewrite (KSb 26%nat) by inl. exact T26a.
+ rewrite (KSb 27%nat) by inl. exact Y27a.
+ rewrite (KSb 3%nat) by inl. rewrite (Ya 3%nat) by inl. apply B34. left; reflexivity.
+ rewrite (KSb 4%nat) by inl. rewrite (Ya 4%nat) by inl. apply B34. right; left; reflexivity.
+ apply LX; [clear; lia| clear; lia| rewrite VIS3; apply TB; [left; clear; lia| exact SX8]].
+ apply LX; [clear; lia| clear; lia| rewrite VIS3; apply TB; [left; clear; lia| exact SX16]].
+ apply LX; [clear; lia| clear; lia| rewrite VIS3; apply TB; [left; clear; lia| exact SX24]].
+ apply LX; [clear; lia| clear; lia| rewrite VIS3; apply TB; [left; clear; lia| exact SX48]].
+ apply LF; [clear; lia| clear; lia| rewrite VIS3; apply TB; [right; clear; lia| exact SF32]].
+ apply LS; [clear; lia| clear; lia| rewrite VIS3; apply TBs; [clear; lia| exact SH4]].
+ apply LS; [clear; lia| clear; lia| rewrite VIS3; apply TBs; [clear; lia| exact SH8]].
+ apply LO; [clear; lia| clear; lia| rewrite VIS3; exact Sc264].
+ apply LO; [clear; lia| clear; lia| rewrite VIS3; exact Sc272].
+ apply LO; [clear; lia| clear; lia| rewrite VIS3; exact Sc280].
+ apply LO; [clear; lia| clear; lia| rewrite VIS3; exact Sc288].
+ exact IA3.
+ exact BASE3.
+ exact REM1.
+ clear - RK. destruct (Z.min_spec k rem) as [[Z1 Z2]|[Z1 Z2]]; lia. }
assert (REMZ : rem = 0) by (clear - REM0 G2; lia).
subst rem.
destruct (Z.eq_dec k 16384) as [KF|KNF].
2:{
cfeed P (PMBSRP1.bsrB0f_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBSRP1.aligned; assumption | clear - KNF Hk QDE QPR G1 G2 G3 Q0a Q0b Q0c Q0d Q0e Q0f; lia]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T12 & _ & _ & _ & _ & T18 & T20 & T21 & T22 & T23 & T25 & T26 & Sb280 & SX8 & SX16 & SX48 & SF32
& _ & _ & _ & SH8 & _ & _ & _ & _ & _ & _ & _ & SH4 & _ & _ & _ & SX24 & Sb264 & Sb272 & Sbd256 & Sb288 & _).
apply (BRUN fx3 R3 M3v 0xb0e58 qc 0 MS3 MG3); [intros i Hi N; apply FRZ3; [exact Hi|..]; intros Y; apply N; unfold W3; clear - Y; lia
| exact Sb264| exact Sb272| exact Sb280| exact Sb288| clear; lia| clear; lia| clear; lia|].
intros M3 model3 BI3 VIS3 MGM3 FR3 PA3 IA3 BASE3.
rewrite <- VIS3 in SX8, SX16, SX48, SX24, SF32, SH8, SH4.
apply (FILLTHEN fx3 R3 M3 model3 LK2 Aw 0 BI3 T1).
+ rewrite (KS3 2%nat) by inl. exact B2R.
+ rewrite (KS3 8%nat) by inl. exact B8R.
+ rewrite (KS3 9%nat) by inl. exact B9R.
+ exact T10.
+ exact T11.
+ exact T12.
+ exact T18.
+ rewrite (KS3 19%nat) by inl. exact B19R.
+ exact T20.
+ exact T21.
+ exact T22.
+ exact T23.
+ exact T25.
+ exact T26.
+ rewrite (KS3 27%nat) by inl. exact B27R.
+ rewrite (KS3 3%nat) by inl. apply B34. left; reflexivity.
+ rewrite (KS3 4%nat) by inl. apply B34. right; left; reflexivity.
+ apply LX; [clear; lia| clear; lia| exact SX8].
+ apply LX; [clear; lia| clear; lia| exact SX16].
+ apply LX; [clear; lia| clear; lia| exact SX24].
+ apply LX; [clear; lia| clear; lia| exact SX48].
+ apply LF; [clear; lia| clear; lia| exact SF32].
+ apply LS; [clear; lia| clear; lia| exact SH4].
+ apply LS; [clear; lia| clear; lia| exact SH8].
+ exact PA3.
+ exact IA3.
+ exact BASE3.
+ reflexivity.
+ clear - Hk; lia. }
subst k.
pose proof (PMBSK.iss_vis L ar C HI LY HIok LB FF' LK2 cr Aw M2 model2 fb str _ sp 20480 HH2 FOK' IA2 ASTK2) as ((_ & _ & _) & IZ2 & IW2 & _ & IAV2 & _ & IOS2).
fold ois MV2 in IZ2, IW2, IAV2, IOS2.
pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY LB FF' LK2 cr Aw M2 model2 0x131ff8 1 HH2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT1.
pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY LB FF' LK2 cr Aw M2 model2 0x131f60 1 HH2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT2.
cbn in VT1, VT2. fold MV2 in VT1, VT2.
pose proof IA2 as (H0j & _ & _ & H16j & _ & _ & _ & _ & _ & _ & _ & _ & IOSBj & _ & _).
destruct IOSBj as (I0j & I32j & I36j & I40j & _ & _ & _ & _ & _).
cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMB.AD ADDR_B] in H0j, H16j, I0j, I32j, I36j, I40j.
replace (ois + 120 + 32) with (ois + 152) in I32j by lia. replace (ois + 120 + 36) with (ois + 156) in I36j by lia.
replace (ois + 120 + 40) with (ois + 160) in I40j by lia.
assert (VH0 : L5.u64_at RSEGS MV2 ois 1253392) by (apply (proj2 (L5A.u64_at_vis _ M2 ois _ ltac:(apply IAV2; lia) ltac:(lia) ltac:(lia))); exact H0j).
assert (VH16 : L5.u64_at RSEGS MV2 (ois + 16) 1253152) by (apply (proj2 (L5A.u64_at_vis _ M2 (ois + 16) _ ltac:(apply IAV2; lia) ltac:(lia) ltac:(lia))); exact H16j).
assert (VI32 : L5.u32_at RSEGS MV2 (ois + 152) sst) by (apply (proj2 (L5A.u32_at_vis _ M2 (ois + 152) _ ltac:(apply IAV2; lia) ltac:(lia) ltac:(lia))); exact I32j).
assert (VI36 : L5.u32_at RSEGS MV2 (ois + 156) 0) by (apply (proj2 (L5A.u32_at_vis _ M2 (ois + 156) _ ltac:(apply IAV2; lia) ltac:(lia) ltac:(lia))); exact I36j).
assert (VI40 : L5.u64_at RSEGS MV2 (ois + 160) (ois + 16)) by (apply (proj2 (L5A.u64_at_vis _ M2 (ois + 160) _ ltac:(apply IAV2; lia) ltac:(lia) ltac:(lia))); exact I40j).
pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PSRC2' & _). destruct PSRC2' as (S240b & S248b & _).
cbn [PM.p_src s0 PM.sr_qc] in S240b, S248b. fold os in S240b, S248b.
assert (VS240 : L5.u64_at RSEGS MV2 (os + 240) ois) by (apply (proj2 (L5A.u64_at_vis _ M2 (os + 240) _ ltac:(apply OAV2; lia) ltac:(lia) ltac:(lia))); exact S240b).
assert (VS248 : L5.u64_at RSEGS MV2 (os + 248) (ois + 16)) by (apply (proj2 (L5A.u64_at_vis _ M2 (os + 248) _ ltac:(apply OAV2; lia) ltac:(lia) ltac:(lia))); exact S248b).
destruct (APART ois 272 0 0 ltac:(intros i Hi; destruct AOI as (f & Hf & Z1 & Z2); unfold aclient, aclient_g; do 3 right; left; exists f; split; [exact Hf| clear - Z1 Z2 Hi; lia]) ltac:(clear; lia)) as (AiF & AiSF & AiFL).
assert (CLshi : forall i, 0 <= i < 34 -> aclient L ar ([] ++ LB) FF 0 0 (ois / 8 + SB + i)).
{ intros i Hi. destruct AOI as (f & Hf & X1 & X2). unfold aclient, aclient_g. do 5 right; left. exists f. split; [exact Hf|].
unfold in_shadow_of, S.
assert (D1 : ff_addr f / 8 <= ois / 8) by (apply Z.div_le_mono; clear - X1; lia).
assert (D2 : (ois + i * 8) / 8 = ois / 8 + i) by (apply Z.div_add; clear; lia).
assert (D3 : (ois + i * 8) / 8 <= (ff_addr f + ff_bytes (ff_class f) - 1) / 8) by (apply Z.div_le_mono; clear - X2 Hi; lia).
clear - D1 D2 D3 Hi. lia. }
destruct (APART (ois / 8 + SB) 34 0 0 CLshi ltac:(clear; lia)) as (_ & AsiSF & _). unfold SB in AsiSF, AiSF.
assert (QiF : ((F / 8) + 2147450880) + 16 <= ((ois / 8) + 2147450880) \/ ((ois / 8) + 2147450880) + 34 <= ((F / 8) + 2147450880)) by (clear - AsiSF; lia).
assert (QT1 : ((F / 8) + 2147450880) + 16 <= 2147607551 \/ 2147607551 + 1 <= ((F / 8) + 2147450880)) by (clear - DF1 QFR; lia).
assert (QT2 : ((F / 8) + 2147450880) + 16 <= 2147607532 \/ 2147607532 + 1 <= ((F / 8) + 2147450880)) by (clear - DF1 QFR; lia).
assert (QXi : X + 56 <= ois \/ ois + 272 <= X) by (clear - ICE SL176 HX1; lia).
assert (Qoi : os + 296 <= ois \/ ois + 272 <= os) by (right; exact IOS2).
destruct IST as [ST0|ST2].
2:{
subst sst.
cfeed P (PMBSRP1.bsrB0e_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 45%nat => ois
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBSRP1.aligned; assumption | clear - QDE QPR I1 G1 G2 G3 Q0a Q0b Q0c Q0d Q0e Q0f; lia]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & T10 & _ & _ & _ & _ & _ & _ & _ & _ & T22 & _ & _ & T25 & T26 & Sb288 & SX8 & SX16 & SX48 & SF32
& _ & _ & _ & SH8 & _ & _ & _ & _ & _ & _ & _ & SH4 & _ & _ & _ & SX24 & Sb264 & Sb272 & Sbd256 & Sb280 & _).
apply (BRUN fx3 R3 M3v 0xb0b3c de 0 MS3 MG3); [intros i Hi N; apply FRZ3; [exact Hi|..]; intros Y; apply N; unfold W3; clear - Y; lia
| exact Sb264| exact Sb272| exact Sb280| exact Sb288| exact G1| clear; lia| clear - G3; lia|].
intros M3 model3 BI3 VIS3 MGM3 FR3 PA3 IA3 BASE3.
rewrite <- VIS3 in SX16, Sb264, Sb272, Sb280, Sb288.
apply (EXITP fx3 R3 M3 model3 LK2 Aw de 0 g 2 0 BI3).
+ rewrite (KS3 2%nat) by inl. exact B2R.
+ rewrite (KS3 8%nat) by inl. exact B8R.
+ rewrite (KS3 9%nat) by inl. exact B9R.
+ exact T22.
+ exact T25.
+ exact T26.
+ rewrite (KS3 3%nat) by inl. apply B34. left; reflexivity.
+ rewrite (KS3 4%nat) by inl. apply B34. right; left; reflexivity.
+ apply LX; [clear; lia| clear; lia| exact SX16].
+ apply LO; [clear; lia| clear; lia| exact Sb264].
+ apply LO; [clear; lia| clear; lia| exact Sb272].
+ apply LO; [clear; lia| clear; lia| exact Sb280].
+ apply LO; [clear; lia| clear; lia| exact Sb288].
+ exact G1.
+ clear; lia.
+ clear - G3; lia.
+ exact IA3.
+ clear - SZ; lia.
+ intros _; reflexivity.
+ clear; lia.
+ clear; lia.
+ intros Y; exfalso; clear - Y; lia.
+ intros _; split; reflexivity. }
subst sst.
destruct (D16K eq_refl) as (c0 & n0 & q0 & ETB & Dq1 & Dq2 & TIN).
assert (APG : p + 16384 <= g \/ eg <= p).
{ pose proof (PMBSK.iss_unread_whereA M ois str _ IA) as [(Y1 & Y2)|(c1 & n1 & q1 & E & Y1 & Y2)]; cbn [PM.sm_g PM.sm_eg] in *.
- destruct (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 ois 272 HH TIN AOI) as [Z1|Z1]; clear - Y1 Y2 Z1 Dq1 Dq2; Lia.lia.
- assert (SIN : In (q1, c1) LBX) by (apply INCS; rewrite E; left; reflexivity).
assert (NS : q0 <> q1) by (apply (PMBSK.fst_neq_appA (PM.parser_own s0) LBX q0 c0 q1 c1); [exact ND| unfold s0, PM.parser_own, PM.vs_own; rewrite ETB; cbn; right; right; left; reflexivity| exact SIN]).
destruct (PMBSK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 q1 c1 HH TIN (SOWN _ ltac:(rewrite E; left; reflexivity)) NS) as [Z1|Z1]; clear - Y1 Y2 Z1 Dq1 Dq2; Lia.lia. }
cfeed P (PMBSRP1.bsrB0x_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 45%nat => ois
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBSRP1.aligned; assumption | clear - QDE QPR I1 G1 G2 G3 Q0a Q0b Q0c Q0d Q0e Q0f; lia]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T12 & _ & _ & _ & _ & T18 & T20 & T22 & T23 & T24 & T25 & T26 & SX8 & SX16 & SX48 & SF32
& _ & _ & _ & SH8 & _ & _ & _ & _ & _ & _ & _ & SH4 & _ & _ & _ & SX24 & Sb264 & Sb272 & Sbd256 & Sb280 & Sb288 & _).
apply (BRUN fx3 R3 M3v 0xd76e4 de 0 MS3 MG3); [intros i Hi N; apply FRZ3; [exact Hi|..]; intros Y; apply N; unfold W3; clear - Y; lia
| exact Sb264| exact Sb272| exact Sb280| exact Sb288| exact G1| clear; lia| clear - G3; lia|].
intros M3 model3 BI3 VIS3 MGM3 FR3 PA3 IA3 BASE3.
rewrite <- VIS3 in SX8, SX16, SX48, SX24, SF32, SH8, SH4, Sb264, Sb272, Sb280, Sb288.
pose proof BI3 as (HH3 & AM3 & MRT3 & INCA3 & INCL3 & ASTK3 & EK3 & DK3 & OWN3 & SHD3).
assert (STK3 : shadow_zero M3 (X - 16384) (16384 / 8)).
{ change (16384 / 8) with 2048.
assert (M8a : (sp - 20480) mod 8 = 0) by (apply PMKB.mod16_8'; replace (sp - 20480) with (sp + (-1280) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
assert (M8b : (X - 16384) mod 8 = 0) by (apply PMKB.mod16_8'; replace (X - 16384) with (X + (-1024) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact HX16).
apply (PMKB.stksh_keepA L ar LB FF sp 20480 WA M M3 EK3 WAPP (X - 16384) 2048); [clear - HX1 SL176 SPT; lia| clear - HX1 SLO; lia| clear - HX1 SHI SPT; lia| exact M8b| clear; lia|].
apply (PMKB.shadow_zero_sub M (sp - 20480) 2560); [exact M8a| exact M8b| clear - HX1; lia| clear - HX1; lia| clear; lia| exact STKSH]. }
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF3 & _).
unfold PMB.xsgetn_spec, PMSPA.xsgetn_spec in XS. cbn [pa_xsgetn PMB.AD ADDR_B] in XS.
apply (XS fx3 R3 M3 model3 K ([] ++ LB) FF' LK2 Aw cr X 723580 ois p str (PM.STRM g eg 0) HH3 AM3 K0).
{ split; [rewrite L5K.rl1; exact T1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; rewrite (KS3 2%nat) by inl; exact B2R|].
split; [rewrite L5K.rl3; rewrite (KS3 3%nat) by inl; rewrite (B34 3%nat) by (left; reflexivity); exact Rgp|].
split; [rewrite L5K.rl4; rewrite (KS3 4%nat) by inl; rewrite (B34 4%nat) by (right; left; reflexivity); exact Rtp|].
change (PMSPA.pm_scr 2) with 16384. split; [|exact STK3]. apply (STKX M3 ASTK3); clear; lia. }
{ apply (PMBUAR.ffroomA_push 4 2 FF LK LK2 _ FRM GLKI2); [exact NDF3| clear; lia]. }
{ apply (PMBUAR.ffrsA_push FF sp X F 1 (X + 32) FRS); clear - HX1; lia. }
{ rewrite L5K.rl10. exact T10. }
{ rewrite L5SAR.r11. exact T11. }
{ rewrite L5SAR.r12. exact T12. }
{ exact (PMBUAR.aobjA_push FF ois 272 _ AOI). }
{ exact I8. }
{ exact IA3. }
{ exact BASE3. }
{ exact SOWN. }
{ exists q0, c0. split; [exact TIN| unfold PM.CHUNK; split; [exact Dq1| exact Dq2]]. }
{ unfold PM.CHUNK. intros a Ha. apply (PMFA.accA_agree M M3 p 16384 (AGSHP M M3 WA EK3 WAPP) DAP a). exact Ha. }
{ cbn [PM.sm_g PM.sm_eg]. unfold PM.CHUNK. exact APG. }
intros fx4 R4 M4 model4 LK4 Aw4 c RP4 A10c Hc IA4 D4 HP4 MRT4 INC4 INCA4 AM4 HH4.
change (PMSPA.pm_scr 2) with 16384 in HP4. unfold PM.CHUNK in Hc, HP4. cbn [PM.sm_g PM.sm_eg PM.sm_st] in Hc, IA4. rewrite L5K.rl10 in A10c.
assert (C0 : 0 <= c <= 16384 /\ g + c <= eg).
{ rewrite Hc. clear - SZ. destruct (Z.min_spec 16384 (eg - g)) as [[X1 X2]|[X1 X2]]; rewrite X2; lia. }
set (WX := [(ois + 40, 8); (p, 16384)]) in *.
assert (OUTX : forall a, (X <= a < X + 56 \/ (F + 32 <= a < F + 120) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16) \/ os <= a < os + 296) -> L5.outside WX a).
{ intros a Ha r0 [<-|[<-|[]]] Y; unfold L5.in_rng in Y; cbn [fst snd] in Y.
- destruct Ha as [Z1|[Z1|[Z1|Z1]]]; [clear - Z1 Y ICE SL176 HX1; lia| clear - Z1 Y AiF; lia| clear - Z1 Y AiSF; lia| clear - Z1 Y Qoi; lia].
- destruct (DAV a Y) as (Z2 & Z3 & Z4 & Z5 & _). destruct Ha as [Z1|[Z1|[Z1|Z1]]]; [apply Z2; clear - Z1 HX1; lia| apply Z3; clear - Z1; lia| apply Z4; exact Z1| apply Z5; exact Z1]. }
assert (BI4 : PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WA [] M4 model4 LK4 cr Aw4).
{ apply (PMBUK.binv_callee L ar C HI HIok M model LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr [] G
WA WA [] [] [] M3 model3 LK2 cr Aw M4 model4 LK4 cr Aw4 16384 WX BI3 HP4 HH4 AM4 MRT4 INCA4 INC4); [clear; lia| clear - HX1; lia| | | intros a Y; exact Y].
- intros rr a Hin Hr. unfold PMBSU.ocell13. change (ff_bytes 1 / 8) with 16. destruct Hin as [<-|[<-|[]]]; unfold L5.in_rng in Hr; cbn [fst snd] in Hr.
+ split; [clear - Hr ICE SL176; lia| unfold SB; clear - Hr AiSF; lia].
+ destruct (DAV a Hr) as (Z2 & _ & Z4 & _). split; [intros Y; apply Z2; clear - Y HX1; lia| unfold SB; exact Z4].
- intros a _ O r0 [<-|[<-|[]]] Y.
+ apply (O (ois + 40, 8)); [unfold WA, PMSPA.W_src, PMSPA.W_srcf; cbn [PM.sr_qc app]; right; left; reflexivity| exact Y].
+ apply (O (p, 16384)); [unfold WA; apply in_or_app; right; left; reflexivity| exact Y]. }
assert (R4c : forall j, In j L5SAR.cs_all -> getr R4 (reg j) = getr R3 (reg j)) by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
destruct (CKEEP M3 M4 16384 WX HP4 ltac:(clear; lia) ltac:(intros a Ha; apply OUTX; destruct Ha as [Y|[Y|Y]]; [left; exact Y| right; left; exact Y| right; right; left; exact Y])) as (K4a & K4b).
assert (O4 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3 a v -> L5.u64_at RSEGS M4 a v).
{ intros a v Ha Hb Y. apply (L5C.u64_at_agree RSEGS M3 M4); [| clear - Ha O1; lia| clear - Hb O1; lia| exact Y].
intros i Hi. apply (proj1 HP4). split; [clear - Ha Hb Hi O1; lia|]. split; [|apply OUTX; right; right; right; clear - Ha Hb Hi; lia].
apply PMBSR1.cl_of_bf. right. destruct (PMBSR1.in_fframe_of_aobjA FF os 296 i AO ltac:(clear - Ha Hb Hi; lia)) as (f & Hf & Z1). exists f. split; [right; exact Hf| exact Z1]. }
pose proof (L5SAR.ek_callee L ar LB [] FF [(F, 1, X + 32)] sp 20480 X 16384 WX WX M3 M4 HP4 ltac:(clear - HX1; lia) ltac:(clear - HX1; lia) (fun a _ Y => Y)) as EK34.
pose proof BI4 as (_ & _ & _ & _ & _ & _ & EK4 & DK4 & _).
assert (U4264 : L5.u64_at RSEGS M4 (os + 264) qc) by (apply O4; [clear; lia| clear; lia| apply LO; [clear; lia| clear; lia| exact Sb264]]).
assert (U4272 : L5.u64_at RSEGS M4 (os + 272) 16384) by (apply O4; [clear; lia| clear; lia| apply LO; [clear; lia| clear; lia| exact Sb272]]).
assert (U4280 : L5.u64_at RSEGS M4 (os + 280) de) by (apply O4; [clear; lia| clear; lia| apply LO; [clear; lia| clear; lia| exact Sb280]]).
assert (U4288 : L5.u64_at RSEGS M4 (os + 288) 0) by (apply O4; [clear; lia| clear; lia| apply LO; [clear; lia| clear; lia| exact Sb288]]).
assert (PA4 : PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M4 op ois (PMSPA.with_src s0 (PM.SRC qc de 0)))
by (apply PARS; [exact EK4| exact DK4| exact U4264| exact U4272| exact U4280| exact U4288| exact G1| clear; lia| clear - G3; lia]).
assert (BASE4 : PMSTA.base_okA RSEGS PMB.AD M4).
{ apply (PMBSK.base_keep L ar C LY LB FF sp 20480 _ M3 M4 EK34); [| exact BASE3].
intros a Ha r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; [clear - Ha I1; lia|].
intros Y. destruct (DX a Y) as (_ & _ & _ & _ & _ & _ & _ & _ & Dx9). apply Dx9. exact Ha. }
destruct (STATEV M4 model4 LK4 Aw4 de 0 16384 BI4 PA4 BASE4) as ((U0 & U1 & U2) & (UX & UX24 & UX8 & UX16 & UX48) & (UOZ & UOW & U264 & U272 & UD256 & U280 & U288 & OAV4)
& (UFD & UFW & UFSW & UFL & UFLW & UF32 & US4 & US8)).
{ apply K4a; [left; clear; lia| apply LX; [clear; lia| clear; lia| exact SX8]]. }
{ apply K4a; [left; clear; lia| apply LX; [clear; lia| clear; lia| exact SX16]]. }
{ apply K4a; [left; clear; lia| apply LX; [clear; lia| clear; lia| exact SX24]]. }
{ apply K4a; [left; clear; lia| apply LX; [clear; lia| clear; lia| exact SX48]]. }
{ apply K4a; [right; clear; lia| apply LF; [clear; lia| clear; lia| exact SF32]]. }
{ apply K4b; [clear; lia| apply LS; [clear; lia| clear; lia| exact SH4]]. }
{ apply K4b; [clear; lia| apply LS; [clear; lia| clear; lia| exact SH8]]. }
set (MV4 := mrestrict (ahid Aw4 model4) M4) in *.
pose proof BI4 as (HH4' & _ & _ & _ & _ & ASTK4 & _).
pose proof (PMBSK.iss_vis L ar C HI LY HIok LB FF' LK4 cr Aw4 M4 model4 fb str _ sp 20480 HH4' FOK' IA4 ASTK4) as ((_ & _ & _) & IZ4 & IW4 & _ & IAV4 & _ & _).
fold ois MV4 in IZ4, IW4, IAV4.
pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY LB FF' LK4 cr Aw4 M4 model4 0x131ff8 1 HH4' ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT14.
pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY LB FF' LK4 cr Aw4 M4 model4 0x131f60 1 HH4' ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT24.
cbn in VT14, VT24. fold MV4 in VT14, VT24.
pose proof IA4 as (H0k & _ & _ & H16k & _ & _ & _ & _ & _ & _ & _ & _ & IOSBk & _ & _).
destruct IOSBk as (I0k & I32k & I36k & I40k & _ & _ & _ & _ & _).
cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMB.AD ADDR_B] in H0k, H16k, I0k, I32k, I36k, I40k.
replace (ois + 120 + 32) with (ois + 152) in I32k by lia. replace (ois + 120 + 36) with (ois + 156) in I36k by lia.
replace (ois + 120 + 40) with (ois + 160) in I40k by lia.
assert (VH0k : L5.u64_at RSEGS MV4 ois 1253392) by (apply (proj2 (L5A.u64_at_vis _ M4 ois _ ltac:(apply IAV4; lia) ltac:(lia) ltac:(lia))); exact H0k).
assert (VH16k : L5.u64_at RSEGS MV4 (ois + 16) 1253152) by (apply (proj2 (L5A.u64_at_vis _ M4 (ois + 16) _ ltac:(apply IAV4; lia) ltac:(lia) ltac:(lia))); exact H16k).
assert (VI32k : L5.u32_at RSEGS MV4 (ois + 152) 0) by (apply (proj2 (L5A.u32_at_vis _ M4 (ois + 152) _ ltac:(apply IAV4; lia) ltac:(lia) ltac:(lia))); exact I32k).
assert (VI36k : L5.u32_at RSEGS MV4 (ois + 156) 0) by (apply (proj2 (L5A.u32_at_vis _ M4 (ois + 156) _ ltac:(apply IAV4; lia) ltac:(lia) ltac:(lia))); exact I36k).
assert (VI40k : L5.u64_at RSEGS MV4 (ois + 160) (ois + 16)) by (apply (proj2 (L5A.u64_at_vis _ M4 (ois + 160) _ ltac:(apply IAV4; lia) ltac:(lia) ltac:(lia))); exact I40k).
pose proof PA4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PSRC4 & _). destruct PSRC4 as (S240k & S248k & _).
cbn [PM.p_src PMSPA.with_src s0 PM.sr_qc] in S240k, S248k. fold os in S240k, S248k.
assert (VS240k : L5.u64_at RSEGS MV4 (os + 240) ois) by (apply (proj2 (L5A.u64_at_vis _ M4 (os + 240) _ ltac:(apply OAV4; lia) ltac:(lia) ltac:(lia))); exact S240k).
assert (VS248k : L5.u64_at RSEGS MV4 (os + 248) (ois + 16)) by (apply (proj2 (L5A.u64_at_vis _ M4 (os + 248) _ ltac:(apply OAV4; lia) ltac:(lia) ltac:(lia))); exact S248k).
assert (R43 : forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg x) = getr R3 (reg x)).
{ intros x Hx. apply R4c. revert x Hx. apply (PMBSR1.sub_in L5SAR.cs_all). vm_compute. reflexivity. }
assert (Z2 : getr R4 (reg 2) = Z_to_bv 64 X) by (rewrite (R43 2%nat) by inl; rewrite (KS3 2%nat) by inl; exact B2R).
assert (Z8 : getr R4 (reg 8) = Z_to_bv 64 sp) by (rewrite (R43 8%nat) by inl; rewrite (KS3 8%nat) by inl; exact B8R).
assert (Z9 : getr R4 (reg 9) = Z_to_bv 64 X) by (rewrite (R43 9%nat) by inl; rewrite (KS3 9%nat) by inl; exact B9R).
assert (Z19 : getr R4 (reg 19) = Z_to_bv 64 os) by (rewrite (R43 19%nat) by inl; rewrite (KS3 19%nat) by inl; exact B19R).
assert (Z27 : getr R4 (reg 27) = Z_to_bv 64 2147450880) by (rewrite (R43 27%nat) by inl; rewrite (KS3 27%nat) by inl; exact B27R).
assert (Z3 : getr R4 (reg 3) = getr R (reg 3)) by (rewrite (R43 3%nat) by inl; rewrite (KS3 3%nat) by inl; apply B34; left; reflexivity).
assert (Z4 : getr R4 (reg 4) = getr R (reg 4)) by (rewrite (R43 4%nat) by inl; rewrite (KS3 4%nat) by inl; apply B34; right; left; reflexivity).
rewrite <- (R43 18%nat) in T18 by inl. rewrite <- (R43 20%nat) in T20 by inl. rewrite <- (R43 22%nat) in T22 by inl. rewrite <- (R43 23%nat) in T23 by inl.
rewrite <- (R43 24%nat) in T24 by inl. rewrite <- (R43 25%nat) in T25 by inl. rewrite <- (R43 26%nat) in T26 by inl.
assert (X16m : L5.u64_at RSEGS M4 (X + 16) F) by (apply K4a; [left; clear; lia| apply LX; [clear; lia| clear; lia| exact SX16]]).
assert (EKO : forall Ma Mb, (forall i, 0 <= i < 2 ^ 64 -> ~ (os + 256 <= i < os + 296) -> Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)) -> L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] Ma Mb).
{ intros Ma Mb FZ. apply (EKC Ma Mb [(os + 256, 40)] (fun a => os + 256 <= a < os + 296) FZ). intros a Y. right; right. intros Ho.
apply (Ho (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
assert (TO5 : forall (M5 : word -> option byte) a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS (mrestrict (ahid Aw4 model4) M5) a v -> L5.u64_at RSEGS M5 a v).
{ intros M5 a v Ha Hb Y. apply (proj1 (L5A.u64_at_vis _ M5 a v ltac:(apply OAV4; clear - Ha Hb; lia) ltac:(clear - Ha O1; lia) ltac:(clear - Hb O1; lia))). exact Y. }
destruct (Z.eq_dec c 16384) as [CF|CNF].
-
rewrite CF in A10c, IA4, C0.
cfeed P (PMBSRP3.bsrXge_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 45%nat => ois
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBSRP3.aligned; assumption | clear - QDE QPR I1 G1 G2 G3 Q0a Q0b Q0c Q0d Q0e Q0f; lia]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z10 & Z18 & Z22 & Z264 & Z272 & Z280 & Z288).
apply (CRUN fx4 R4 M4 model4 LK4 Aw4 fx5 R5 M5v 723580 0xb0b3c (fun a => os + 256 <= a < os + 296) BI4); [intros a Y; right; right; left; exact Y| exact MS5| exact MG5| |].
{ intros i Hi N. apply FRZ5; [exact Hi| intros Y; apply N; clear - Y; lia]. }
intros M5 model5 BI5 VIS5 MGM5 FR5.
apply (EXITP fx5 R5 M5 model5 LK4 Aw4 de 0 (g + 16384) 0 16384 BI5).
+ rewrite (KS5 2%nat) by inl. exact Z2.
+ rewrite (KS5 8%nat) by inl. exact Z8.
+ rewrite (KS5 9%nat) by inl. exact Z9.
+ exact Z22.
+ rewrite (KS5 25%nat) by inl. exact T25.
+ rewrite (KS5 26%nat) by inl. exact T26.
+ rewrite (KS5 3%nat) by inl. exact Z3.
+ rewrite (KS5 4%nat) by inl. exact Z4.
+ apply (L5C.u64_at_agree RSEGS M4 M5); [intros i Hi; apply FR5; [clear - Hi QX; lia| clear - Hi QXo; lia]| clear - Q0e; lia| clear - QX; lia| exact X16m].
+ apply TO5; [clear; lia| clear; lia| rewrite VIS5; exact Z264].
+ apply TO5; [clear; lia| clear; lia| rewrite VIS5; exact Z272].
+ apply TO5; [clear; lia| clear; lia| rewrite VIS5; exact Z280].
+ apply TO5; [clear; lia| clear; lia| rewrite VIS5; exact Z288].
+ exact G1.
+ clear; lia.
+ clear - G3; lia.
+ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 _ M4 M5 (EKO M4 M5 FR5) WSW FRB BRB ois str _ AOI); [exact SOWN| exact OUTIS| exact OUTBLK| exact IA4].
+ clear - C0; lia.
+ intros Y; exact Y.
+ clear; lia.
+ clear; lia.
+ intros Y; exfalso; clear - Y; lia.
+ intros Y; exfalso; clear - Y; lia.
-
assert (Cr : 0 <= c <= 16383) by (clear - C0 CNF; lia).
cfeed P (PMBSRP3.bsrXlt_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 45%nat => ois
| 47%nat => F | 48%nat => fl | 50%nat => X | 51%nat => c | _ => 0 end)) ltac:(first [assumption | unfold PMBSRP3.aligned; assumption | clear - Cr QDE QPR I1 G1 G2 G3 Q0a Q0b Q0c Q0d Q0e Q0f; lia]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z10 & Z12 & Z13 & Z18 & Z22 & Z152 & Z264 & Z272 & Z280 & Z288).
apply (CRUN fx4 R4 M4 model4 LK4 Aw4 fx5 R5 M5v 723580 0xb0b3c (fun a => os + 256 <= a < os + 296 \/ ois + 152 <= a < ois + 156) BI4);
[intros a [Y|Y]; [right; right; left; exact Y| right; right; right; exact Y]| exact MS5| exact MG5| |].
{ intros i Hi N. apply FRZ5; [exact Hi| intros Y; apply N; left; clear - Y; lia| intros Y; apply N; right; clear - Y; lia]. }
intros M5 model5 BI5 VIS5 MGM5 FR5.
set (WE := [(os + 256, 40); (ois + 152, 4)]).
assert (EK45 : L5SAR.ek L ar LB FF sp 20480 WE M4 M5).
{ apply (EKC M4 M5 WE _ FR5). intros a [Y|Y]; right; right; intros Ho.
- apply (Ho (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia].
- apply (Ho (ois + 152, 4)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
assert (WSE : PMKB.wapp WE).
{ unfold WE. apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - OBIG; Lia.lia|].
apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - IBIG; Lia.lia| apply PMKB.wapp_nil]. }
assert (U152 : L5.u32_at RSEGS M5 (ois + 152) 2).
{ rewrite <- VIS5 in Z152. apply (proj1 (L5A.u32_at_vis _ M5 (ois + 152) 2 ltac:(apply IAV4; lia) ltac:(lia) ltac:(lia))). exact Z152. }
assert (OUTI : forall i, ois <= i < ois + 272 -> ~ (ois + 152 <= i < ois + 156) -> L5.outside WE i).
{ intros i Hi N r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; [clear - Hi IOS2; lia| clear - N; lia]. }
assert (IA5 : PM.iss_at RSEGS PMB.AD PMSPA.accA M5 ois str (PM.STRM (g + c) eg 2)).
{ apply (PMBSK.iss_st_updA M4 M5 ois str (g + c) eg 0 2 IA4); [clear - I1; lia| clear - I1; lia| | | | exact MGM5| | exact U152| right; reflexivity].
- apply (PMKB.agA_obj L ar LB FF sp 20480 WE M4 M5 EK45 WSE FRB ois 152); [apply (PMBSK.aobj_fb FF fb); [exact FOK| unfold ois, PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_B]; lia| unfold ois, PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_B]; lia]|].
intros i Hi. apply OUTI; clear - Hi; lia.
- apply (PMKB.agA_obj L ar LB FF sp 20480 WE M4 M5 EK45 WSE FRB (ois + 156) 116); [apply (PMBSK.aobj_fb FF fb); [exact FOK| unfold ois, PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_B]; lia| unfold ois, PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_B]; lia]|].
intros i Hi. apply OUTI; clear - Hi; lia.
- apply (PMKB.agsh_obj L ar LB FF sp 20480 WE M4 M5 EK45 WSE FRB (ois + 152) 4). apply (PMBSK.aobj_fb FF fb); [exact FOK| unfold ois, PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_B]; lia| unfold ois, PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_B]; lia].
- intros c1 n1 q1 E. assert (SIN : In (q1, c1) LB) by (apply SOWN; rewrite E; left; reflexivity).
apply (PMKB.agA_blk L ar LB FF sp 20480 WE M4 M5 EK45 WSE BRB q1 c1 SIN). intros i Hi r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd].
+ destruct (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 os 296 HH SIN AO) as [Zb|Zb]; clear - Hi Zb; lia.
+ destruct (PMBSK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 ois 272 HH SIN AOI) as [Zb|Zb]; clear - Hi Zb; lia. }
apply (EXITP fx5 R5 M5 model5 LK4 Aw4 de 0 (g + c) 2 c BI5).
+ rewrite (KS5 2%nat) by inl. exact Z2.
+ rewrite (KS5 8%nat) by inl. exact Z8.
+ rewrite (KS5 9%nat) by inl. exact Z9.
+ exact Z22.
+ rewrite (KS5 25%nat) by inl. exact T25.
+ rewrite (KS5 26%nat) by inl. exact T26.
+ rewrite (KS5 3%nat) by inl. exact Z3.
+ rewrite (KS5 4%nat) by inl. exact Z4.
+ apply (L5C.u64_at_agree RSEGS M4 M5); [intros i Hi; apply FR5; [clear - Hi QX; lia| intros [Y|Y]; clear - Y Hi QXo QXi; lia]| clear - Q0e; lia| clear - QX; lia| exact X16m].
+ apply TO5; [clear; lia| clear; lia| rewrite VIS5; exact Z264].
+ apply TO5; [clear; lia| clear; lia| rewrite VIS5; exact Z272].
+ apply TO5; [clear; lia| clear; lia| rewrite VIS5; exact Z280].
+ apply TO5; [clear; lia| clear; lia| rewrite VIS5; exact Z288].
+ exact G1.
+ clear; lia.
+ clear - G3; lia.
+ exact IA5.
+ clear - C0; lia.
+ intros _; reflexivity.
+ clear - Cr; lia.
+ clear; lia.
+ intros Y; exfalso; clear - Y; lia.
+ intros _; split; reflexivity.
Qed.
End WithHeap.
End PMBSRD.
