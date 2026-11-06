(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmFrame PmParSpecs PmParSpecsU PmParKit PmParStep PmSrcUPeekP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSrcUPeek () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecsU.PMPSU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "2and"; "2eq"; "3Z"; "0HI"; "0K"; "0L"; "0LB"; "4Model"; "4m_halted"]; ["4m_vm_lazy"; "4m_vmmaps"; "5bvmap"; "0M1"; "0M3"; "0R1"; "0R3"; "6credit"; "6hi_heap"; "6hl_sptop"; "7stk"; "9defined"; "9u64_at"; "8SCFG"; ":fill_buffer_spec"; ":peek_spec"]; [";cfg"; "<FPState"; "<getr"; "=TSet"; ">srealizes"; "?mem_grows"; "@loaded_segments"; "0SCFG_P"; "AIn"; "Ble"; "Blt"; "Bof_nat"; "Bpow"; "Bsub"; "0a"; "0b"]; ["0cr"; "0fx1"; "0fx3"; "0i"; "0k"; "0model"; "0sp"; "CZ_to_bv"; "Cbv"; "Cbv_unsigned"; "0w1"; "0w8"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMUPK.
Import PMU.
Ltac tr64 M0 AG := lazymatch goal with |- L5.u64_at ?sg ?M2 ?a ?v =>
let X := fresh "X" in assert (X : L5.u64_at sg M0 a v) by PMK.gmem;
apply (L5C.u64_at_agree sg M0 M2 a v); [apply AG; lia | lia | lia | exact X] end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Let SF := PMKU.sfoot_U L LY.
Lemma peek_tail : ltac2:(TCodec.tc2 tcn__PmSrcUPeek "W4'Q1&By5'QHyR0%211%5241'5y8%611%311p061'>&Q3'2'6'9%2211%411&G&Hv:r6r5r9&Ar8%211%8576541'8%G1I&?%118(0%11M%63531%E2OO%G11&@r:%211(4%116%>3631&J&Iv<%211r<r7+@%744321&Q2r>&QG&Q;u2%211%42QH1%7261&Q=%12Q3;%82QJ1%Q23QJ41r?u:%;11%=2R11%@241%?2R1Q;%Q93R121'7&Q9z%221QB&Q:&Q<+2+QO%3221%52QH1%:271&Kr@+1%332Q>1&L&Q6rA+8%N2Q:1&QI%12RHQE%746531rBr=%Q421Q>%;4:315pSJRMRHr1%L2K1+X0%K231%Q0231r4%QE21Q6r2%QE2S71%R?3S731u1%QG11%QI2S=1%QL2RI1%RD3S<1C%QN2RLQHrE%QN2S@1%RH3S@31u8%R011%R22SF1%R52R81rC%RN3SF21'3&Q8(1u3u4u9uBuCuDuEuFuGuHuIuJuK%S31@%?3A21%@3B41%A3C61%B3D81%C3E:1%D3F<1%E3G>1%F3H@1%G3IB1%H3JD1%I3KF1%J3LH1%K3MJ1%M3NQG1%S41QA%S62TJ1%S92SF1rO%S;213%T33TK31p071pS:Q61+R0%RH2RG1%RJ2R21%RO2R21%T01QL%:1QM%T<3TO21p041pS8TK1&Q5rN%221TFrLrK%TH14%TN5TM32T;1'Q4&MvQ7%211&Q0+VlTLr;%36S3RKT:21L%84S451>p0:1p0?1p0C1p0M1p0R51p0R<1p0RA1p0RG1p0RM1pS0UE1pQ:S41pQ>V11pS6V81rF+VlT<rD%E6SE3RI21RB%J4SFG1S?p061p0S>1p0SC1p0SL1p0T11p0T=1p0TE1p0U21p0U;1p0UD1p0UL1pSHVD1pSFVE1pRNV;1pS>V<1pS2V:1pLV<1pHVB1pS<VD1pQ8VF1pQ<VL1pS4W31").
Proof. intros fx1 R1 M1 model K LB cr sp a w1 w8.
intros HH Mh Ml STK R2 R10 Ha D C8 C16 KONT.
pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
destruct (PMPX.lbu_run RSEGS fx1 R1 M1 0x3708c (ltac:(oW' 0x3708c%Z)) 10%bv 10%bv 0%bv a (ltac:(oF' 0x3708c%Z)) eq_refl (ltac:(oD' 0x3708c%Z))) as (b & Hb & U8 & MSb).
{ intros E. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate E. }
{ lia. } { lia. } { rewrite L5K.rl10. exact R10. } { lia. }
{ change (bv_signed (0%bv : bv 12)) with 0. lia. } { change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r. exact D. }
change (0x3708c + 4) with 0x37090 in MSb. rewrite L5K.rl10 in MSb.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx1 fx1 R1 0x3708c _ 0x37090 M1 K Mh Ml MSb).
set (R2' := regupd R1 (PMK.reg 10) (Z_to_bv 64 b)) in *.
assert (O : forall k, k <> 10%nat -> (k < 32)%nat -> getr R2' (PMK.reg k) = getr R1 (PMK.reg k)) by (intros k N Hk; apply PMPX.regupd_other_idx; lia).
pose proof (bv_unsigned_in_range 64 w1) as B1. pose proof (bv_unsigned_in_range 64 w8) as B8. change (bv_modulus 64) with (2 ^ 64) in *.
pose proof (L5C.stk_writable RSEGS _ M1 sp 16 STK) as WR.
cfeed P (PMUPKP.upkT_conc fx1 R2' M1 (fun j => match j with 2%nat => sp | 40%nat => bv_unsigned w1 | 41%nat => bv_unsigned w8 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUPKP.aligned; exact A16 | rewrite O by lia; exact R2]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & T1 & T2 & T8)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8.
apply (PMK.spiece RSEGS L HI KL HIok LB cr M1 model fx1 fx3 R2' 0x37090 R3 0x3709c M3 (fun _ => False) K HH Mh Ml ltac:(lia) MS MG).
{ intros i Hi _. apply FRZ. exact Hi. } { intros i []. } { intros i. right. intros []. }
intros HH3. apply (KONT fx3 R3 M3 b Hb); try assumption.
- rewrite (KS 10%nat) by PMK.inl. apply PMPX.regupd_same_idx. lia.
- intros k Hk. rewrite (KS k) by (revert k Hk; apply (PMPK.sub_in PMUPKP.KS_upkT); vm_compute; reflexivity).
apply O; cbn in Hk; repeat (destruct Hk as [<-|Hk]; [lia|]); destruct Hk.
Qed.
Theorem peek_ok : ltac2:(TCodec.tc2 tcn__PmSrcUPeek "8&NvQ7v<v:%43321&O%13543p031").
Proof.
intros FB. unfold PMPSU.peek_spec, PMPS.peek_spec, PMPS.src_spec.
intros fx R M model K LBX cr sp r fb s str sm Wextra HH MOK K0 ENT FOK A10 _ WX PA IA BASE INCS KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame AD PmLayoutU.ADDR_U] in F2.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
unfold PMSP.no_W in WX. subst Wextra. rewrite app_nil_r in KONT.
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
unfold PMSP.o_src, PMSP.o_p, PMSP.o_is in *. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U] in *.
change (PMSP.pm_scr 4) with 20480 in *. unfold PM.CHUNK in *.
assert (SC0 : 0 <= 20480) by lia.
set (LB := PM.parser_own s ++ LBX) in *.
assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
pose proof (L5C.stk_writable RSEGS _ M sp 20480 STK) as WR.
destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. destruct sm as [g eg st].
cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
destruct (BR qc 16384 QIN) as (Q0 & Q1 & Q4). unfold hl_ceil in Q4.
pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & PSRC & _).
destruct PSRC as (_ & _ & S256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & _ & DCH & _).
cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
set (s0 := PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk) in *.
assert (PINC : incl (PM.parser_own s0) LB) by (unfold LB; apply incl_appl; apply incl_refl).
assert (AL36 : (fb + 40 + 24) mod 8 = 0) by (replace (fb + 40 + 24) with (fb + 8 * 8) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (WF : L5.writable RSEGS M (fb + 40 + 24 + 256) 40).
{ apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M (fb + 40) 384); [exact PDEF|lia|lia]|lia|lia]. }
set (WS := PMSP.W_srcf AD fb ++ [(qc, 16384)]).
assert (WSE : PMSP.W_src AD fb (PM.SRC qc de rem) = WS) by reflexivity. rewrite WSE in KONT. clear WSE.
assert (WCs : forall a, PMK.inW WS a -> (fb + 320 <= a < fb + 360) \/ (fb + 480 <= a < fb + 488) \/ (fb + 592 <= a < fb + 596) \/ (qc <= a < qc + 16384)).
{ intros a (r0 & Hin & Hr). unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is in Hin. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U app] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia. }
assert (INF : forall a, fb + 320 <= a < fb + 360 -> PMK.inW WS a).
{ intros a Ha. unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U app]. apply PMK.inW_here. lia. }
assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
unfold PMSP.cfg. cbn [pa_peek AD PmLayoutU.ADDR_U].
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as B8.
change (bv_modulus 64) with (2 ^ 64) in *.
assert (REMB : 0 <= rem <= 16384) by lia.
assert (DEB : qc <= de <= qc + 16384) by lia.
destruct (Z_le_gt_dec 1 rem) as [REM1|REM0].
-
cfeed P (PMUPKP.upkA1_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUPKP.aligned; first [exact A16 | exact AL36] | apply (L5.defined_sub M qc 16384); [exact DCH|lia|lia] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & FR1 & FRZ1 & MS1 & KS1 & X2 & X8 & X10 & C16 & C8)); PMK.pvz_clrT.
set (P1 := fun a => sp - 16 <= a < sp - 16 + 16).
assert (PF1 : forall a, P1 a -> sp - 20480 <= a < sp) by (intros a X; unfold P1 in X; lia).
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x37050 R1 0x3708c M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1).
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). apply PF1 in Pa. lia. }
{ intros a. apply PMK.rng_dec. }
intros HH1.
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by (apply (PMK.stk_grows L M M1 sp 20480 MG1 STK)).
assert (EK1 : PMK.ek L LB sp 20480 [] M M1) by (apply (PMFR.ek_of_piece RSEGS L KL LB sp 20480 M M1 P1 FRZ1 STK (PMFR.brange_hi L LB BR) PF1)).
apply (peek_tail fx1 R1 M1 model K LB cr sp de (getr R (PMK.reg 1)) (getr R (PMK.reg 8)) HH1 Mh Ml); try assumption.
{ apply (PMK.stk_call L M1 sp 20480 sp 16 STK1); [lia|lia|lia|exact A16]. }
{ lia. }
{ apply (L5.defined_grows M M1 _ _ MG1). apply (L5.defined_sub M qc 16384); [exact DCH|lia|lia]. }
intros fx3 R3 M3 b Hb T10 T1 T2 T8 KS3 EQ3 MG3 HH3.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
{ apply (PMK.ret_to RSEGS fx3 R3 M3 0x3709c (ltac:(oW' 0x3709c%Z)) r (ltac:(oF' 0x3709c%Z)) eq_refl (ltac:(oD' 0x3709c%Z))); [rewrite T1; exact Rra| lia| exact Hr2]. }
assert (EK3 : PMK.ek L LB sp 20480 [] M1 M3) by (intros a (Ha & _); apply EQ3; exact Ha).
assert (EK03 : PMK.ek L LB sp 20480 [] M M3) by (apply (PMK.ek_trans L LB sp 20480 [] M M1 M3 EK1 EK3)).
apply (KONT fx3 R3 M3 (PM.SRC qc de rem) (PM.STRM g eg st)).
+ apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [first [ rewrite T2; symmetry; exact Rsp | exact T8
| (rewrite (KS3 _) by PMK.inl; apply KS1; PMK.inl) ] |]). destruct Hk.
+ apply (PMFR.parser_keep RSEGS AD L KL LB sp 20480 [] M M3 EK03 STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact PINC| exact PA].
+ apply (PMFR.iss_keep RSEGS AD L KL LB sp 20480 [] M M3 EK03 STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact SINC| exact IA].
+ unfold PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros E; exact E| lia].
+ unfold PMPS.peek_res, PMSP.consumed, PM.unread. cbn [PM.sr_rem PM.sm_eg PM.sm_g]. split; [lia|]. right. exists b. rewrite L5K.rl10. split; [exact Hb|]. split; [exact T10| exact REM1].
+ apply (PMK.hpres_of L LB sp 20480 _ M M3).
* apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 _ [] M M3 EK03); [apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil.
* apply (L5.defined_grows M1 M3 _ _ MG3). apply (L5.defined_grows M M1 _ _ MG1). exact SDEF.
* apply (PMK.dk_grows L LB sp 20480 M M3). apply (mem_grows_trans M M1 M3 MG1 MG3).
+ exact HH3.
-
assert (rem = 0) by lia. subst rem.
cfeed P (PMUPKP.upkA0_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUPKP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & FR1 & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X11 & X12 & C280 & C16 & C8 & C264 & C272 & C288 & C256)); PMK.pvz_clrT.
set (P1 := fun a => (sp - 16 <= a < sp - 16 + 16) \/ (fb + 320 <= a < fb + 360)).
assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ1; [exact Ha| |]; intros X; apply N; unfold P1; [left; exact X| right; lia]. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x37050 R1 0x37720 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P1 in Pa. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
set (W1 := [(fb + 320, 40)] : list L5.range).
assert (WHI1 : forall a, PMK.inW W1 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
assert (EK1 : PMK.ek L LB sp 20480 W1 M M1).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M M1 P1 FRZ1' STK (PMFR.brange_hi L LB BR)). intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by (apply (PMK.stk_grows L M M1 sp 20480 MG1 STK)).
set (s1 := PMPS.with_src s0 (PM.SRC qc qc 0)).
assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (unfold LB, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BR _ _ VIN) as (V0 & _ & V4). unfold hl_ceil in V4.
assert (AGB1 : forall B m, In (B, m) LB -> L5C.agree_on M M1 B m).
{ intros B m Hin i Hi. destruct (BR B m Hin) as (Z0 & _ & Z4). unfold hl_ceil in Z4. apply FRZ1'; [lia|]. unfold P1. lia. }
assert (PA1 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) s1).
{ apply (PMPK.parser_src_upd RSEGS AD M M1 (fb + 40) (fb + 440) s0 qc 0 PA); cbn [s0 PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; unfold PM.CHUNK.
- lia.
- lia.
- intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
- intros i Hi. apply FRZ1'; [lia|]. unfold P1. lia.
- apply PMPK.dkr_grows. exact MG1.
- apply PMPK.dkr_grows. exact MG1.
- lia.
- lia.
- apply (AGB1 _ _ VIN).
- intros c0 n0 p0 _. apply PMPK.dkr_grows. exact MG1.
- replace (fb + 40 + 288) with (fb + 40 + 24 + 264) by lia. exact C264.
- replace (fb + 40 + 296) with (fb + 40 + 24 + 272) by lia. exact C272.
- replace (fb + 40 + 304) with (fb + 40 + 24 + 280) by lia. exact C280.
- replace (fb + 40 + 312) with (fb + 40 + 24 + 288) by lia. exact C288.
- lia.
- lia.
- lia. }
assert (IA1 : PM.iss_at RSEGS AD PMSP.T3 M1 (fb + 440) str (PM.STRM g eg st)).
{ apply (PMFR.iss_keep RSEGS AD L KL LB sp 20480 W1 M M1 EK1 STK SC0 BR WHI1); [lia|lia| |exact SINC| exact IA].
intros i Hi I. apply PMFR.inW_inv1 in I. lia. }
assert (BASE1 : PMST.base_ok RSEGS AD M1).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 W1 M M1 EK1); first [exact BASE | intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha; lia]. }
assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 16) 18432).
{ apply (PMK.stk_call L M1 sp 20480 (sp - 16) 18432 STK1); [lia|lia|lia|]. replace (sp - 16) with (sp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMPSU.fill_buffer_spec, PMPS.fill_buffer_spec, PMPS.src_spec in FB. cbn [pa_fill_buffer AD PmLayoutU.ADDR_U] in FB.
apply (FB fx1 R1 M1 model K LBX cr (sp - 16) 225404 fb s1 str (PM.STRM g eg st) [] HH1 MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [split; [lia| reflexivity]|]. split; [exact X2|].
split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutU.ADDR_U]. split; [lia|]. split; [lia| exact F3]. }
{ rewrite L5K.rl10. rewrite (KS1 10%nat) by PMK.inl. unfold PMSP.o_src, PMSP.o_p. cbn [pa_off_p AD PmLayoutU.ADDR_U]. exact A10. }
{ unfold PMPS.fill_args. rewrite L5K.rl11, L5K.rl12. split; [exact X11| exact X12]. }
{ reflexivity. }
{ unfold PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U]. exact PA1. }
{ unfold PMSP.o_is. cbn [pa_off_is AD PmLayoutU.ADDR_U]. exact IA1. }
{ exact BASE1. } { exact INCS. }
intros fx2 R2 M2 src2 sm2 RP2 PA2 IA2 STEP2 RES2 HP2 HH2.
unfold PMPS.fill_res in RES2. destruct RES2 as (-> & c & Y10 & CR & GG2 & _ & _).
unfold PMSP.o_p, PMSP.o_is in PA2, IA2. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U] in PA2, IA2.
change (PMSP.pm_scr 3) with 18432 in HP2. rewrite app_nil_r in HP2.
rewrite L5K.rl10 in Y10. unfold PM.CHUNK in CR.
destruct sm2 as [g2 eg2 st2]. cbn [PM.sm_g PM.sm_eg PM.sm_st] in GG2.
assert (EKc : PMK.ek L LB (sp - 16) 18432 WS M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (SCc : 0 <= 18432) by lia.
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 20480 (sp - 16) 18432 WS STK1 HP2); lia).
pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
assert (HI2 : forall a n, sp - 16 <= a -> a + n <= fb + 320 -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB (sp - 16) 18432 WS M1 M2 EKc STKc SCc a n H1); [lia|]. intros i Hi I. apply WCs in I. lia. }
assert (EK2 : PMK.ek L LB sp 20480 WS M1 M2).
{ apply (PMK.ek_callee_in' RSEGS L KL LB LB sp 20480 (sp - 16) 18432 WS WS M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LB BR)|].
intros a I. right. exact I. }
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as B1'. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as B8'.
change (bv_modulus 64) with (2 ^ 64) in B1', B8'.
assert (R2_2 : getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl; exact X2).
assert (R2_8 : getr R2 (PMK.reg 8) = Z_to_bv 64 (fb + 40 + 24)) by (rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl; exact X8).
pose proof PA2 as (_ & PDEF2 & _ & _ & _ & _ & _ & _ & _ & PSRC2 & _).
destruct PSRC2 as (_ & _ & T256 & T264 & T272 & T280 & T288 & _ & _ & _ & _ & DCH2 & _).
cbn [PMPS.with_src s1 s0 PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in T264, T280, T288, DCH2. unfold PM.CHUNK in *.
assert (WF2 : L5.writable RSEGS M2 (fb + 40 + 24 + 256) 40).
{ apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 (fb + 40) 384); [exact PDEF2|lia|lia]|lia|lia]. }
assert (C16' : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))).
{ apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C16]. }
assert (C8' : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))).
{ apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C8]. }
destruct (Z.eq_dec c 0) as [C0|C1].
+
subst c.
cfeed P (PMUPKP.upkB0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => qc | 36%nat => fb + 40 + 24
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUPKP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T10 & D288 & D264 & D272 & D280 & D256 & _)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8.
set (P3 := fun a => (sp - 16 <= a < sp - 16 + 16) \/ (fb + 320 <= a < fb + 360)).
assert (FRZ3' : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ3; [exact Ha| |]; intros X; apply N; unfold P3; [left; exact X| right; lia]. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model fx2 fx3 R2 0x3707c R3 0x3709c M3 P3 K HH2 Mh Ml ltac:(lia) MS3 MG3 FRZ3').
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P3 in Pa. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH3.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
{ apply (PMK.ret_to RSEGS fx3 R3 M3 0x3709c (ltac:(oW' 0x3709c%Z)) r (ltac:(oF' 0x3709c%Z)) eq_refl (ltac:(oD' 0x3709c%Z))); [rewrite T1; exact Rra| lia| exact Hr2]. }
assert (EK3 : PMK.ek L LB sp 20480 W1 M2 M3).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M2 M3 P3 FRZ3' STK2 (PMFR.brange_hi L LB BR)). intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
assert (EW1 : forall a, L5.outside WS a -> L5.outside W1 a).
{ intros a O r0 Hr0. unfold W1 in Hr0. destruct Hr0 as [<-|[]]. apply O. unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U app].
left. apply (f_equal2 (@pair Z Z)); lia. }
apply (KONT fx3 R3 M3 (PM.SRC qc qc 0) (PM.STRM g2 eg2 st2)).
* apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [first [ rewrite T2; symmetry; exact Rsp | exact T8
| (rewrite (KS3 _) by PMK.inl; rewrite (PMK.cs_of_preserved R1 R2 _ RP2) by PMK.inl; apply KS1; PMK.inl) ] |]). destruct Hk.
* apply (PMPK.parser_src_upd RSEGS AD M2 M3 (fb + 40) (fb + 440) s1 qc 0 PA2); cbn [s1 s0 PMPS.with_src PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; unfold PM.CHUNK.
-- lia.
-- lia.
-- intros i Hi. apply FRZ3'; [lia|]. unfold P3. lia.
-- intros i Hi. apply FRZ3'; [lia|]. unfold P3. lia.
-- apply PMPK.dkr_grows. exact MG3.
-- apply PMPK.dkr_grows. exact MG3.
-- lia.
-- lia.
-- intros i Hi. apply FRZ3'; [lia|]. unfold P3. lia.
-- intros c0 n0 p0 _. apply PMPK.dkr_grows. exact MG3.
-- replace (fb + 40 + 288) with (fb + 40 + 24 + 264) by lia. exact D264.
-- replace (fb + 40 + 296) with (fb + 40 + 24 + 272) by lia. exact D272.
-- replace (fb + 40 + 304) with (fb + 40 + 24 + 280) by lia. exact D280.
-- replace (fb + 40 + 312) with (fb + 40 + 24 + 288) by lia. exact D288.
-- lia.
-- lia.
-- lia.
* apply (PMFR.iss_keep RSEGS AD L KL LB sp 20480 W1 M2 M3 EK3 STK2 SC0 BR WHI1); [lia|lia| |exact SINC| exact IA2].
intros i Hi I. apply PMFR.inW_inv1 in I. lia.
* unfold PMSP.src_step, PM.unread in STEP2 |- *. cbn [s1 s0 PMPS.with_src PM.p_src PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st] in STEP2 |- *.
destruct STEP2 as (_ & E2 & L2 & S2 & _). split; [reflexivity|]. split; [exact E2|]. split; [exact L2|]. split; [exact S2| lia].
* unfold PMPS.peek_res, PMSP.consumed, PM.unread. cbn [PM.sr_rem PM.sm_eg PM.sm_g].
unfold PMSP.src_step in STEP2. cbn [PM.sm_eg] in STEP2. destruct STEP2 as (_ & E2 & _).
split; [lia|]. left. rewrite L5K.rl10. exact T10.
* apply (PMK.hpres_of L LB sp 20480 _ M M3).
-- apply (PMK.ek_trans L LB sp 20480 WS M M1 M3).
{ apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 WS W1 M M1 EK1); [apply incl_refl| intros x Hx; exact Hx| exact EW1]. }
apply (PMK.ek_trans L LB sp 20480 WS M1 M2 M3 EK2).
apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 WS W1 M2 M3 EK3); [apply incl_refl| intros x Hx; exact Hx| exact EW1].
-- destruct STK2 as (_ & _ & _ & _ & D2). apply (L5.defined_grows M2 M3 _ _ MG3). exact D2.
-- apply (PMK.dk_trans L LB sp 20480 M M1 M3); [apply (PMK.dk_grows L LB sp 20480 M M1 MG1)|].
apply (PMK.dk_trans L LB sp 20480 M1 M2 M3); [|apply (PMK.dk_grows L LB sp 20480 M2 M3 MG3)].
apply (PMK.dk_callee L LB LB sp 20480 (sp - 16) 18432 WS M1 M2 HP2 (incl_refl _)); lia.
* exact HH3.
+
cfeed P (PMUPKP.upkB1_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 36%nat => fb + 40 + 24
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUPKP.aligned; first [exact A16 | exact AL36] | apply (L5.defined_sub M2 qc 16384); [exact DCH2|lia|lia] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & T10 & D288 & D264 & D272 & D280 & D256 & D8 & D16)); PMK.pvz_clrT.
set (P3 := fun a => (sp - 16 <= a < sp - 16 + 16) \/ (fb + 320 <= a < fb + 360)).
assert (FRZ3' : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ3; [exact Ha| |]; intros X; apply N; unfold P3; [left; exact X| right; lia]. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model fx2 fx3 R2 0x3707c R3 0x3708c M3 P3 K HH2 Mh Ml ltac:(lia) MS3 MG3 FRZ3').
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P3 in Pa. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH3.
assert (STK3 : L5C.stk (hl_sptop L) M3 sp 20480) by (apply (PMK.stk_grows L M2 M3 sp 20480 MG3 STK2)).
assert (EK3 : PMK.ek L LB sp 20480 W1 M2 M3).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M2 M3 P3 FRZ3' STK2 (PMFR.brange_hi L LB BR)). intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
assert (PA3 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M3 (fb + 40) (fb + 440) (PMPS.with_src s0 (PM.SRC qc qc c))).
{ apply (PMPK.parser_src_upd RSEGS AD M2 M3 (fb + 40) (fb + 440) s1 qc c PA2); cbn [s1 s0 PMPS.with_src PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; unfold PM.CHUNK.
- lia.
- lia.
- intros i Hi. apply FRZ3'; [lia|]. unfold P3. lia.
- intros i Hi. apply FRZ3'; [lia|]. unfold P3. lia.
- apply PMPK.dkr_grows. exact MG3.
- apply PMPK.dkr_grows. exact MG3.
- lia.
- lia.
- intros i Hi. apply FRZ3'; [lia|]. unfold P3. lia.
- intros c0 n0 p0 _. apply PMPK.dkr_grows. exact MG3.
- replace (fb + 40 + 288) with (fb + 40 + 24 + 264) by lia. exact D264.
- replace (fb + 40 + 296) with (fb + 40 + 24 + 272) by lia. exact D272.
- replace (fb + 40 + 304) with (fb + 40 + 24 + 280) by lia. exact D280.
- replace (fb + 40 + 312) with (fb + 40 + 24 + 288) by lia. exact D288.
- lia.
- lia.
- lia. }
assert (IA3 : PM.iss_at RSEGS AD PMSP.T3 M3 (fb + 440) str (PM.STRM g2 eg2 st2)).
{ apply (PMFR.iss_keep RSEGS AD L KL LB sp 20480 W1 M2 M3 EK3 STK2 SC0 BR WHI1); [lia|lia| |exact SINC| exact IA2].
intros i Hi I. apply PMFR.inW_inv1 in I. lia. }
apply (peek_tail fx3 R3 M3 model K LB cr sp qc (getr R (PMK.reg 1)) (getr R (PMK.reg 8)) HH3 Mh Ml).
{ apply (PMK.stk_call L M3 sp 20480 sp 16 STK3); [lia|lia|lia|exact A16]. }
{ rewrite (KS3 2%nat) by PMK.inl. exact R2_2. }
{ exact T10. }
{ lia. }
{ apply (L5.defined_grows M2 M3 _ _ MG3). apply (L5.defined_sub M2 qc 16384); [exact DCH2|lia|lia]. }
{ exact D8. } { exact D16. }
intros fx4 R4 M4 b Hb U10 U1 U2 U8 KS4 EQ4 MG4 HH4.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
{ apply (PMK.ret_to RSEGS fx4 R4 M4 0x3709c (ltac:(oW' 0x3709c%Z)) r (ltac:(oF' 0x3709c%Z)) eq_refl (ltac:(oD' 0x3709c%Z))); [rewrite U1; exact Rra| lia| exact Hr2]. }
assert (EK4 : PMK.ek L LB sp 20480 [] M3 M4) by (intros a (Ha & _); apply EQ4; exact Ha).
assert (EW1 : forall a, L5.outside WS a -> L5.outside W1 a).
{ intros a O r0 Hr0. unfold W1 in Hr0. destruct Hr0 as [<-|[]]. apply O. unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U app].
left. apply (f_equal2 (@pair Z Z)); lia. }
apply (KONT fx4 R4 M4 (PM.SRC qc qc c) (PM.STRM g2 eg2 st2)).
* apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [first [ rewrite U2; symmetry; exact Rsp | exact U8
| (rewrite (KS4 _) by PMK.inl; rewrite (KS3 _) by PMK.inl; rewrite (PMK.cs_of_preserved R1 R2 _ RP2) by PMK.inl; apply KS1; PMK.inl) ] |]). destruct Hk.
* apply (PMFR.parser_keep RSEGS AD L KL LB sp 20480 [] M3 M4 EK4 STK3 SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact PINC| exact PA3].
* apply (PMFR.iss_keep RSEGS AD L KL LB sp 20480 [] M3 M4 EK4 STK3 SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact SINC| exact IA3].
* unfold PMSP.src_step, PM.unread in STEP2 |- *. cbn [s1 s0 PMPS.with_src PM.p_src PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st] in STEP2 |- *.
destruct STEP2 as (_ & E2 & L2 & S2 & _). split; [reflexivity|]. split; [exact E2|]. split; [exact L2|]. split; [exact S2| lia].
* unfold PMPS.peek_res, PMSP.consumed, PM.unread. cbn [PM.sr_rem PM.sm_eg PM.sm_g].
unfold PMSP.src_step in STEP2. cbn [PM.sm_eg] in STEP2. destruct STEP2 as (_ & E2 & _).
split; [lia|]. right. exists b. rewrite L5K.rl10. split; [exact Hb|]. split; [exact U10| lia].
* apply (PMK.hpres_of L LB sp 20480 _ M M4).
-- apply (PMK.ek_trans L LB sp 20480 WS M M1 M4).
{ apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 WS W1 M M1 EK1); [apply incl_refl| intros x Hx; exact Hx| exact EW1]. }
apply (PMK.ek_trans L LB sp 20480 WS M1 M2 M4 EK2).
apply (PMK.ek_trans L LB sp 20480 WS M2 M3 M4).
{ apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 WS W1 M2 M3 EK3); [apply incl_refl| intros x Hx; exact Hx| exact EW1]. }
apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 WS [] M3 M4 EK4); [apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil.
-- destruct STK3 as (_ & _ & _ & _ & D3). apply (L5.defined_grows M3 M4 _ _ MG4). exact D3.
-- apply (PMK.dk_trans L LB sp 20480 M M1 M4); [apply (PMK.dk_grows L LB sp 20480 M M1 MG1)|].
apply (PMK.dk_trans L LB sp 20480 M1 M2 M4); [apply (PMK.dk_callee L LB LB sp 20480 (sp - 16) 18432 WS M1 M2 HP2 (incl_refl _)); lia|].
apply (PMK.dk_grows L LB sp 20480 M2 M4). apply (mem_grows_trans M2 M3 M4 MG3 MG4).
* exact HH4.
Qed.
End WithHeap.
End PMUPK.
