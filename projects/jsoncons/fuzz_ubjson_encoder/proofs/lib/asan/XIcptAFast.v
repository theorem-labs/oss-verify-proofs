(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanFast SegFastHavoc XIcptA XIcptAs0Kit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_XIcptAFast () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SegPlan3SGP6regionC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX29sym_state00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan6XIcptA3XIA5xstepC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegPlanFast3SGF9existsb_lC13~~~C47Corelib4Init5Logic8eq_ind_rC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegPlanFast3SGF9forallb_lC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan:XIcptAFast4XIAF7xstep_gC13~~~I47Corelib4Init5Logic2eq00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX26kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX24expr00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<AsanPlanCore3APC8kn_havocC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegPlanFast3SGF;copy_factsMC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<AsanPlanCore3APC:copy_factsC13~~~I47Corelib4Init9Datatypes4bool00C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List7forallbc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan:XIcptAFast4XIAF;xstep_g_refC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegPlanFast3SGF=forallb_l_eqfC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegPlanFast3SGF=existsb_l_eqfC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegPlanFast3SGF>copy_factsM_eqC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<SegFastHavoc4AX2H:kn_havocMFC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<SegFastHavoc4AX2H=kn_havocMF_eqC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan:XIcptAFast4XIAF7xstep_fC13~~~C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images4Asan1M?loaded_segmentsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan6XIcptA3XIA8AS0_MSETC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan6XIcptA3XIA8AS0_MCPYC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan6XIcptA3XIA9AS0_CELLSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan6XIcptA3XIA9AS0_TLSPCC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan6XIcptA3XIA:AS0_TCELLSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan6XIcptA3XIA7AS0_TPVC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan6XIcptA3XIA8AS0_ENTVC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan6XIcptA3XIA;AS0_CTXSLOTC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan6XIcptA3XIA;AS0_BLKSLOTC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan:XIcptAFast4XIAF:xstep_f_eqC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan:XIcptAFast6XIAS0F7xstep_fC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan;XIcptAs0Kit5XIAS05xstepC13~~~".
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module XIAF.
Definition xstep_g :=
  ltac:(let t := eval cbv beta delta [XIA.xstep XIA.xmemset XIA.xmemcpy XIA.xtls XIA.has_cells XIA.has_tcells XIA.shz_cover] in @XIA.xstep in
        SGF.has_const t (@APC.kn_havoc); SGF.has_const t (@APC.copy_facts); SGF.has_const t (@existsb); SGF.has_const t (@forallb);
        let t' := eval pattern (@APC.kn_havoc), (@APC.copy_facts), (@existsb), (@forallb) in t in
        lazymatch t' with ?F _ _ _ _ => exact F end).
Lemma xstep_g_ref : xstep_g (@APC.kn_havoc) (@APC.copy_facts) (@existsb) (@forallb) = @XIA.xstep.
Proof.
ltac2:(KReplay.run1 (kr_t_XIcptAFast ()) [] "h07BLKSLOTh15CELLSh27CTXSLOTh34ENTVh41Fh54MCPYh64MSETh76TCELLSh85TLSPCh93TPVh:2idh;4segsh<2ssp;1p;2g0000j10Tg000Pj21Tg0010j13Tg001Rj22Tg001l#0g002kR0g003IR1,10/10#0R2g003h#0g0055R3%33]<^:1]4^00^20^30^90^72^80]1^50]6];g006J'2o"). Qed.
Definition xstep_f := xstep_g AX2H.kn_havocMF SGF.copy_factsM (@SGF.existsb_l) (@SGF.forallb_l).
Theorem xstep_f_eq : xstep_f = @XIA.xstep.
Proof. unfold xstep_f. rewrite AX2H.kn_havocMF_eq, SGF.copy_factsM_eq, SGF.existsb_l_eqf, SGF.forallb_l_eqf. exact xstep_g_ref. Qed.
End XIAF.

(* [comment removed for export] *)
Module XIAS0F.
Definition xstep_f : list SGP.region -> nat -> sym_state -> option sym_state :=
  XIAF.xstep_f Asan.M.loaded_segments XIA.AS0_MSET XIA.AS0_MCPY XIA.AS0_CELLS XIA.AS0_TLSPC XIA.AS0_TCELLS XIA.AS0_TPV XIA.AS0_ENTV XIA.AS0_CTXSLOT XIA.AS0_BLKSLOT.
Lemma xstep_f_eq : xstep_f = XIAS0.xstep.
Proof.
ltac2:(KReplay.run1 (kr_t_XIcptAFast ()) [] "h07BLKSLOTh15CELLSh27CTXSLOTh34ENTVh41Fh54MCPYh64MSETh76TCELLSh85TLSPCh93TPVh:2idh;1oh<4segsh=2ssp;1p;2p;:p;3p;6g0000j10Tg000Pj21Tg0010j14Tg006JR0l:3Tg00<7j32Tg001Rj26Tg008nj65Tg001l#0g002kR1g003IR2,11/11#0R3g003h#0R4g0055R5%45R6]=^:2]4^01^21^31^91^73^81]1^51]6]<R1P0P6\5\2\4R4f0g00N7R2g00ODR5g00PWR6g00QjR0g00S>R3g00TRR7g00UgR8g00W9R9g00XLR:g00YbR;O:P2P5P6P0P3P7P8P9P:P;M:3R;32X;1164;g00L`g00[8E5g00\Rg00]k524eo"). Qed.
End XIAS0F.
