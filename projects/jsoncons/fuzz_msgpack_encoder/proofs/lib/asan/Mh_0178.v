(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan XIcptA. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module XIcptAs0Kit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan XIcptA. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.XIcptA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_XIcptAs0Kit () := "C69OSSVerify5KrLib4asan6XIcptA3XIA8xstep_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA8AS0_MSETC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA8AS0_MCPYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA9AS0_CELLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA9AS0_TLSPCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA:AS0_TCELLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA7AS0_TPVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA8AS0_ENTVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA;AS0_CTXSLOTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA;AS0_BLKSLOTC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS09fill_specC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS09copy_specC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS08tls_specC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import AX2.
Open Scope Z_scope.
Module XIAS0.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition fill_spec : Prop := XIA.icpt_fill_spec RSEGS XIA.AS0_MSET XIA.AS0_CELLS.
Definition copy_spec : Prop := XIA.icpt_copy_spec RSEGS XIA.AS0_MCPY XIA.AS0_CELLS.
Definition tls_spec : Prop := XIA.icpt_tls_spec RSEGS XIA.AS0_TLSPC XIA.AS0_TCELLS XIA.AS0_TPV XIA.AS0_ENTV XIA.AS0_CTXSLOT XIA.AS0_BLKSLOT.
Definition xstep : list SGP.region -> nat -> sym_state -> option sym_state :=
  XIA.xstep RSEGS XIA.AS0_MSET XIA.AS0_MCPY XIA.AS0_CELLS XIA.AS0_TLSPC XIA.AS0_TCELLS XIA.AS0_TPV XIA.AS0_ENTV XIA.AS0_CTXSLOT XIA.AS0_BLKSLOT.
Theorem xstep_ok : fill_spec -> copy_spec -> tls_spec -> forall nx0 BR F M0, SGP.XSTEP_ok RSEGS nx0 BR xstep F M0.
Proof.
ltac2:(KReplay.run1 (kr_t_XIcptAs0Kit ()) [] "h02HCh12HFh22HTp;=g0000l=0Tg000mg002Bg003?g004<g005:g0068g0077g0083g0090g00:0f2R0f1R1f0R2M=0p=1g00;0g00<=g00=JA1012W2W0W1o"). Qed.
End XIAS0.

End XIcptAs0Kit.
From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0087. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require XIcptA.
Module XIcptAFast.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0087. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require XIcptA. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.SegPlanFast OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0087.SegFastHavoc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.XIcptA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.XIcptAs0Kit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac2 kr_t_XIcptAFast () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib7SegPlan3SGP6regionC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29sym_state00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA5xstepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF9existsb_lC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF9forallb_lC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA8AS0_MSETC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA8AS0_MCPYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA9AS0_CELLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA9AS0_TLSPCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA:AS0_TCELLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA7AS0_TPVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA8AS0_ENTVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA;AS0_CTXSLOTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan6XIcptA3XIA;AS0_BLKSLOTC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib4asan7Mh_0178:XIcptAFast4XIAF7xstep_fC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib4asan7Mh_0178:XIcptAFast4XIAF:xstep_f_eqC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib4asan7Mh_0178:XIcptAFast6XIAS0F7xstep_fC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS05xstepC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import AX2. Import AX2B. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
ltac2:(KReplay.run1 (kr_t_XIcptAFast ()) [] "h07BLKSLOTh15CELLSh27CTXSLOTh34ENTVh41Fh54MCPYh64MSETh76TCELLSh85TLSPCh93TPVh:2idh;4segsh<2ssp;1p;2g0000j10Tg000Pj21Tg0010j13Tg001Rj22Tg001l#0g002kR0g003IR1,10/10#0R2g003h#0g004_R3%33]<^:1]4^00^20^30^90^72^80]1^50]6];g005f'2o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_XIcptAFast ()) [] "h07BLKSLOTh15CELLSh27CTXSLOTh34ENTVh41Fh54MCPYh64MSETh76TCELLSh85TLSPCh93TPVh:2idh;1oh<4segsh=2ssp;1p;2p;:p;3p;6p1006`p4p710R0g007fR1p4p710p9P0p1008Dp4p710R2p8P2P0p8P0p1008`p4p710R2p8P2P0p8g0000j10Tg000Pj21Tg0010j14Tg005fR0l:3Tg009fj32Tg001Rj26TP1j65Tg001l#0g002kR1g003IR2,11/11#0R3g003h#0R4g004_R5%45R6]=^:2]4^01^21^31^91^73^81]1^51]6]<R1P0P6\5\2\4R4f0g00:@R2g00;UR5g00<RR6g00=OR0g00>MR3g00?KR7g00@JR8g00AFR9g00BCR:g00CCR;O:P2P5P6P0P3P7P8P9P:P;M:3R;32X;1164;g00DCg00ELE5g00FXg00Gc524eo"). Qed.
End XIAS0F.

End XIcptAFast.
