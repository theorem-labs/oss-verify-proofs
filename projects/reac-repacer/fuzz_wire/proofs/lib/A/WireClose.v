(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: made for reac-repacer/fuzz_uci's ASan image from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/A/DecodeClose.v (the closing form: one named Section hypothesis per open part, the parts proved elsewhere applied as Lemmas of the hypotheses' names and statements, the program contract LIB_CONTRACT from the entry walk and its callees, the two statements from AsanTop; its About / Print Assumptions commands are left out, because on this image's core those commands for the three tops take about 13 minutes per build) and libreac/fuzz_grant proofs/libreac/fuzz_grant/lib/A/AGrantT.v (the driver step: the core arguments of tfib_srealizesX, the run ceiling and TFIB_T), with the sink guard of fuzz_grant's lib/A/GrantTop.v; names GrantB -> UciB, the library shape fuzz_uci's checksum_shape, fuzz_uci's own program statements and rows; module paths changed. *)
(* The closing side of fuzz_wire's two ASan statements (this file is assembly: it proves no function), in the form of
   fuzz_uci's lib/A/UciClose.v.

   TFIB_T (lib/A/WireTFIB.v) is closed by lib/A/WireCloseParts.v wire_TFIB_T_of_lib: the relocated core's
   lib/A/AD1q.v:172 tfib_srealizesX over the program contract of the entry function (lib/A/ACfn.v
   tfib_lib_contract_x_all), which LIB_CONTRACT below gives from the entry's walk and its callees' contracts. From
   TFIB_T, lib/A/AsanTop.v gives Statements.asan_agrees and Statements.asan_halts.

   This file takes NO hypothesis. The walk of every program function is a proved theorem, applied at its statement
   (lib/A/Prog/<fn>_cg.v):
   - the entry: lib/A/Prog/LLVMFuzzerTestOneInput_walk.v wire_llvmf_holds_any;
   - the checks: lib/A/Prog/check_forward_cgW.v wire_check_forward_holds, check_ret_cgW.v wire_check_ret_cg_holds,
     check_downstream_cgW.v wire_check_downstream_cg_holds, check_meter_cgW.v wire_check_meter_holds,
     check_counter_cgW.v wire_check_counter_cg_holds, check_width_cgW.v wire_check_width_holds, check_read_cgW.v
     wire_check_read_holds, check_copy_cgW.v wire_check_copy_cg_holds;
   - rp_copy_untag (realizes form): lib/A/Prog/rp_copy_untag_cgW.v wire_rp_copy_untag_holds;
   - the library leaves, by their footprint walks, each leaf's PROVED translation wire_<leaf>_cg_of_F and the kit
     glue: rp_fwd_class_FW.v, rp_ret_accept_FW.v, rp_ds_accept_FW.v, rp_meter_counter_FW.v, rp_counter_FW.v
     (<leaf>_holds_F), the chain reac_frame_clean_len_F.v -> rp_frame_channels_F.v -> rp_slot_width_F.v ->
     rp_slot_read_F.v, and reac_frame_is_reac_F_nosh.v (reac_frame_clean_len and reac_frame_is_reac: the released
     libreac/fuzz_decode walks relocated).
   Every other part is a Lemma: the runtime contracts, the facts about WireB and the meter, the leaf-kit facts, the
   fake stack of classes 0 and 1 and the driver step (lib/A/WireCloseParts.v), and the record facts
   (lib/A/WireAFacts.v). *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_repacer.fuzz_wire Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK15 YK18.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK04 YA0i YA0n YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YE00 YE01 YCbq YC5d YCbp YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v AD2l AF0m ACfn AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import WireTFIB.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require PaBase WireCg LeafCgKit
LLVMFuzzerTestOneInput_cg check_forward_cg check_ret_cg check_downstream_cg check_meter_cg check_counter_cg
check_width_cg check_width_cgW check_read_cg check_copy_cg check_forward_cgW check_ret_cgW check_counter_cgW check_copy_cgW
check_downstream_cgW check_meter_cgW check_read_cgW
rp_ret_accept_FW rp_counter_FW LLVMFuzzerTestOneInput_walk
rp_fwd_class_F_c rp_fwd_class_FW rp_fwd_class_cg rp_ret_accept_F_c rp_ret_accept_cg rp_ds_accept_F_c rp_ds_accept_FW
rp_ds_accept_cg
rp_meter_counter_F_c rp_meter_counter_FW rp_meter_counter_cg rp_counter_F_c rp_counter_cg rp_frame_channels_F_c
rp_frame_channels_F
rp_frame_channels_cg
rp_slot_width_F_c rp_slot_width_F rp_slot_width_cg rp_slot_read_F_c rp_slot_read_F rp_slot_read_cg rp_copy_untag_cg
rp_copy_untag_cgW
reac_frame_is_reac_F_nosh reac_frame_is_reac_cg reac_frame_clean_len_F_c reac_frame_clean_len_F
reac_frame_clean_len_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Rt Require MemmoveDef.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require WireAFacts WireCloseParts AsanTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance checksum_shape.
Open Scope Z_scope.

Module WSt := OSSVerify.reac_repacer.fuzz_wire.Statements.
Module PB := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.PaBase.
Module PCs := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.WireCg.
Module LK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.LeafCgKit.
Module PL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.LLVMFuzzerTestOneInput_cg.
Module PCF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_forward_cg.
Module PCR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_ret_cg.
Module PCD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_downstream_cg.
Module PCM := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_meter_cg.
Module PCN := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_counter_cg.
Module PCW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_width_cg.
Module PCRD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_read_cg.
Module PCC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_copy_cg.
Module FFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_fwd_class_F_c.
Module LFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_fwd_class_cg.
Module FRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_ret_accept_F_c.
Module LRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_ret_accept_cg.
Module FDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_ds_accept_F_c.
Module LDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_ds_accept_cg.
Module FMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_meter_counter_F_c.
Module LMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_meter_counter_cg.
Module FRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_counter_F_c.
Module LRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_counter_cg.
Module FFCH := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_frame_channels_F.
Module LFCH := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_frame_channels_cg.
Module FSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_slot_width_F_c.
Module LSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_slot_width_cg.
Module FSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_slot_read_F_c.
Module LSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_slot_read_cg.
Module PRU := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_copy_untag_cg.
Module FIR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.reac_frame_is_reac_F_nosh.
Module LIR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.reac_frame_is_reac_cg.
Module WCL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.reac_frame_clean_len_F.
Module LCL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.reac_frame_clean_len_cg.
Module MD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Rt.MemmoveDef.
Module WAF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.WireAFacts.
Module WCP := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.WireCloseParts.

(* The guard: the plain build's sink hints are out of the way. *)
#[local] Remove Hints YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints YI5c.src0_sink : typeclass_instances.

Local Abbreviation segs := wiresegs0.
Local Abbreviation B := AD2l.WireB.
Local Abbreviation MT := ameter_triv.
Local Abbreviation XL := WAF.wire_XL0.
Local Abbreviation RLO := WAF.WIRE_RLO.
Local Abbreviation RHI := WAF.WIRE_RHI.

(* ===================================================================================================== *)
(* The facts about B that the program statements shape, by computation at WireB                         *)
(* ===================================================================================================== *)
(* check_copy's two fixed traces ([0x52594; 0x80c88], [0x52434; 0x80dd0]) and the entry's four (lib/A/ACej.v
   TRACES_LLVMFuzzerTestOneInput) are in Tfib_universe. *)
Lemma HB_CC_UFIX : @PCC.wire_cc_ufix B.
Proof. unfold PCC.wire_cc_ufix. split; apply WAF.wacrt_trace_mem_In; vm_compute; reflexivity. Qed.
Lemma HB_LLVMF_UFIX : @PL.wire_llvmf_ufix B.
Proof.
  assert (D1 : forallb (fun r => WAF.wacrt_trace_mem (PCs.wire_utrace (pc_malloc_ra0 (as_code B)) [r]) (as_universe B))
                 PL.WIRE_LLVMF_RA_MALLOC = true) by (vm_compute; reflexivity).
  assert (D2 : forallb (fun r => WAF.wacrt_trace_mem (PCs.wire_utrace (pc_free_ra0 (as_code B)) [r]) (as_universe B))
                 PL.WIRE_LLVMF_RA_FREE = true) by (vm_compute; reflexivity).
  unfold PL.wire_llvmf_ufix. split; intros r Hr.
  - exact (WAF.wacrt_trace_mem_In _ _ (proj1 (forallb_forall _ _) D1 r Hr)).
  - exact (WAF.wacrt_trace_mem_In _ _ (proj1 (forallb_forall _ _) D2 r Hr)).
Qed.
(* At MT = ameter_triv every mo_malloc and mo_free is 0, so the entry's cost is 0 <= wire_XL0 n. *)
Lemma HB_COST : forall n, 0 <= n -> @PL.wire_llvmf_cost MT n <= XL n.
Proof.
  intros n _. unfold PL.wire_llvmf_cost, PCC.wire_check_copy_cost, WAF.wire_XL0, ameter_triv. cbn.
  destruct ((n =? 0) || (2 ^ 26 <=? n))%bool; lia.
Qed.

Section RC. Context {rc : YM05.RunCeil}.

(* ===================================================================================================== *)
(* 1. The leaves, from their footprint walks, their PROVED translations and the kit glue                 *)
(* ===================================================================================================== *)
(* cgF is passed as @lemma (all implicit arguments explicit), so its first argument is the float state fx. *)
Local Ltac leaf_of_F cgF fx HF :=
  exact (cgF fx (world segs) (@w_H segs) (SRr segs) alayout astate (@AR rc segs B) (aview segs)
    same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B) (WCP.H_LEAF_GLUE rc fx) HF).

(* The footprint chain, every link PROVED: reac_frame_clean_len -> rp_frame_channels -> rp_slot_width ->
   rp_slot_read. *)
Let CLN_F := WCL.reac_frame_clean_len_holds_F.
Let FCH_F := FFCH.rp_frame_channels_holds_F CLN_F.
Let SW_F := rp_slot_width_F.rp_slot_width_holds_F FCH_F.
Let SR_F := rp_slot_read_F.rp_slot_read_holds_F SW_F.

Lemma LEAF_FWD : forall fx : YK11.FPState, @PCs.wire_leaf_at rc B (@LFC.wire_rp_fwd_class_cg) fx.
Proof. intros fx. leaf_of_F (@LFC.wire_rp_fwd_class_cg_of_F) fx rp_fwd_class_FW.rp_fwd_class_holds_F. Qed.
Lemma LEAF_RET : forall fx : YK11.FPState, @PCs.wire_leaf_at rc B (@LRA.wire_rp_ret_accept_cg) fx.
Proof. intros fx. leaf_of_F (@LRA.wire_rp_ret_accept_cg_of_F) fx rp_ret_accept_FW.rp_ret_accept_holds_F. Qed.
Lemma LEAF_DS : forall fx : YK11.FPState, @PCs.wire_leaf_at rc B (@LDA.wire_rp_ds_accept_cg) fx.
Proof. intros fx. leaf_of_F (@LDA.wire_rp_ds_accept_cg_of_F) fx rp_ds_accept_FW.rp_ds_accept_holds_F. Qed.
Lemma LEAF_MET : forall fx : YK11.FPState, @PCs.wire_leaf_wr_at rc B (@LMC.wire_rp_meter_counter_cg) fx.
Proof. intros fx. leaf_of_F (@LMC.wire_rp_meter_counter_cg_of_F) fx rp_meter_counter_FW.rp_meter_counter_holds_F. Qed.
Lemma LEAF_CNT : forall fx : YK11.FPState, @PCs.wire_leaf_at rc B (@LRC.wire_rp_counter_cg) fx.
Proof. intros fx. leaf_of_F (@LRC.wire_rp_counter_cg_of_F) fx rp_counter_FW.rp_counter_holds_F. Qed.
Lemma LEAF_FCH : forall fx : YK11.FPState, @PCs.wire_leaf_at rc B (@LFCH.wire_rp_frame_channels_cg) fx.
Proof. intros fx. leaf_of_F (@LFCH.wire_rp_frame_channels_cg_of_F) fx FCH_F. Qed.
Lemma LEAF_SR : forall fx : YK11.FPState, @PCs.wire_leaf_wr_at rc B (@LSR.wire_rp_slot_read_cg) fx.
Proof. intros fx. leaf_of_F (@LSR.wire_rp_slot_read_cg_of_F) fx SR_F. Qed.
Lemma LEAF_ISR : forall fx : YK11.FPState, @PCs.wire_leaf_at rc B (@LIR.wire_reac_frame_is_reac_cg) fx.
Proof. intros fx. leaf_of_F (@LIR.wire_reac_frame_is_reac_cg_of_F) fx FIR.reac_frame_is_reac_holds_F_nosh. Qed.

(* ===================================================================================================== *)
(* 2. The callees of the entry, from their walks and their callee contracts                              *)
(* ===================================================================================================== *)
Lemma RCPY_HOLDS : forall fx : YK11.FPState, @PRU.wire_rp_copy_untag_cg fx rc B (wire_sigma WS_rp_copy_untag).
Proof.
  intros fx. apply (@rp_copy_untag_cgW.wire_rp_copy_untag_holds fx rc B).
  - exact WAF.wire_cells_WireB.
  - apply AR_laws_ok.
  - intros fx'. exact (WCP.H_RT_ASAN_MEMMOVE rc fx').
  - exact LEAF_ISR.
Qed.
Lemma CFWD_HOLDS : forall fx : YK11.FPState, @PCF.wire_check_forward_cg fx rc B MT (wire_sigma WS_check_forward).
Proof.
  intros fx. apply (@check_forward_cgW.wire_check_forward_holds fx rc B MT);
    [exact WAF.wire_cells_WireB | apply AR_laws_ok | exact WCP.HB_METER_LAWS | exact LEAF_FWD].
Qed.
Lemma CRET_HOLDS : forall fx : YK11.FPState, @PCR.wire_check_ret_cg fx rc B MT (wire_sigma WS_check_ret).
Proof.
  intros fx. apply (@check_ret_cgW.wire_check_ret_cg_holds fx rc B MT);
    [exact WAF.wire_cells_WireB | apply AR_laws_ok | exact WCP.HB_METER_LAWS | exact LEAF_RET].
Qed.
Lemma CDS_HOLDS : forall fx : YK11.FPState, @PCD.wire_check_downstream_cg fx rc B MT (wire_sigma WS_check_downstream).
Proof.
  intros fx. apply (@check_downstream_cgW.wire_check_downstream_cg_holds fx rc B MT);
    [exact WAF.wire_cells_WireB | apply AR_laws_ok | exact WCP.HB_METER_LAWS | exact LEAF_DS].
Qed.
Lemma CCNT_HOLDS : forall fx : YK11.FPState, @PCN.wire_check_counter_cg fx rc B MT (wire_sigma WS_check_counter).
Proof.
  intros fx. apply (@check_counter_cgW.wire_check_counter_cg_holds fx rc B MT);
    [exact WAF.wire_cells_WireB | apply AR_laws_ok | exact WCP.HB_METER_LAWS | exact LEAF_CNT].
Qed.
Lemma CWID_HOLDS : forall fx : YK11.FPState, @PCW.wire_check_width_cg fx rc B MT (wire_sigma WS_check_width).
Proof.
  intros fx. apply (@check_width_cgW.wire_check_width_holds fx rc B MT).
  - exact WAF.wire_cells_WireB.
  - exact WAF.wire_ro_rd_unowned_WireB.
  - exact WAF.wire_rom_no_errno_WireB.
  - apply AR_laws_ok.
  - exact WCP.HB_METER_LAWS.
  - exact LEAF_FCH.
Qed.
Lemma CMET_HOLDS : forall fx : YK11.FPState, @PCM.wire_check_meter_cg fx rc B MT (wire_sigma WS_check_meter).
Proof.
  intros fx. apply (@check_meter_cgW.wire_check_meter_holds fx rc B MT).
  - exact WCP.HB_PC_STACK_MALLOC0.
  - exact WAF.wire_cells_WireB.
  - apply AR_laws_ok.
  - exact WCP.HB_METER_LAWS.
  - exact WCP.HB_METER_FS_LAWS.
  - exact WCP.HB_SMP.
  - exact (WCP.HB_ASF rc).
  - exact (WCP.HB_FFL rc).
  - intros fx'. exact (WCP.H_RT_STACK_MALLOC0 rc fx').
  - exact LEAF_MET.
Qed.
Lemma CRD_HOLDS : forall fx : YK11.FPState, @PCRD.wire_check_read_cg fx rc B MT (wire_sigma WS_check_read).
Proof.
  intros fx. apply (@check_read_cgW.wire_check_read_holds fx rc B MT).
  - exact WCP.HB_PC_STACK_MALLOC1.
  - exact WAF.wire_cells_WireB.
  - exact WAF.wire_ro_rd_unowned_WireB.
  - exact WAF.wire_rom_no_errno_WireB.
  - apply AR_laws_ok.
  - exact WCP.HB_METER_LAWS.
  - exact WCP.HB_METER_FS_LAWS.
  - exact WCP.HB_SMP.
  - exact (WCP.HB_ASF rc).
  - exact (WCP.HB_FFL rc).
  - intros fx'. exact (WCP.H_RT_STACK_MALLOC1 rc fx').
  - intros fx'. exact (WCP.H_RT_ASAN_MEMSET rc fx').
  - exact LEAF_SR.
Qed.
Lemma CCPY_HOLDS : forall fx : YK11.FPState, @PCC.wire_check_copy_cg fx rc B MT (wire_sigma WS_check_copy).
Proof.
  intros fx. apply (@check_copy_cgW.wire_check_copy_cg_holds fx rc B MT).
  - exact WCP.HB_PC_WRAP_MALLOC.
  - exact WCP.HB_PC_WRAP_FREE.
  - exact WAF.wire_cells_WireB.
  - apply AR_laws_ok.
  - exact WCP.HB_METER_LAWS.
  - exact HB_CC_UFIX.
  - intros fx'. exact (WCP.H_LINK_MALLOC04 rc fx').
  - intros fx'. exact (WCP.H_LINK_FREE04 rc fx').
  - intros fx'. exact (WCP.H_RT_ASAN_MEMCPY rc fx').
  - intros fx'. exact (WCP.H_RT_BCMP rc fx').
  - exact RCPY_HOLDS.
Qed.

(* ===================================================================================================== *)
(* 3. The program contract of the entry function, from its walk and every callee it names                *)
(* ===================================================================================================== *)
Lemma LIB_CONTRACT : @tfib_lib_contract_x_all rc checksum_shape B MT XL XL RLO RHI.
Proof.
  apply (@LLVMFuzzerTestOneInput_walk.wire_llvmf_holds_any rc B MT XL RLO RHI).
  - exact WCP.HB_PC_WRAP_MALLOC.
  - exact WCP.HB_PC_WRAP_FREE.
  - exact WAF.wire_cells_WireB.
  - exact WAF.wire_ro_rd_unowned_WireB.
  - exact WAF.wire_rom_no_errno_WireB.
  - exact HB_LLVMF_UFIX.
  - apply AR_laws_ok.
  - exact WCP.HB_MODEL_LAWS.
  - exact WCP.HB_METER_LAWS.
  - exact WCP.HB_METER_FS_LAWS.
  - exact WCP.HB_SINK_IMG_LAWS.
  - exact (WCP.HB_SINK_KEPT rc).
  - exact (WCP.HB_META_KEPT rc).
  - exact WAF.wire_ro_below_ofl_WireB.
  - intros fx. exact (WCP.H_LINK_MALLOC04 rc fx).
  - intros fx. exact (WCP.H_LINK_FREE04 rc fx).
  - intros fx. exact (WCP.H_RT_ASAN_MEMCPY rc fx).
  - exact CFWD_HOLDS.
  - exact CRET_HOLDS.
  - exact CDS_HOLDS.
  - exact CMET_HOLDS.
  - exact CCNT_HOLDS.
  - exact CWID_HOLDS.
  - exact CRD_HOLDS.
  - exact CCPY_HOLDS.
  - exact HB_COST.
Qed.
End RC.

(* ===================================================================================================== *)
(* 4. The composition                                                                                     *)
(* ===================================================================================================== *)
Theorem wire_TFIB_T_of_parts : TFIB_T.
Proof. exact (WCP.wire_TFIB_T_of_lib (fun rc => @LIB_CONTRACT rc)). Qed.

(* The two ASan statements of record. *)
Theorem wire_asan_agrees_of_parts : WSt.asan_agrees.
Proof. exact (AsanTop.wire_asan_agrees_of_tfib wire_TFIB_T_of_parts). Qed.
Theorem wire_asan_halts_of_parts : WSt.asan_halts.
Proof. exact (AsanTop.wire_asan_halts_of_tfib wire_TFIB_T_of_parts). Qed.
