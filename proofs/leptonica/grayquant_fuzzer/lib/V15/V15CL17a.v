(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PropExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StepTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Hoare.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require ShapeAlg.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require AllocIface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PureModel.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require VmLedger.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StoreOk.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPSteps.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL14a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptRmc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptDithBinSpec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptDith2Spec.
Module V15LeptDithTop.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL14a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptRmc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptDithBinSpec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptDith2Spec.
(* [comment removed for export] *)









Import V15CL14a.V15LeptDither_iface.


Section DithTop.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.

Theorem pixDitherToBinary_Wc : pixDitherToBinary_contract.
Proof. exact (pixDitherToBinary_W pixRemoveColormap_gray8_W). Qed.

Theorem pixDitherTo2bpp_Wc : pixDitherTo2bpp_contract.
Proof. exact (pixDitherTo2bpp_W pixRemoveColormap_gray8_W). Qed.
End DithTop.
End V15LeptDithTop.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoomPC.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom14.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL7a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL8a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL10a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCopy.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL15a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL16a.
Module V15LeptGqWrap.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoomPC.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom14.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL7a.
Import V15CL8a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCreate.
Import V15CL10a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopy.
Import V15CL14a.
Import V15CL15a.
Import V15CL16a.
(* [comment removed for export] *)









Import V15CL7a.V15LeptErr.

Import V15CL8a.V15LeptPixHdr. Import V15CL8a.V15LeptGqArms. Import V15CL8a.V15LeptThrErr.


Import V15CL10a.V15LeptCmapValid.


Import V15CL14a.V15LeptDither_iface.

Import V15CL15a.V15LeptOwn.

Import V15CL16a.V15LeptGq_iface. Import V15CL16a.V15LeptThr.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Wrap.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Theorem F1_W : pixDitherTo2bpp_contract -> pixDitherTo2bpp_d_contract -> F1_contract.
Proof.
  intros HS HD. unfold F1_contract, gq_F_contract.
  intros fx C X A m md regs s pix w h d cd data ad kd kna kn ret S FZ CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 OWN HOK Hw Hh kR bR RM HkR HbR HC.
  unfold GQ_STACK_F, TP_gq in *.
  destruct OWN as [P0 | OWN].
  - subst pix.
    apply (F1_null_W fx C A m md regs s ret S FZ CK HW H2 Hs16 ltac:(unfold GQ_ARM_STACK, LSF; lia) Hhi H1 Hret H10).
    intros fx' m' regs' FZ' HW' CS' PM' A0'. rewrite <- (with_vmmaps_same md).
    apply (HC fx' A m' (m_vmmaps md) regs' FZ' ltac:(rewrite with_vmmaps_same; exact HW') CS' PM' (or_introl (conj A0' (fun q => eq_refl)))).
    apply (aroom_mono A (m_vmmaps md) kR bR); [exact RM | clear - HkR; unfold RK_d2bpp, RK_dbin, RK_thr_gq, RK_rmc, RK_cml, RK_pix in *; lia | clear - HbR; unfold RB_d2bpp, RB_dbin, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia].
  - pose proof (pown_cm_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWN) as CMF.
    destruct OWN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR).
    destruct (FR _ (or_introl eq_refl)) as [_ L0p].
    destruct (Z.eq_dec d 8) as [->|ND].
    + apply (HS fx C A m md regs s pix w h cd data (CMAPV ad kd kna kn 0) ret S FZ CK HW H2 Hs16 ltac:(unfold D2BPP_STACK, RMC_STACK, LSF; lia) Hhi H1 Hret H4 H10 H11
               PX HOK Hw Hh Lp L0p Ld CMF kR bR RM HkR HbR).
      intros fx' A' m' vm' regs' FZ' HW' CS' PM' RES RM'.
      apply (HC fx' A' m' vm' regs' FZ' HW' CS' PM'); [|exact RM'].
      destruct RES as [[A0' LQ] | (pixd & datad & cdd & cv' & A0' & PN & _)]; [left; split; assumption | right].
      exists pixd, w, h, 2%Z, cdd, datad, cv'. split; [exact A0' | split; [exact PN|]].
      assert (1 <= wpl_of w 2)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). nia.
    + apply (HD fx C A m md regs s pix w h d cd data ret S CK HW H2 Hs16 ltac:(unfold LSF; lia) Hhi H1 Hret H10 PX ND Lp).
      intros m' regs' HW' CS' PM' A0'. rewrite <- (with_vmmaps_same md).
      apply (HC fx A m' (m_vmmaps md) regs' FZ ltac:(rewrite with_vmmaps_same; exact HW') CS' PM' (or_introl (conj A0' (fun q => eq_refl)))).
      apply (aroom_mono A (m_vmmaps md) kR bR); [exact RM | clear - HkR; unfold RK_d2bpp, RK_dbin, RK_thr_gq, RK_rmc, RK_cml, RK_pix in *; lia | clear - HbR; unfold RB_d2bpp, RB_dbin, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia].
Qed.

Theorem F2_W : pixDitherToBinary_contract -> pixDitherToBinary_d_contract -> F2_contract.
Proof.
  intros HS HD. unfold F2_contract, gq_F_contract.
  intros fx C X A m md regs s pix w h d cd data ad kd kna kn ret S FZ CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 _ OWN HOK Hw Hh kR bR RM HkR HbR HC.
  unfold GQ_STACK_F, TP_gq in *.
  destruct OWN as [P0 | OWN].
  - subst pix.
    apply (F2_null_W fx C A m md regs s ret S FZ CK HW H2 Hs16 ltac:(unfold GQ_ARM_STACK, LSF; lia) Hhi H1 Hret H10).
    intros fx' m' regs' FZ' HW' CS' PM' A0'. rewrite <- (with_vmmaps_same md).
    apply (HC fx' A m' (m_vmmaps md) regs' FZ' ltac:(rewrite with_vmmaps_same; exact HW') CS' PM' (or_introl (conj A0' (fun q => eq_refl)))).
    apply (aroom_mono A (m_vmmaps md) kR bR); [exact RM | clear - HkR; unfold RK_d2bpp, RK_dbin, RK_thr_gq, RK_rmc, RK_cml, RK_pix in *; lia | clear - HbR; unfold RB_d2bpp, RB_dbin, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia].
  - pose proof (pown_cm_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWN) as CMF.
    destruct OWN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR).
    destruct (FR _ (or_introl eq_refl)) as [_ L0p].
    destruct (Z.eq_dec d 8) as [->|ND].
    + apply (HS fx C A m md regs s pix w h cd data (CMAPV ad kd kna kn 0) ret S FZ CK HW H2 Hs16 ltac:(unfold DBIN_STACK, RMC_STACK, LSF; lia) Hhi H1 Hret H4 H10 
               PX HOK Hw Hh Lp L0p Ld CMF kR bR RM HkR HbR).
      intros fx' A' m' vm' regs' FZ' HW' CS' PM' RES RM'.
      apply (HC fx' A' m' vm' regs' FZ' HW' CS' PM'); [|exact RM'].
      destruct RES as [[A0' LQ] | (pixd & datad & cdd & cv' & A0' & PN & _)]; [left; split; assumption | right].
      exists pixd, w, h, 1%Z, cdd, datad, cv'. split; [exact A0' | split; [exact PN|]].
      assert (1 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). nia.
    + apply (HD fx C A m md regs s pix w h d cd data ret S CK HW H2 Hs16 ltac:(unfold LSF; lia) Hhi H1 Hret H10 PX ND Lp).
      intros m' regs' HW' CS' PM' A0'. rewrite <- (with_vmmaps_same md).
      apply (HC fx A m' (m_vmmaps md) regs' FZ ltac:(rewrite with_vmmaps_same; exact HW') CS' PM' (or_introl (conj A0' (fun q => eq_refl)))).
      apply (aroom_mono A (m_vmmaps md) kR bR); [exact RM | clear - HkR; unfold RK_d2bpp, RK_dbin, RK_thr_gq, RK_rmc, RK_cml, RK_pix in *; lia | clear - HbR; unfold RB_d2bpp, RB_dbin, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia].
Qed.

Theorem F6_W : pixRemoveColormap_gray8_contract -> pixDestroy_rc2_contract -> F6_contract.
Proof.
  intros HRMC HRC2. unfold F6_contract, gq_F_contract.
  intros fx C X A m md regs s pix w h d cd data ad kd kna kn ret S FZ CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 (H11 & H12 & H13 & H14 & H15) OWN HOK Hw Hh kR bR RM HkR HbR HC.
  unfold GQ_STACK_F, TP_gq, GQ_EDGES in *.
  destruct OWN as [P0 | OWN].
  - subst pix.
    apply (F6_null_W fx C A m md regs s ret S FZ CK HW H2 Hs16 ltac:(unfold GQ_ARM_STACK, LSF; lia) Hhi H1 Hret H10).
    intros fx' m' regs' FZ' HW' CS' PM' A0'. rewrite <- (with_vmmaps_same md).
    apply (HC fx' A m' (m_vmmaps md) regs' FZ' ltac:(rewrite with_vmmaps_same; exact HW') CS' PM' (or_introl (conj A0' (fun q => eq_refl)))).
    apply (aroom_mono A (m_vmmaps md) kR bR); [exact RM | clear - HkR; unfold RK_d2bpp, RK_dbin, RK_thr_gq, RK_rmc, RK_cml, RK_pix in *; lia | clear - HbR; unfold RB_d2bpp, RB_dbin, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia].
  - pose proof (pown_cm_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWN) as CMF.
    destruct OWN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR).
    destruct (FR _ (or_introl eq_refl)) as [_ L0p].
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    destruct (Z.eq_dec d 8) as [->|ND].
    + apply (pixThresholdGrayArb_W HRMC HRC2 fx C A m md regs s pix w h cd data (CMAPV ad kd kna kn 0) ret S FZ CK HW H2 Hs16 ltac:(unfold THR_STACK; lia) Hhi H1 Hret H4 H10
               H11 H12 H13 H14 H15 PX HOK Hw Hh Lp L0p Ld CMF kR bR RM HkR HbR).
      intros fx' A' m' vm' regs' FZ' HW' CS' PM' (pixd & datad & cmap & cmaparr & A0' & PN) RM'.
      apply (HC fx' A' m' vm' regs' FZ' HW' CS' PM'); [|exact RM'].
      right. exists pixd, w, h, 8%Z, cmap, datad, (CMAPV cmaparr 8 256 5 0). split; [exact A0' | split; [exact PN | exact Rpos]].
    + pose proof PX as (_ & _ & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh. pose proof (wf_d _ WF) as Rd. cbn in Rw, Rh, Rd.
      apply (thr_d_W fx C A m md regs s pix w h d ret S CK HW H2 Hs16 ltac:(unfold THRE_WIN; lia) Hhi H1 Hret H10 Lp ltac:(lia) ltac:(lia) ALp Rw Rh Rd ND
               ltac:(rewrite Z.add_0_r; exact (PIX_rd_w SEGS m pix _ PX)) (PIX_rd_h SEGS m pix _ PX) (PIX_rd_d SEGS m pix _ PX)).
      intros m' regs' HW' CS' PM' A0'. rewrite <- (with_vmmaps_same md).
      apply (HC fx A m' (m_vmmaps md) regs' FZ ltac:(rewrite with_vmmaps_same; exact HW') CS' PM' (or_introl (conj A0' (fun q => eq_refl)))).
      apply (aroom_mono A (m_vmmaps md) kR bR); [exact RM | clear - HkR; unfold RK_d2bpp, RK_dbin, RK_thr_gq, RK_rmc, RK_cml, RK_pix in *; lia | clear - HbR; unfold RB_d2bpp, RB_dbin, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia].
Qed.
End Wrap.
End V15LeptGqWrap.
