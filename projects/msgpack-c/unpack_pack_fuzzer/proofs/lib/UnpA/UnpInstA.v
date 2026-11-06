(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge Ops ClientX GLib Seal PkOps UnpInst
     G0A G1A G3PA G4A GInvA GBndA GMid GNarrow GNameA GPerm GTwinViewC GVecHi GViewDrop2 GPotInit GPotName OpShLoadU GGran GGranP GChk GBgNone GRoomA GAncA GCnt GCurA GFmv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require GVEndA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GPotHR.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require VDestroy.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require VDestroyA GCapB GTwinBnd.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GExcl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UO UG CX.
Open Scope Z_scope.

Module UnpInstA.
Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs (XTP segs)) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Theorem g0a_sound : forall pc, contract_sound segs OPS MP PB (G0A.g0a_contract pc).
Proof. intros pc. exact (G0A.g0a_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.
Theorem g1a_sound : forall pc, contract_sound segs OPS MP PB (G1A.g1a_contract pc).
Proof. intros pc. exact (G1A.g1a_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.
Theorem g3pa_sound : forall pc, contract_sound segs OPS MP PB (G3PA.g3pa_contract pc).
Proof. intros pc. exact (G3PA.g3pa_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.
Theorem g4a_sound : forall pc rR rSZ, contract_sound segs OPS MP PB (G4A.g4a_contract pc rR rSZ).
Proof. intros pc rR rSZ. exact (G4A.g4a_sound pc rR rSZ segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.
Theorem ginva_sound : forall pc, contract_sound segs OPS MP PB (GInvA.ginva_contract pc).
Proof. intros pc. exact (GInvA.ginva_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem gbnda_sound : forall pc r, contract_sound segs OPS MP PB (GBndA.gbnd_contract pc r).
Proof. intros pc r. exact (GBndA.gbnd_sound pc r segs OPS MP PB). Qed.

Theorem gmid_sound : forall pc r, contract_sound segs OPS MP PB (GMid.gmid_contract pc r).
Proof. intros pc r. exact (GMid.gmid_sound pc r segs OPS MP PB). Qed.

Theorem gcnt_sound : forall pc r, contract_sound segs OPS MP PB (GCnt.gcnt_contract pc r).
Proof. intros pc r. exact (GCnt.gcnt_sound pc r segs OPS MP PB). Qed.

Theorem gfmv_sound : forall pc, contract_sound segs OPS MP PB (GFmv.GFmv.gfmv_contract segs pc).
Proof. intros pc. exact (GFmv.GFmv.gfmv_sound segs OPS MP PB pc). Qed.

Theorem gvea_sound : forall pc nf, contract_sound segs OPS MP PB (GVEndA.GVEA.gvea_contract pc nf).
Proof. intros pc nf. exact (GVEndA.GVEA.gvea_sound pc nf segs OPS MP PB). Qed.

Theorem gvea2_sound : forall pc nf, contract_sound segs OPS MP PB (GVEndA.GVEA.gvea2_contract pc nf).
Proof. intros pc nf. exact (GVEndA.GVEA.gvea2_sound pc nf segs OPS MP PB). Qed.

Theorem gvea3_sound : forall pc nf, contract_sound segs OPS MP PB (GVEndA.GVEA.gvea3_contract pc nf).
Proof. intros pc nf. exact (GVEndA.GVEA.gvea3_sound pc nf segs OPS MP PB). Qed.

Theorem gpothr_sound : forall pc c, contract_sound segs OPS MP PB (GPotHR.GPotHR.gpothr_contract pc c).
Proof. intros pc c. exact (GPotHR.GPotHR.gpothr_sound pc c segs OPS MP PB). Qed.

Theorem gcura_sound : forall pc, contract_sound segs OPS MP PB (GCurA.gcur_contract pc).
Proof. intros pc. exact (GCurA.gcur_sound pc segs OPS MP PB). Qed.

Theorem gnarrow_sound : forall pc, contract_sound segs OPS MP PB (GNarrow.gnarrow_contract pc).
Proof. intros pc. exact (GNarrow.gnarrow_sound pc segs OPS MP PB). Qed.

Theorem gtvc_carg_sound : forall pc i S, contract_sound segs OPS MP PB (GTwinViewC.gtvc_carg pc i S).
Proof. intros pc i S. exact (GTwinViewC.gtwinviewc_sound pc (GTwinViewC.sel_carg i) S segs OPS MP PB). Qed.
Theorem gtvc_reg_sound : forall pc r S, contract_sound segs OPS MP PB (GTwinViewC.gtvc_reg pc r S).
Proof. intros pc r S. exact (GTwinViewC.gtwinviewc_sound pc (GTwinViewC.sel_reg r) S segs OPS MP PB). Qed.

Theorem gvechi_sound : forall pc S ib ie, contract_sound segs OPS MP PB (GVecHi.gvechi_contract pc S ib ie).
Proof. intros pc S ib ie. exact (GVecHi.gvechi_sound pc S ib ie segs OPS MP PB). Qed.

Theorem gviewgc_sound : forall pc S, contract_sound segs OPS MP PB (GViewDrop2.gviewgc_contract pc S).
Proof. intros pc S. exact (GViewDrop2.gviewdrop_sound pc S GViewDrop2.mode_gc segs OPS MP PB). Qed.
Theorem gviewdrop_carg_sound : forall pc S i, contract_sound segs OPS MP PB (GViewDrop2.gviewdrop_carg_contract pc S i).
Proof. intros pc S i. exact (GViewDrop2.gviewdrop_sound pc S (GViewDrop2.mode_carg i) segs OPS MP PB). Qed.
Theorem gviewdrop_reg_sound : forall pc S r, contract_sound segs OPS MP PB (GViewDrop2.gviewdrop_reg_contract pc S r).
Proof. intros pc S r. exact (GViewDrop2.gviewdrop_sound pc S (GViewDrop2.mode_reg r) segs OPS MP PB). Qed.

Theorem ggran_sound : forall pc rs off, contract_sound segs OPS MP PB (GGran.ggran_contract pc rs off).
Proof. intros pc rs off. exact (GGran.ggran_sound pc rs off segs OPS MP PB). Qed.
Theorem ggranp_sound : forall pc rs off, contract_sound segs OPS MP PB (GGranP.ggranp_contract pc rs off).
Proof. intros pc rs off. exact (GGranP.ggranp_sound pc rs off segs OPS MP PB). Qed.

Theorem ggranl_sound : forall pc rs off, contract_sound segs OPS MP PB (GGranP.ggranl_contract pc rs off).
Proof. intros pc rs off. exact (GGranP.ggranl_sound pc rs off segs OPS MP PB). Qed.

Theorem grooma_sound : forall pc isV, contract_sound segs OPS MP PB (GRoomA.grooma_contract pc isV).
Proof. intros pc isV. exact (GRoomA.grooma_sound pc isV segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem ganca_sound : forall pc, contract_sound segs OPS MP PB (GAncA.GAncA.ganca_contract pc).
Proof. intros pc. exact (GAncA.GAncA.ganca_sound pc segs IMGX AW _ OPS HOPS MP PB). Qed.

Theorem gtwinbnd_sound : forall pc, contract_sound segs OPS MP PB (GTwinBnd.GTwinBnd.gtwinbnd_contract pc).
Proof. intros pc. exact (GTwinBnd.GTwinBnd.gtwinbnd_sound pc segs OPS MP PB). Qed.

Theorem gbgnone_sound : forall pc r, contract_sound segs OPS MP PB (GBgNone.gbgnone_contract pc r).
Proof. intros pc r. exact (GBgNone.gbgnone_sound pc r segs OPS MP PB). Qed.

Theorem gperm_vec_sound : forall pc, contract_sound segs OPS MP PB (GPerm.gperm_vec_contract pc).
Proof. intros pc. exact (UnpInst.gperm_sound segs IMGX AW OPS HOPS MP PB pc (GPerm.twin_of_carg 4%nat) (GPerm.twin_of_carg 1%nat)). Qed.

Theorem gcapb_sound : forall pc isV, contract_sound segs OPS MP PB (GCapB.GCapB.gcapb_contract pc isV).
Proof. intros pc isV. exact (GCapB.GCapB.gcapb_sound pc isV segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem gcapb2_sound : forall pc, contract_sound segs OPS MP PB (GCapB.GCapB.gcapb2_contract pc).
Proof. intros pc. exact (GCapB.GCapB.gcapb2_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem gexcl_sound : forall pc, contract_sound segs OPS MP PB (GExcl.GExcl.gexcl_contract pc).
Proof. intros pc. exact (GExcl.GExcl.gexcl_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem gpotinit_sound : forall pc, contract_sound segs OPS MP PB (GPotInit.gpotinit_contract pc).
Proof. intros pc. exact (GPotInit.gpotinit_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem gnamea_sound : forall pc, contract_sound segs OPS MP PB (GNameA.gnamea_contract pc).
Proof. intros pc. exact (GNameA.gnamea_sound pc segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS MP PB). Qed.
Theorem gpotname_sound : forall pc, contract_sound segs OPS MP PB (GPotName.gpotname_contract pc).
Proof. intros pc. exact (GPotName.gpotname_sound pc segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS MP PB). Qed.

Section Acc.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Theorem vd_acc_sound : forall pc cur beg lim s ng, contract_sound segs OPS MP PB (VDestroy.VD.vd_contract segs pc cur beg lim s ng).
Proof. intros pc cur beg lim s ng. exact (VDestroyA.VDA.vd_sound_acc segs pc cur beg lim s ng OPS MP PB HMPA). Qed.

Theorem gchkl_sound : forall pc rs off pcok hv rl fuel, contract_sound segs OPS MP PB (GChk.GChk.gchkl_contract segs pc rs off pcok hv rl fuel).
Proof. intros pc rs off pcok hv rl fuel. exact (GChk.GChk.gchkl_sound segs pc rs off pcok hv rl fuel OPS MP PB HMPA). Qed.

Section ShLoad.
Variable CHS : list oinst -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis LAWS : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPS mo -> Forall (fun o => op_holds OPS (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CHS os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPS mo' /\
              Forall (fun o => op_holds OPS (fst o) (snd o) m mo') os.
Hypothesis SHLAW : forall os args md aw ws ca LB m mo cs c p,
  In (OPID, args) os -> decode args = Some (md, aw, ws, ca) ->
  aw_holds segs IMGX AW aw LB ws m mo -> windows_wf ws LB (aw_ceiling segs IMGX AW mo) ->
  Seal.seal_ok ws cs -> In c cs -> In (chunk_block c) LB ->
  (forall w, In w ws -> (w_kind w = K_BLOCK \/ K_GHOST <= w_kind w) -> forall a, in_iv (w_iv w) a -> ~ in_iv (chunk_block c) a) ->
  in_iv (chunk_block c) p ->
  m (Z_to_bv 64 (Seal.shadZ p)) = Some (Z_to_bv 8 0) /\ CHS os m mo (Seal.shadZ p).

Theorem opshloadu_sound : forall pc, contract_sound segs OPS MP PB (OpShLoadU.opshloadu_c segs pc).
Proof. exact (OpShLoadU.opshloadu_sound segs IMGX AW (XTP segs) OPS HOPS CHS LAWS SHLAW MP PB HMPA). Qed.
End ShLoad.
End Acc.
End Sound.
End UnpInstA.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Notation OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Model OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Layout OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Ops OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.ClientX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Seal OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkOps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.UnpInst OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.G0A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.G1A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.G3PA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.G4A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GInvA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GBndA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GMid OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GNarrow OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GNameA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GPerm OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GTwinViewC OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GVecHi OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GViewDrop2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GPotInit OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GPotName OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpShLoadU OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GGran OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GGranP OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GChk OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GBgNone OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GRoomA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GAncA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GCnt OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GCurA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GFmv.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UO UG CX.
Open Scope Z_scope.

Module UnpInstA.
Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs (XTP segs)) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Theorem g0a_sound : forall pc, contract_sound segs OPS MP PB (G0A.g0a_contract pc).
Proof. intros pc. exact (G0A.g0a_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.
Theorem g1a_sound : forall pc, contract_sound segs OPS MP PB (G1A.g1a_contract pc).
Proof. intros pc. exact (G1A.g1a_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.
Theorem g3pa_sound : forall pc, contract_sound segs OPS MP PB (G3PA.g3pa_contract pc).
Proof. intros pc. exact (G3PA.g3pa_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.
Theorem g4a_sound : forall pc rR rSZ, contract_sound segs OPS MP PB (G4A.g4a_contract pc rR rSZ).
Proof. intros pc rR rSZ. exact (G4A.g4a_sound pc rR rSZ segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.
Theorem ginva_sound : forall pc, contract_sound segs OPS MP PB (GInvA.ginva_contract pc).
Proof. intros pc. exact (GInvA.ginva_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem gbnda_sound : forall pc r, contract_sound segs OPS MP PB (GBndA.gbnd_contract pc r).
Proof. intros pc r. exact (GBndA.gbnd_sound pc r segs OPS MP PB). Qed.

Theorem gmid_sound : forall pc r, contract_sound segs OPS MP PB (GMid.gmid_contract pc r).
Proof. intros pc r. exact (GMid.gmid_sound pc r segs OPS MP PB). Qed.

Theorem gcnt_sound : forall pc r, contract_sound segs OPS MP PB (GCnt.gcnt_contract pc r).
Proof. intros pc r. exact (GCnt.gcnt_sound pc r segs OPS MP PB). Qed.

Theorem gfmv_sound : forall pc, contract_sound segs OPS MP PB (GFmv.GFmv.gfmv_contract segs pc).
Proof. intros pc. exact (GFmv.GFmv.gfmv_sound segs OPS MP PB pc). Qed.

Theorem gvea_sound : forall pc nf, contract_sound segs OPS MP PB (GVEndA.TwinB.GVEA.gvea_contract pc nf).
Proof. intros pc nf. exact (GVEndA.TwinB.GVEA.gvea_sound pc nf segs OPS MP PB). Qed.

Theorem gvea2_sound : forall pc nf, contract_sound segs OPS MP PB (GVEndA.TwinB.GVEA.gvea2_contract pc nf).
Proof. intros pc nf. exact (GVEndA.TwinB.GVEA.gvea2_sound pc nf segs OPS MP PB). Qed.

Theorem gvea3_sound : forall pc nf, contract_sound segs OPS MP PB (GVEndA.TwinB.GVEA.gvea3_contract pc nf).
Proof. intros pc nf. exact (GVEndA.TwinB.GVEA.gvea3_sound pc nf segs OPS MP PB). Qed.

Theorem gpothr_sound : forall pc c, contract_sound segs OPS MP PB (GPotHR.GPotHR.gpothr_contract pc c).
Proof. intros pc c. exact (GPotHR.GPotHR.gpothr_sound pc c segs OPS MP PB). Qed.

Theorem gcura_sound : forall pc, contract_sound segs OPS MP PB (GCurA.gcur_contract pc).
Proof. intros pc. exact (GCurA.gcur_sound pc segs OPS MP PB). Qed.

Theorem gnarrow_sound : forall pc, contract_sound segs OPS MP PB (GNarrow.gnarrow_contract pc).
Proof. intros pc. exact (GNarrow.gnarrow_sound pc segs OPS MP PB). Qed.

Theorem gtvc_carg_sound : forall pc i S, contract_sound segs OPS MP PB (GTwinViewC.gtvc_carg pc i S).
Proof. intros pc i S. exact (GTwinViewC.gtwinviewc_sound pc (GTwinViewC.sel_carg i) S segs OPS MP PB). Qed.
Theorem gtvc_reg_sound : forall pc r S, contract_sound segs OPS MP PB (GTwinViewC.gtvc_reg pc r S).
Proof. intros pc r S. exact (GTwinViewC.gtwinviewc_sound pc (GTwinViewC.sel_reg r) S segs OPS MP PB). Qed.

Theorem gvechi_sound : forall pc S ib ie, contract_sound segs OPS MP PB (GVecHi.gvechi_contract pc S ib ie).
Proof. intros pc S ib ie. exact (GVecHi.gvechi_sound pc S ib ie segs OPS MP PB). Qed.

Theorem gviewgc_sound : forall pc S, contract_sound segs OPS MP PB (GViewDrop2.gviewgc_contract pc S).
Proof. intros pc S. exact (GViewDrop2.gviewdrop_sound pc S GViewDrop2.mode_gc segs OPS MP PB). Qed.
Theorem gviewdrop_carg_sound : forall pc S i, contract_sound segs OPS MP PB (GViewDrop2.gviewdrop_carg_contract pc S i).
Proof. intros pc S i. exact (GViewDrop2.gviewdrop_sound pc S (GViewDrop2.mode_carg i) segs OPS MP PB). Qed.
Theorem gviewdrop_reg_sound : forall pc S r, contract_sound segs OPS MP PB (GViewDrop2.gviewdrop_reg_contract pc S r).
Proof. intros pc S r. exact (GViewDrop2.gviewdrop_sound pc S (GViewDrop2.mode_reg r) segs OPS MP PB). Qed.

Theorem ggran_sound : forall pc rs off, contract_sound segs OPS MP PB (GGran.ggran_contract pc rs off).
Proof. intros pc rs off. exact (GGran.ggran_sound pc rs off segs OPS MP PB). Qed.
Theorem ggranp_sound : forall pc rs off, contract_sound segs OPS MP PB (GGranP.ggranp_contract pc rs off).
Proof. intros pc rs off. exact (GGranP.ggranp_sound pc rs off segs OPS MP PB). Qed.

Theorem ggranl_sound : forall pc rs off, contract_sound segs OPS MP PB (GGranP.ggranl_contract pc rs off).
Proof. intros pc rs off. exact (GGranP.ggranl_sound pc rs off segs OPS MP PB). Qed.

Theorem grooma_sound : forall pc isV, contract_sound segs OPS MP PB (GRoomA.grooma_contract pc isV).
Proof. intros pc isV. exact (GRoomA.grooma_sound pc isV segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem ganca_sound : forall pc, contract_sound segs OPS MP PB (GAncA.GAncA.ganca_contract pc).
Proof. intros pc. exact (GAncA.GAncA.ganca_sound pc segs IMGX AW _ OPS HOPS MP PB). Qed.

Theorem gtwinbnd_sound : forall pc, contract_sound segs OPS MP PB (GTwinBnd.TwinB.GTwinBnd.gtwinbnd_contract pc).
Proof. intros pc. exact (GTwinBnd.TwinB.GTwinBnd.gtwinbnd_sound pc segs OPS MP PB). Qed.

Theorem gbgnone_sound : forall pc r, contract_sound segs OPS MP PB (GBgNone.gbgnone_contract pc r).
Proof. intros pc r. exact (GBgNone.gbgnone_sound pc r segs OPS MP PB). Qed.

Theorem gperm_vec_sound : forall pc, contract_sound segs OPS MP PB (GPerm.gperm_vec_contract pc).
Proof. intros pc. exact (UnpInst.gperm_sound segs IMGX AW OPS HOPS MP PB pc (GPerm.twin_of_carg 4%nat) (GPerm.twin_of_carg 1%nat)). Qed.

Theorem gcapb_sound : forall pc isV, contract_sound segs OPS MP PB (GCapB.TwinB.GCapB.gcapb_contract pc isV).
Proof. intros pc isV. exact (GCapB.TwinB.GCapB.gcapb_sound pc isV segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem gcapb2_sound : forall pc, contract_sound segs OPS MP PB (GCapB.TwinB.GCapB.gcapb2_contract pc).
Proof. intros pc. exact (GCapB.TwinB.GCapB.gcapb2_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem gexcl_sound : forall pc, contract_sound segs OPS MP PB (GExcl.GExcl.gexcl_contract pc).
Proof. intros pc. exact (GExcl.GExcl.gexcl_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem gpotinit_sound : forall pc, contract_sound segs OPS MP PB (GPotInit.gpotinit_contract pc).
Proof. intros pc. exact (GPotInit.gpotinit_sound pc segs IMGX AW (XTP segs) OPS HOPS MP PB). Qed.

Theorem gnamea_sound : forall pc, contract_sound segs OPS MP PB (GNameA.gnamea_contract pc).
Proof. intros pc. exact (GNameA.gnamea_sound pc segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS MP PB). Qed.
Theorem gpotname_sound : forall pc, contract_sound segs OPS MP PB (GPotName.gpotname_contract pc).
Proof. intros pc. exact (GPotName.gpotname_sound pc segs IMGX AW (unp_cw segs (XTP segs)) OPS HOPS MP PB). Qed.

Section Acc.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Theorem vd_acc_sound : forall pc cur beg lim s ng, contract_sound segs OPS MP PB (VDestroy.VD.vd_contract segs pc cur beg lim s ng).
Proof. intros pc cur beg lim s ng. exact (VDestroyA.TwinB.VDA.vd_sound_acc segs pc cur beg lim s ng OPS MP PB HMPA). Qed.

Theorem gchkl_sound : forall pc rs off pcok hv rl fuel, contract_sound segs OPS MP PB (GChk.GChk.gchkl_contract segs pc rs off pcok hv rl fuel).
Proof. intros pc rs off pcok hv rl fuel. exact (GChk.GChk.gchkl_sound segs pc rs off pcok hv rl fuel OPS MP PB HMPA). Qed.

Section ShLoad.
Variable CHS : list oinst -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis LAWS : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPS mo -> Forall (fun o => op_holds OPS (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CHS os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPS mo' /\
              Forall (fun o => op_holds OPS (fst o) (snd o) m mo') os.
Hypothesis SHLAW : forall os args md aw ws ca LB m mo cs c p,
  In (OPID, args) os -> decode args = Some (md, aw, ws, ca) ->
  aw_holds segs IMGX AW aw LB ws m mo -> windows_wf ws LB (aw_ceiling segs IMGX AW mo) ->
  Seal.seal_ok ws cs -> In c cs -> In (chunk_block c) LB ->
  (forall w, In w ws -> (w_kind w = K_BLOCK \/ K_GHOST <= w_kind w) -> forall a, in_iv (w_iv w) a -> ~ in_iv (chunk_block c) a) ->
  in_iv (chunk_block c) p ->
  m (Z_to_bv 64 (Seal.shadZ p)) = Some (Z_to_bv 8 0) /\ CHS os m mo (Seal.shadZ p).

Theorem opshloadu_sound : forall pc, contract_sound segs OPS MP PB (OpShLoadU.opshloadu_c segs pc).
Proof. exact (OpShLoadU.opshloadu_sound segs IMGX AW (XTP segs) OPS HOPS CHS LAWS SHLAW MP PB HMPA). Qed.
End ShLoad.
End Acc.
End Sound.
End UnpInstA.
End TwinB.
