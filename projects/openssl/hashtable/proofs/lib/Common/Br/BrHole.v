(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxImage FxRun FxRn FxHandoff.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cx Require Import CxPlan CxPlanSound.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrRev BrClass BrRevS BrDress BrTrans.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Hole.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, CXS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : CXS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CAP.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variable nx0 : nat.
Hypothesis NX0_spw : CAP.expr_vars_lt nx0 CAP.e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), AxSymRun3.env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, AxSymRun3.env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

Definition fx_hole (START END : CAP.acs) : Prop :=
  forall E R FULL m (T : ShapeAlgBase.TSet),
    CXS.cs_ok segs A Lim SINV argH ISP FS0 E START R FULL m ->
    (forall E1 R1 FULL1 m1,
       AxSymRun3.env_agree (CAP.nxt START) E E1 ->
       CXS.cs_ok segs A Lim SINV argH ISP FS0 E1 END R1 FULL1 m1 ->
       m_fs m1 = m_fs m ->
       realizes_cfg cfg segs (CXS.cfg_of segs R1 (AX2.s_pc (CAP.a_ss END)) FULL1 m1) T) ->
    realizes_cfg cfg segs (CXS.cfg_of segs R (AX2.s_pc (CAP.a_ss START)) FULL m) T.

Theorem fx_hole_chk TT n shapes cuts classes START d bs bp k F' r cnt VT END :
  tr_check IM A nx0 TT n shapes cuts classes START d bs F' VT
           (AX2.s_pc (CAP.a_ss END)) (AX2.s_regs (CAP.a_ss END)) (CAP.kn END) = true ->
  side_chk A TT (CAP.kn START) d = true ->
  (k <= 61)%nat ->
  fx_run IM code bp k (dress (state_of d) bs) = (F', r, cnt) ->
  tr_state START (AX2.s_pc (CAP.a_ss END)) (AX2.s_regs (CAP.a_ss END)) (CAP.kn END) (CAP.nxt END) = END ->
  fx_hole START END.
Proof.
  intros Hchk Hside Hk Hrun Eend E R FULL m T HCS HK.
  apply (fx_transform_chk cfg segs IM code Hcode HIM HWR A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high
           nx0 NX0_spw argH_agree SINV_agree SINV_frame TT n shapes cuts classes START d bs bp k F' r cnt VT
           (AX2.s_pc (CAP.a_ss END)) (AX2.s_regs (CAP.a_ss END)) (CAP.kn END) (CAP.nxt END) E R FULL m T
           HCS Hchk Hside Hk Hrun).
  intros E1 R1 FULL1 m1 Hag HCS1 Hfs. rewrite Eend in HCS1. exact (HK E1 R1 FULL1 m1 Hag HCS1 Hfs).
Qed.
End Hole.
