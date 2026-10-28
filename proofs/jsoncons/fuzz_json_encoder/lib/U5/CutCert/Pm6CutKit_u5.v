(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition src0_cut_cert (itr : list (Z * nat)) (BFUEL : nat) (c : CC.cutpoint) (T : list CX.xop) (T2 : list CX.xop2) (p : SGP.splan) : bool :=
  SGP.cert_ok RSEGS (itab_of RSEGS itr) X_CPY X_SET X_LEN RO_LO RO_HI BFUEL A0 (CC.cp_nx c) [] (CX.xstepS RSEGS A0 T) (CX.xstep2 T2)
              (CC.cp_F c) (CC.cp_PSS c) p (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c).

Theorem src0_cut_plan_sound : forall itr BFUEL c T T2 p, src0_cut_cert itr BFUEL c T T2 p = true -> CC.plan_sound RSEGS c.
Proof.
  intros itr BFUEL c T T2 p Hc fx E R M HR HK.
  destruct (src0_plan_sound2 itr BFUEL (CC.cp_nx c) [] (CX.xstepS RSEGS A0 T) (CX.xstep2 T2) (CC.cp_F c) (CC.cp_PSS c) p (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c)
              Hc (fun M0 => CX.xstepS_ok A0 RSEGS (CC.cp_nx c) [] T (CC.cp_F c) M0 src0_in_hull src0_hull_ok) (fun M0 => CX.xstep2_ok RSEGS (CC.cp_nx c) [] T2 (CC.cp_F c) M0)
              fx E R M HR HK ltac:(constructor))
    as (fx' & E' & R' & M' & k & ps & Hps & Hag & Hms & Hregs & Hx0 & Hflat & Hfr & Hcells & Hgr).
  exists fx', E', R', M', k, ps. split; [exact Hps|]. split; [exact Hag|]. split; [exact Hms|].
  constructor; assumption.
Qed.
