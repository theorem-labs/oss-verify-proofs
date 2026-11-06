(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Lemma tm_okF_mem : forall segs T E M rom ms, ST.tm_okF segs T E M rom ms -> ms_mem ms = M.
Proof.
  intros segs T E M rom ms (_ & _ & regs & Hms & _). rewrite Hms. cbn [ST.tstate s_log mem_denot]. reflexivity.
Qed.

Lemma summ_okH_of_ok : forall GP (S : SP.summ), SP.sm_PS S = None -> SP.summ_ok psegs GP S ->
  SP.summ_okH psegs GP MMP.hmH MMP.hmA MMP.hmC MMP.hmR S.
Proof.
  intros GP S HPS HS E M rom ms _ HAG _ HHM HT HG.
  destruct (HS E M rom ms HAG HT HG) as (ms' & X & E' & M' & HmsF & HinX & HX & HGX & Hg & Hb & FR).
  exists ms', X, E', M'. split; [exact HmsF|]. split; [exact HinX|]. split; [exact HX|]. split; [exact HGX|].
  split; [exact Hg|]. split; [exact Hb|]. split.
  - unfold MMP.hmH in *. pose proof (ExecF.mstepsF_msteps psegs _ _ _ HmsF) as Hms.
    pose proof (msteps_wrel psegs _ _ Hms) as HW. rewrite (tm_okF_mem _ _ _ _ _ _ HT), (tm_okF_mem _ _ _ _ _ _ HX) in HW.
    exact (wrel_mem_inv psegs _ _ HW HHM).
  - unfold SP.frame_ok. rewrite HPS. exact FR.
Qed.
Print Assumptions summ_okH_of_ok.
