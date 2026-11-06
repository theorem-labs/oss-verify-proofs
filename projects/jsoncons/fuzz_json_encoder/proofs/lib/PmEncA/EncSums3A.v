(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface HeapIfaceA L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ESA3.
Definition cp4_xsumA (pc scr : Z) (breg : nat) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 0%nat
    (fun regs _ => Some (APC.eaddz (nth 10 regs (ELit 0)) 1))
    (fun regs => let '(ob, ok) := split_lit (nth 12 regs (ELit 0)) in [(ob, ok - ok mod 8, ELit 8)])
    (fun regs BL => BL)
    (fun regs cells g BLk => let '(ob, ok) := split_lit (nth 12 regs (ELit 0)) in
       (KWord (SA ob ok) 4 (nth breg regs (ELit 0)) :: KRange (EVar (g + 5)) 0 0 :: ESA.STATICS, BLk))
    (fun F => F)) (fun _ => []).
End ESA3.
