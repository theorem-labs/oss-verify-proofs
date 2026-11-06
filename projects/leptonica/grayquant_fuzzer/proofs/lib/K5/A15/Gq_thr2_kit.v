(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Image.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_leaf Lept_chain LeptC_leaf Lept_objkit LeptL_kit D_iface D_defs
  Ed_fp Ed_fpkit Gq_numa Numa_kit Gq_gaps Gq_iface Gq_thr_iface Gq_parse_kit F_atof_kit.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac fold_reg k :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
    lazymatch v with
    | Some ?w =>
        tryif is_wlit w then idtac
        else tryif wclosed w then
          (let u := eval vm_compute in (bv_unsigned w) in change w with (Z_to_bv 64 u))
        else idtac
    | _ => idtac
    end
  end.
(* [comment removed for export] *)
Ltac fold_regs_ns := fold_reg 5; fold_reg 6; fold_reg 7; fold_reg 28; fold_reg 29; fold_reg 30; fold_reg 31;
                     fold_reg 10; fold_reg 11; fold_reg 12; fold_reg 13; fold_reg 14; fold_reg 15; fold_reg 16; fold_reg 17.
(* [comment removed for export] *)
Ltac nwalk1 := pwalk1; try fold_regs_ns.
Ltac nwalk stops := repeat (tryif at_stop stops then fail else nwalk1).
Ltac ppc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc | |- cps _ (ASTA _ _ _ (eq (MS _ _ ?pc _ _ _ _))) _ => idtac "CPS-PC:" pc | |- _ => idtac "OTHER GOAL" end.
(* [comment removed for export] *)
Ltac fstep_named :=
  step;
  lazymatch goal with |- evt _ _ (MS _ (bvmap_set ?k ?v ?F0) _ _ _ _ _) =>
    let Fn := fresh "Ff" in let En := fresh "EFf" in remember (bvmap_set k v F0) as Fn eqn:En end.
(* [comment removed for export] *)
Ltac flt_decide :=
  lazymatch goal with |- evt _ _ (MS _ ?Fb _ _ _ _ _) =>
  lazymatch goal with EFb : Fb = bvmap_set _ ?v4 ?Fa |- _ =>
  lazymatch goal with EFa : Fa = bvmap_set _ ?v5 ?F0 |- _ =>
    step;
    lazymatch goal with |- context [flt_s (reg_get Fb ?r14) (reg_get Fb ?r15)] =>
      replace (reg_get Fb r14) with v4 by (rewrite EFb; symmetry; apply freg_get_same; reflexivity);
      replace (reg_get Fb r15) with v5 by (rewrite EFb, freg_get_other by reflexivity; rewrite EFa; symmetry; apply freg_get_same; reflexivity)
    end;
    replace (flt_s v4 v5) with false by (vm_compute; reflexivity);
    clear EFa EFb; try clear Fa; try clear F0
  end end end.
