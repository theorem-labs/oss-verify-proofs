(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_w7d InfAGlue_w7 InfPure_table InfPure_codelens.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7pull InfB_w6base InfB_w6kit InfB_w6garm InfB_cldone_base InfB_clbase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint_hyp := lazymatch goal with |- acc_in ?R ?x => match goal with HA : acc_in R x |- _ => exact HA end end.
Local Ltac acc_hint ::= first [ acc_hint_hyp | acc_hint_sh ].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation GARM2 cx ly Lb X := (garm2_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Notation CLH cx ly N := (clhead_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).
  Notation CLD cx ly := (cldone_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh).

  Theorem codelens_entry : forall cx ly, (forall N, CLH cx ly N) -> CLD cx ly -> GARM2 cx ly 0x8f7ec CODELENS.
  Proof.
    intros cx ly HEAD DONE. unfold garm2_stmtA, GARM2_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    destruct (cl_facts _ _ _ _ SI MODE) as (NL1 & NL2 & ND1 & ND2 & SH0 & SH1 & L15 & LC0 & LB1 & LB15 & NX0 & NX1 & TOK & RLF & RCF).
    revert HEAD DONE. inf_arm_open. intros HEAD DONE.
    subst lc.
    zrung [0x8f858].
    replace (ndist + nlen) with (nlen + ndist) by (clear; lia).
    zs. zbr0 KD.
    -
      eapply (DONE (IST mode last flags cin cout hold bits out ret len offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact CTX0| exact PAYR| exact PLEN| exact MODE| clear - KD; gcbn; lia| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA].
    -
      zrung [0x8f8a8].
      setreg 5 (Z_to_bv 64 (S + 1384)) ltac:(unfold cp_addrA; f_equal; clear; lia).
      rewrite !(zx32_small lb) by (clear - LB1 LB15; lia). rewrite ?unsigned_lit by (clear - LB1 LB15; lia).
      rewrite mask_sllw by (clear - LB1 LB15; lia).
      eapply (HEAD (Z.to_nat (nlen + ndist - shave)) (IST mode last flags cin cout hold bits out ret len offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [clear; gcbn; lia| clear - KD; gcbn; lia| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
