(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfAGlue_p04.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
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

  Theorem lit_arm : forall cx ly, arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8e814 LIT.
  Proof.
    intros cx ly. unfold arm_stmtA, ARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    pose proof KA as (KD & KB & KL & KLV).
    inf_arm_open.
    destruct (pay_out_sep _ _ _ _ _ CTX0) as (cOD & COD0 & COD1 & COD2). cbn [c_q c_n] in COD1, COD2.
    clear R13.
    zs. zs. zbr0 KLEFT.
    2: {
      zs.
      eapply (KL (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI| exact ARR| exact VISf| exact HID]. }
    zrunb [0x8e84c].
    assert (SOK : store_ok asegs m (Z_to_bv 64 (6336512 + cout)) 1 = true)
      by (eapply (f8arr_store_ok asegs m 6336512 (Z.to_nat osz) fo cout); [exact OUT| lia| reflexivity]).
    zstep.
    destruct (out_write asegs m 6336512 (Z.to_nat osz) fo cout (le1 (sx32 (Z_to_bv 64 len))) OUT ltac:(lia) (length_le1 _)) as (fo' & OUT' & FOR').
    store_done.
    zrunb [0x8e2dc].
    destruct (sinv_upd _ _ _ _ LEN 1 len SI (or_intror MODE) ltac:(lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(icx_cbn; lia) (or_intror eq_refl)) as (SI' & ME').
    replace (6336512 + cout + 1) with (6336512 + (cout + 1)) in * by lia. replace (osz - cout + -1) with (osz - (cout + 1)) by lia.
    eapply (KD (st_upd (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) LEN 1 len) lf cf wf fo');
      [exact SI'| exact ME'| destruct ARR as [AW _]; split; [exact AW| intros i _; apply FOR']| change LEN with 16200; unfold st_upd; inf_vis_close| inf_hid_close].
    (* v240 is a vestige binder of KDISP at 1.4 (InfABase's inf_locals no longer holds it), so
       eapply leaves it as a shelved word; any value does *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
