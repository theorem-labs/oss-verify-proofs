(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfB_loop0.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Hypothesis PAYR : Forall (fun c => 0 <= c < 256) payload.

  Notation KDISPB cx ly B := (KDISP cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation KLV cx ly := (KLEAVE cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh).
  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation ARMSOK cx ly := (arms_ok AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).
  Notation KDP P cx ly B := (KDISP_P AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh P cx ly B).

  Lemma kdisp_step_B : forall cx ly B, inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KLV cx ly -> ARMSOK cx ly -> KDISPB cx ly B -> KDP modesB cx ly (B + 1).
  Proof.
    intros cx ly B CTX PLEN KL ARMS KD. unfold KDISP_P, DISP_MS, L_DISP. intros until m. intros CASES SI ME ARR VIS HID.
    assert (KA : KALLB cx ly (meas cx st)).
    { apply kall_of_kdisp; [exact CTX| exact PLEN| exact KL|]. eapply kdisp_mono; [| exact KD]. lia. }
    clear KD.
    unfold modesB in CASES.
    inf_arm_open.
    destruct ARMS as (A_HEAD & A_DICTID & A_DICT & A_TYPE & A_TYPEDO & A_STORED & A_COPY_ & A_COPY & A_TABLE & A_LENLENS & A_CODELENS & A_LEN_ & A_LEN & A_LENEXT & A_DIST & A_DISTEXT & A_MATCH & A_LIT & A_CHECK & A_LENGTH).
    cbv [HEAD DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM] in CASES, MNE.
    Local Ltac disp Lb := zrunb [Lb].
    Local Ltac arm A :=
      lazymatch goal with
      | SI : sinv ?cx0 ?st0 ?lf0 ?cf0, KA : KALL ?cx0 ?ly0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          eapply (A st0 lf0 cf0);
            [ lazymatch goal with H : inf_ctx _ _ _ _ _ |- _ => exact H end | assumption | assumption | reflexivity | exact SI | eassumption
            | inf_vis_close | inf_hid_close | exact KA ]
      end.
    decompose [or] CASES; clear CASES; match goal with Hc : mode = _ |- _ => rewrite Hc in *; clear Hc; try clear mode end.
    - disp 0x91730. arm A_LEN_.
    - disp 0x9174c. arm A_LEN.
    - disp 0x8e74c. arm A_LENEXT.
    - disp 0x91d9c. arm A_DIST.
    - disp 0x8e72c. arm A_DISTEXT.
    - disp 0x92318. arm A_MATCH.
    - disp 0x8ec00. arm A_LIT.
    - disp 0x8eea4. arm A_CHECK.
    - disp 0x90a4c. arm A_LENGTH.
    -
      zrunb [0x93758].
      destruct KA as (_ & _ & _ & KLV0).
      eapply (KLV0 (IST 16208 last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) 1 lf cf wf fo);
        [exact SI| exact ARR| inf_vis_close| inf_hid_close].
    -
      zrunb [0x93758].
      destruct KA as (_ & _ & _ & KLV0).
      eapply (KLV0 (IST 16209 last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) (-3) lf cf wf fo);
        [exact SI| exact ARR| inf_vis_close| inf_hid_close].
    - exfalso. lia.
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
