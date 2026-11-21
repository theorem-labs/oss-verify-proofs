(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_w7d InfAGlue_w7 InfPure_table InfPure_codelens.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab InfA_w7pull InfA_w6base InfA_w6kit InfA_cldone_base InfA_clbase InfA_clbase2 InfA_clreg InfA_cldec InfA_clsym InfA_clfill InfA_clr16 InfA_clr17 InfA_clr18.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation GARM2 cx ly Lb X := (garm2_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Notation CLH cx ly N := (clhead_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).
  Notation CLD cx ly := (cldone_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh).

  Theorem codelens_entry : forall cx ly, (forall N, CLH cx ly N) -> CLD cx ly -> GARM2 cx ly 0x8f4cc CODELENS.
  Proof.
    intros cx ly HEAD DONE. unfold garm2_stmtA, GARM2_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    destruct (cl_facts _ _ _ _ SI MODE) as (NL1 & NL2 & ND1 & ND2 & SH0 & SH1 & L15 & LC0 & LB1 & LB15 & NX0 & NX1 & TOK & RLF & RCF).
    revert HEAD DONE. inf_arm_open. intros HEAD DONE.
    subst lc.
    zrunb [0x8f530].
    replace (ndist + nlen) with (nlen + ndist) by (clear; lia).
    zs. zbr0 KD.
    -
      eapply (DONE (IST mode last flags cin cout hold bits out ret len offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact CTX0| exact PAYR| exact PLEN| exact MODE| clear - KD; gcbn; lia| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA].
    -
      zrunb [0x8f56c].
      setreg 16 (Z_to_bv 64 (S + 1384)) ltac:(unfold cp_addrA; f_equal; clear; lia).
      rewrite (zx32_small lb) by (clear - LB1 LB15; lia).
      eapply (cl_mask RNG POST) with (lb := lb); [clear - LB1 LB15; lia|]. intros x11' x13'.
      zs. (* 1.4 reloads next_in into t3 from frame slot 496 (0x8f54c), stored at 0x8f49c *)
      eapply (HEAD (Z.to_nat (nlen + ndist - shave)) (IST mode last flags cin cout hold bits out ret len offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [clear; gcbn; lia| clear - KD; gcbn; lia| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.
  Lemma cl_loop : forall (N : nat) (cx : ictx) (ly : ilay), CLD cx ly -> CLH cx ly N.
  Proof.
    induction N as [|N IH]; intros cx ly DONE.
    - unfold clhead_stmt. intros until m. intros HN HJN. exfalso. clear - HN HJN. lia.
    - apply (cl_head AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N cx ly).
      pose proof (cl_next AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N cx ly (IH cx ly DONE) DONE) as HNEXT.
      pose proof (cl_chk AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N cx ly HNEXT) as HCHK.
      apply (cl_res AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N cx ly HNEXT).
      + exact (cl_rep16 AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N cx ly HCHK).
      + exact (cl_rep17 AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N cx ly HCHK).
      + exact (cl_rep18 AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N cx ly HCHK).
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.

  Theorem codelens_garm2 : forall cx ly, CLD cx ly -> GARM2 cx ly 0x8f4cc CODELENS.
  Proof. intros cx ly DONE. apply codelens_entry; [intros N; apply cl_loop; exact DONE| exact DONE]. Qed.

  Theorem codelens_garm : forall cx ly, CLD cx ly -> garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8f4cc CODELENS.
  Proof. intros cx ly DONE. apply garm2_garm. apply codelens_garm2. exact DONE. Qed.
End S.
End CANSEC1.
