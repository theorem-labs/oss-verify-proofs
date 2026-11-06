(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RF_memset RF_memcpy RF_fwritex RF_pad RF_stdio_lib RF_pop_arg R_Exit Printf_model Printf_mlib RF_printf_iface RF_printf_core RF_vfprintf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_pieces.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.  (* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Export RF_vfprintf_stdout1.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Stdout.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.
  Hypothesis FWX : fwritex_stdout_stmt.

  Let OUT := stdout_fwritex get_so set_so.
  Let SINK := SINK_stdout (St:=St) get_so.

  (* [comment removed for export] *)
  Local Notation vfprintf_stdout_post := (RF_vfprintf_stdout1.vfprintf_stdout_post get_so).
  Local Notation vfprintf_stdout_stmt := (RF_vfprintf_stdout1.vfprintf_stdout_stmt get_so set_so).
  Local Notation vfp_stdout_active := (RF_vfprintf_stdout1.vfp_stdout_active get_so set_so GS SS FWX).
  Local Notation vfp_stdout_inactive := (RF_vfprintf_stdout1.vfp_stdout_inactive get_so set_so GS SS FWX).

  (* [comment removed for export] *)
  Lemma vfp_stdout_after_prologue :
    forall (ra : word) (sp : word) (gp : word) (tp : word) (t0 : word) (t1 : word) (t2 : word) (s0 : word) (s1 : word) (a3 : word) (a4 : word) (a5 : word) (a6 : word) (a7 : word) (s2 : word) (s3 : word) (s4 : word) (s5 : word) (s6 : word) (s7 : word) (s8 : word) (s9 : word) (s10 : word) (s11 : word) (t3 : word) (t4 : word) (t5 : word) (t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (A : Z) (VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (lo : Z) (canary : word) (flags : word) (mode : word) (tail : list byte) (bufbytes : list byte) (m0 : mem),
    (rw_cells rsegs m0 150256 [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 106548); C8 (Z_to_bv 64 (if so_active (get_so st) then 349208 + 1024 else 0)); C8 (Z_to_bv 64 (if so_active (get_so st) then 349208 + zlength (so_buf (get_so st)) else 0)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (if so_active (get_so st) then 349208 else 0)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (if so_first (get_so st) then 107000 else 106592)); C8 (Z_to_bv 64 106992); C8 (Z_to_bv 64 349208); C8 (Z_to_bv 64 1024); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 (if so_lbf_nl (get_so st) then 10 else 4294967295)); C4 (Z_to_bv 64 0); CB 80 tail]) ->
    (Z.land (bv_unsigned flags) 72 = 0) ->
    (rw_cells rsegs m0 349208 [CB 1024 bufbytes]) ->
    (firstn (length (so_buf (get_so st))) bufbytes = to_bytes (so_buf (get_so st))) ->
    (zlength (so_buf (get_so st)) <= 1024) ->
    (so_active (get_so st) = false → so_buf (get_so st) = []) ->
    (bytes_at rsegs m0 A (zb fmt)) ->
    (Forall (λ c : Z, 0 <= c < 256) fmt) ->
    (pass1_ok fmt = true) ->
    (bytes_at rsegs m0 VA (u64s slots)) ->
    (args_ok 150256 349208 1024 m lo (bv_unsigned sp) (bv_unsigned sp + -368) slots args) ->
    (printf_pieces fmt args = Some (ps, r)) ->
    (fp_calls (length fmt) fmt args = []) ->
    (lo <= bv_unsigned sp - 5552) ->
    (352256 <= lo) ->
    (bv_unsigned sp < 0x800000000000) ->
    (rw_cells rsegs m0 145704 [C8 (Z_to_bv 64 348080)]) ->
    (rw_cells rsegs m0 348080 [C8 canary]) ->
    (mem_inv rsegs m0) ->
    (frm0 fc) ->
    (65536 <= A) ->
    (A + Z.of_nat (length fmt) <= 131072) ->
    (bv_unsigned sp <= VA) ->
    (VA + 8 * Z.of_nat (length slots) <= 2 ^ 64) ->
    (0 <= bv_unsigned sp < 2 ^ 64) ->
    (0 <= A ∧ A + Z.of_nat (length fmt) <= 2 ^ 64) ->
    (length (zb fmt) = length fmt) ->
    (length (u64s slots) = (8 * length slots)%nat) ->
    (munch [(lo, bv_unsigned sp); (150256, 150256 + 232); (349208, 349208 + 1024)] m m0) ->
    (wmono rsegs m m0) ->
    (munch [(lo, bv_unsigned sp); (150256, 150256 + 232)] m m0) ->
    (length bufbytes = 1024%nat) ->
    (stk rsegs m0 lo (bv_unsigned sp + -368)) ->
     forall (junk : list byte),
    (rw_cells rsegs m0 (bv_unsigned sp + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 248 (firstn 248 (firstn 280 (skipn 16 (firstn 304 (firstn 312 (firstn 320 (firstn 328 (firstn 336 (firstn 344 (firstn 352 (firstn 360 junk))))))))))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
    evt rsegs (λ ms' : machine_state, impl rsegs (at_node rsegs) ((printf_model OUT OUTFP_stdout fmt args;;; mret ()) (set_so (if so_active (get_so st) then get_so st else {| so_active := true; so_buf := []; so_lbf_nl := so_lbf_nl (get_so st); so_first := so_first (get_so st) |}) st)) (epost (λ p : () * St, vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m p.1 p.2)) ms') (MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some t6) TEmpty) (Some a5) TEmpty) (Some t2) (TNode TEmpty (Some s7) TEmpty)) (Some gp) (TNode (TNode TEmpty (Some s3) TEmpty) (Some (Z_to_bv 64 A)) (TNode TEmpty (Some s11) TEmpty))) (Some (Z_to_bv 64 107264)) (TNode (TNode (TNode TEmpty (Some a7) TEmpty) (Some (Z_to_bv 64 A)) (TNode TEmpty (Some s9) TEmpty)) (Some t0) (TNode (TNode TEmpty (Some s5) TEmpty) (Some (Z_to_bv 64 (bv_unsigned sp + -272))) (TNode TEmpty (Some t4) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some a6) TEmpty) (Some (Z_to_bv 64 150256)) (TNode TEmpty (Some s8) TEmpty)) (Some tp) (TNode (TNode TEmpty (Some s4) TEmpty) (Some (Z_to_bv 64 (bv_unsigned sp + -368))) (TNode TEmpty (Some t3) TEmpty))) (Some (Z_to_bv 64 (bv_unsigned sp + -368))) (TNode (TNode (TNode TEmpty (Some (Z_to_bv 64 348080)) TEmpty) (Some (Z_to_bv 64 0)) (TNode TEmpty (Some s10) TEmpty)) (Some t1) (TNode (TNode TEmpty (Some s6) TEmpty) (Some (Z_to_bv 64 (bv_unsigned sp + -104))) (TNode TEmpty (Some t5) TEmpty))))) F (Z_to_bv 64 107592) fc None m0 (seg_rom rsegs)).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st A VA fmt slots args ps r lo canary flags mode tail bufbytes m0 FC FL72 BUF PFX BLEN INACT BY HF P1 VAA AOK PP FPC LO GLO QHI SSP1 SSP2 MI FRM HA0 HA QVA VAHI Rq AB LZB LU MU WM MU1 LBB ST junk FR.

    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evt_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
    cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [rsegs] in SSP1, SSP2. fold rsegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit. zs. zs. zs.
    destruct (so_active (get_so st)) eqn:ACT.
    - (* [comment removed for export] *)
      eapply vfp_stdout_active; eassumption.
    - (* [comment removed for export] *)
      eapply vfp_stdout_inactive; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma vfp_stdout_after12 :
    forall (ra : word) (sp : word) (gp : word) (tp : word) (t0 : word) (t1 : word) (t2 : word) (s0 : word) (s1 : word) (a3 : word) (a4 : word) (a5 : word) (a6 : word) (a7 : word) (s2 : word) (s3 : word) (s4 : word) (s5 : word) (s6 : word) (s7 : word) (s8 : word) (s9 : word) (s10 : word) (s11 : word) (t3 : word) (t4 : word) (t5 : word) (t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (A : Z) (VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (lo : Z) (canary : word) (flags : word) (mode : word) (tail : list byte) (bufbytes : list byte) (m0 : mem),
    (rw_cells rsegs m0 150256 [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 106548); C8 (Z_to_bv 64 (if so_active (get_so st) then 349208 + 1024 else 0)); C8 (Z_to_bv 64 (if so_active (get_so st) then 349208 + zlength (so_buf (get_so st)) else 0)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (if so_active (get_so st) then 349208 else 0)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (if so_first (get_so st) then 107000 else 106592)); C8 (Z_to_bv 64 106992); C8 (Z_to_bv 64 349208); C8 (Z_to_bv 64 1024); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 (if so_lbf_nl (get_so st) then 10 else 4294967295)); C4 (Z_to_bv 64 0); CB 80 tail]) ->
    (Z.land (bv_unsigned flags) 72 = 0) ->
    (rw_cells rsegs m0 349208 [CB 1024 bufbytes]) ->
    (firstn (length (so_buf (get_so st))) bufbytes = to_bytes (so_buf (get_so st))) ->
    (zlength (so_buf (get_so st)) <= 1024) ->
    (so_active (get_so st) = false → so_buf (get_so st) = []) ->
    (bytes_at rsegs m0 A (zb fmt)) ->
    (Forall (λ c : Z, 0 <= c < 256) fmt) ->
    (pass1_ok fmt = true) ->
    (bytes_at rsegs m0 VA (u64s slots)) ->
    (args_ok 150256 349208 1024 m lo (bv_unsigned sp) (bv_unsigned sp + -368) slots args) ->
    (printf_pieces fmt args = Some (ps, r)) ->
    (fp_calls (length fmt) fmt args = []) ->
    (lo <= bv_unsigned sp - 5552) ->
    (352256 <= lo) ->
    (bv_unsigned sp < 0x800000000000) ->
    (rw_cells rsegs m0 145704 [C8 (Z_to_bv 64 348080)]) ->
    (rw_cells rsegs m0 348080 [C8 canary]) ->
    (mem_inv rsegs m0) ->
    (frm0 fc) ->
    (65536 <= A) ->
    (A + Z.of_nat (length fmt) <= 131072) ->
    (bv_unsigned sp <= VA) ->
    (VA + 8 * Z.of_nat (length slots) <= 2 ^ 64) ->
    (0 <= bv_unsigned sp < 2 ^ 64) ->
    (0 <= A ∧ A + Z.of_nat (length fmt) <= 2 ^ 64) ->
    (length (zb fmt) = length fmt) ->
    (length (u64s slots) = (8 * length slots)%nat) ->
    (munch [(lo, bv_unsigned sp); (150256, 150256 + 232); (349208, 349208 + 1024)] m m0) ->
    (wmono rsegs m m0) ->
    (munch [(lo, bv_unsigned sp); (150256, 150256 + 232)] m m0) ->
    (length bufbytes = 1024%nat) ->
    (stk rsegs m0 lo (bv_unsigned sp + -368)) ->
     forall (junk : list byte),
    (rw_cells rsegs m0 (bv_unsigned sp + -368) [CB 312 (firstn 312 (firstn 320 (firstn 328 (firstn 336 (firstn 344 (firstn 352 (firstn 360 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
    evt rsegs (λ ms' : machine_state, impl rsegs (at_node rsegs) ((printf_model OUT OUTFP_stdout fmt args;;; mret ()) (set_so (if so_active (get_so st) then get_so st else {| so_active := true; so_buf := []; so_lbf_nl := so_lbf_nl (get_so st); so_first := so_first (get_so st) |}) st)) (epost (λ p : () * St, vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m p.1 p.2)) ms') (MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some t6) TEmpty) (Some a5) TEmpty) (Some t2) (TNode TEmpty (Some s7) TEmpty)) (Some gp) (TNode (TNode TEmpty (Some s3) TEmpty) (Some (Z_to_bv 64 A)) (TNode TEmpty (Some s11) TEmpty))) (Some ra) (TNode (TNode (TNode TEmpty (Some a7) TEmpty) (Some (Z_to_bv 64 A)) (TNode TEmpty (Some s9) TEmpty)) (Some t0) (TNode (TNode TEmpty (Some s5) TEmpty) (Some a3) (TNode TEmpty (Some t4) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some a6) TEmpty) (Some (Z_to_bv 64 150256)) (TNode TEmpty (Some s8) TEmpty)) (Some tp) (TNode (TNode TEmpty (Some s4) TEmpty) (Some (Z_to_bv 64 VA)) (TNode TEmpty (Some t3) TEmpty))) (Some (Z_to_bv 64 (bv_unsigned sp + -368))) (TNode (TNode (TNode TEmpty (Some (Z_to_bv 64 348080)) TEmpty) (Some (Z_to_bv 64 144064)) (TNode TEmpty (Some s10) TEmpty)) (Some t1) (TNode (TNode TEmpty (Some s6) TEmpty) (Some a4) (TNode TEmpty (Some t5) TEmpty))))) F (Z_to_bv 64 107208) fc None m0 (seg_rom rsegs)).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st A VA fmt slots args ps r lo canary flags mode tail bufbytes m0 FC FL72 BUF PFX BLEN INACT BY HF P1 VAA AOK PP FPC LO GLO QHI SSP1 SSP2 MI FRM HA0 HA QVA VAHI Rq AB LZB LU MU WM MU1 LBB ST junk FR.

    do 14 zs.
    eapply vfp_stdout_after_prologue; eassumption.
  Qed.
End Stdout.
End RC__1.
