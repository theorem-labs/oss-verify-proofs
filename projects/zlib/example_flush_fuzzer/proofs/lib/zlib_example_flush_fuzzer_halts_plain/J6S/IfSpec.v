(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout InffastModel InffastCtx InffastSafe.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Definition if_kept : list reg := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition FPOST (segs : list Segment) (LFX DFX : Z) (MSGA : Z -> Z)
           (mem : word -> option byte) (sp : Z) (c : icall) (r : iregs) (ZP S I0 P0 WB : Z)
           (m' : word -> option byte) (w' : iw) : Prop :=
  let ON := arr_len (ic_outbuf c) in
  let c' := w_c w' in let s' := w_s w' in
  w_r w' = r /\ ic_input c' = ic_input c
  /\ (ic_total_in c' = ic_total_in c /\ ic_total_out c' = ic_total_out c /\ ic_adler c' = ic_adler c /\ ic_data_type c' = ic_data_type c)
  /\ arr_len (ic_outbuf c') = ON /\ (forall i, 0 <= i < ON -> 0 <= arr_get (ic_outbuf c') i < 256)
  /\ cells segs m' P0 1 1 ON (arr_get (ic_outbuf c'))
  /\ cell segs m' (ZP + 0) 8 (I0 + ic_next_in c') /\ cell segs m' (ZP + 8) 4 (ic_avail_in c')
  /\ cell segs m' (ZP + 24) 8 (P0 + ic_next_out c') /\ cell segs m' (ZP + 32) 4 (ic_avail_out c')
  /\ isl_scalars segs LFX DFX m' S (ISP ZP WB) s'
  /\ cell segs m' (ZP + 48) 8 (MSGA (ic_msg c'))
  /\ agree_out (FFall sp P0 ON ZP S) mem m' /\ (forall x, mem x <> None -> m' x <> None)
  /\ 0 <= ic_next_in c' <= arr_len (ic_input c) /\ 0 <= ic_next_out c' <= ON
  /\ 0 <= is_hold s' < 2 ^ is_bits s' /\ 0 <= is_bits s' < 8.

Definition inflate_fast_spec_at (segs : list Segment) (LFX DFX RLO RHI WLO ENTRY : Z) (MSGA : Z -> Z) : Prop :=
  forall (mem : word -> option byte) (sp : Z) (ra : word) (s : inflate_state) (c : icall) (r : iregs)
         (ZP S I0 P0 WB : Z) (regs : bvmap 5 word),
    iff_pre segs LFX DFX RLO RHI WLO mem sp ra s c r ZP S I0 P0 WB ->
    cell segs mem (ZP + 48) 8 (MSGA (ic_msg c)) ->
    0 <= ir_out r < 2 ^ 32 ->
    getr regs 1 = ra -> getr regs 2 = zw (sp + 112) -> getr regs 10 = zw ZP -> getr regs 11 = zw (ir_out r) ->
    ff_ok s c r = true ->
    exists R m',
      msteps segs (mkst regs (zw ENTRY) mem (seg_rom segs)) (mkst R ra m' (seg_rom segs))
      /\ getr R 2 = zw (sp + 112)
      /\ (forall k : reg, In k if_kept -> getr R k = getr regs k)
      /\ FPOST segs LFX DFX MSGA mem sp c r ZP S I0 P0 WB m' (inflate_fast (mkW s c r)).
End FXG.
