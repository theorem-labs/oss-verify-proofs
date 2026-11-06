(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode SysStep Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue F_uselocale.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

Definition WUNSH : Z := 0xa40b0.
Definition USELOC_RA1 : Z := 0xa40e0.
Definition USELOC_RA2 : Z := 0xa4108.
Definition CLOC : Z := 0x24c18.
Definition TPLOC : Z := 0xe9d68.
Definition GLOC : Z := 0x10a060.
Definition RTP_ : Z := 0xe9d98.
Definition WUNSH_DEPTH : Z := 64.

Definition wunshift_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (E X lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp + -64, bv_unsigned sp); (E, E + 8); (TPLOC, TPLOC + 8)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' E [C8 (Z_to_bv 64 X)]
    /\ rw_cells psegs m' TPLOC [C8 (Z_to_bv 64 GLOC)].

Lemma wunshift_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (CV E X lo : Z) (j : list byte),
  a0 = Z_to_bv 64 CV -> rw_cells psegs m (CV + 16) [C8 (Z_to_bv 64 CLOC)] -> (0 < CV) -> (CV + 24 <= lo) ->
  a4 = Z_to_bv 64 E -> a2 = Z_to_bv 64 X -> a3 = Z_to_bv 64 (X + 8) -> rw_cells psegs m E [CB 8 j] -> (0 <= X) -> (X + 16 < 2^64) ->
  (bv_unsigned sp <= E) -> (E + 8 < 2^63) ->
  tp = Z_to_bv 64 RTP_ -> rw_cells psegs m TPLOC [C8 (Z_to_bv 64 GLOC)] ->
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - WUNSH_DEPTH) -> (GLOBALS_TOP <= lo) ->
  mem_inv psegs m ->
  evt psegs (wunshift_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc E X lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 WUNSH) fc None m (seg_rom psegs)).
Proof.
  intros until j. intros -> CVL CV0 CVH -> -> -> CE X0 XH ES EH -> TPL ST LO GLO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold WUNSH, WUNSH_DEPTH, GLOBALS_TOP, CLOC, TPLOC, GLOC, RTP_ in *.
  pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (E, E + 8); (0xe9d68, 0xe9d68 + 8)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  carve_frame 64%nat ST.
  do 6 lstep.
  lstep. lstep. lstep.
  lstep.
  lstep.
  lstep.
  name_sp sp (-64)%Z. replace (bv_unsigned sp + -64) with (bv_unsigned sp0) in ST, FR by lia.
  call (uselocale_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1089632 150552);
    [ first [reflexivity | lia | eassumption] .. | ].
  Ltac eval_post H := cbn [usel_ret usel_new] in H;
    match type of H with rw_cells _ _ _ [C8 (Z_to_bv 64 ?v)] => let v' := eval vm_compute in v in replace v with v' in H by (vm_compute; reflexivity) end.
  Ltac eval_a0 := cbn [usel_ret usel_new];
    match goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      let v' := eval vm_compute in v in replace v with v' by (vm_compute; reflexivity) end.
  eval_post POST. eval_a0. rename POST into TPL1.
  lstep. lstep.
  lstep. lstep. lstep.
  lstep.
  lstep.
  lstep. if_cases K0; zify_cond K0. 1:{ exfalso. clear - K0 Hsp RSP LO GLO. try rewrite unsigned_lit in K0 by lia. lia. } clear K0.
  lstep. lstep. if_lit.
  lstep.
  lstep. lstep.
  lstep.
  lstep. if_lit.
  lstep. lstep.
  call (uselocale_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 150552 18446744073709551615);
    [ first [reflexivity | lia | eassumption] .. | ].
  eval_post POST. eval_a0. rename POST into TPL2.
  lstep. lstep. lstep. if_lit.
  lstep.
  lstep.
  lstep.
  lstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear - K1 X0 XH. try rewrite !unsigned_lit in K1 by lia. lia. } clear K1.
  lstep. if_lit.
  do 5 lstep.
  unname_sp.
  lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  apply evt_done. unfold wunshift_post. sys_finish.
Qed.
