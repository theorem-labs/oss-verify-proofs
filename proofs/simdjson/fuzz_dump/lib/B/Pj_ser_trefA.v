(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_hkitB Pj_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition PJ_TREF_A : Z := 0xafc0c.

Lemma tref_idx_ok : forall idx, 0 <= idx < 2^60 -> (idx + 1152921504606846976) / 2305843009213693952 = 0.
Proof. intros idx H. apply Z.div_small. change 1152921504606846976 with (2^60). change 2305843009213693952 with (2^61). lia. Qed.

Lemma tref_walk : forall (DOCP TAPE idx sp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo sp -> lo <= sp - 16 -> 0x7fff7f800000 <= lo -> sp < 2^63 ->
  client_consts m -> 0 < DOCP -> DOCP + 16 < 2^47 -> DOCP mod 8 = 0 -> bytes_at bsegs m (shad DOCP) [z8; z8] ->
  rw_cells bsegs m DOCP [C8 (Z_to_bv 64 TAPE)] -> 0 < TAPE -> TAPE mod 8 = 0 -> 0 <= idx -> TAPE + 8 * idx < 2^63 ->
  (DOCP + 8 <= sp - 16 \/ sp <= DOCP) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (a4' : word),
      ms = MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (TAPE + 8 * idx)) (Z_to_bv 64 0) (Z_to_bv 64 TAPE) (Z_to_bv 64 1152921504606846976) a4' a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 16, sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo sp)
    (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DOCP) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PJ_TREF_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH (G1 & G2 & _) D0 DH D8 SHD DC T0 T8 I0 IH SEP MI. unfold PJ_TREF_A.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(sp - 16, sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 DOCP) = DOCP) by (apply unsigned_lit; lia).
  change (id (bytes_at bsegs m (shad DOCP) [z8; z8])) in SHD.
  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose (mcur := mx) end.
  assert (SHZ : shz mcur DOCP 16).
  { change 16 with (8 * Z.of_nat 2). apply (shz_of_zero_run mcur DOCP 2); [exact D8| lia|].
    unfold id in SHD. eapply bytes_at_agree; [exact SHD|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [length Z.of_nat repeat] in Hx.
    unfold shad, SHB in Hx. cbn [outside]. split; [Z.div_mod_to_equations; lia| exact I]. }
  subst mcur.
  clear SHD.
  zstep. zstep. zstep.
  shz_pose SHZ DOCP.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. zstep.
  rewrite (Z.shiftl_mul_pow2 idx 3) by lia. change (2 ^ 3) with 8.
  replace ((idx * 8) mod 18446744073709551616) with (idx * 8) by (symmetry; apply Z.mod_small; lia).
  replace (TAPE + idx * 8) with (TAPE + 8 * idx) by lia.

  zstep. zstep. rewrite (proj2 (Z.ltb_lt 0 TAPE)) by lia. rewrite (proj2 (Z.ltb_ge (TAPE + 8 * idx) 1)) by lia.
  zstep. if_false.

  zstep. zstep. zstep. zstep.
  rewrite ?Z.shiftr_div_pow2 by lia. change (2 ^ 61) with 2305843009213693952.
  replace ((idx + 1152921504606846976) mod 18446744073709551616) with (idx + 1152921504606846976) by (symmetry; apply Z.mod_small; lia).
  rewrite tref_idx_ok by lia.
  zstep. if_false.

  zstep. if_cases G1'; zify_cond G1'; [exfalso; rewrite ?unsigned_lit in G1' by lia; lia|].
  zstep. if_cases G2'; zify_cond G2'; [exfalso; rewrite ?unsigned_lit in G2' by lia; lia|].

  zstep. rewrite (land7_mod8 (TAPE + 8 * idx)) by (Z.div_mod_to_equations; lia).
  zstep. if_false.

  zstep. zstep. release_frame FR ST sp. zstep.
  replace (sp - 16 + 16) with sp by lia.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ST].
Qed.
