(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_new Sj_h_dtor Atp_fzwA Atp_pdtorA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma pt_walk1a : forall (usp P copy lo : Z) (impl tape sbuf dcap : word) (pre8 mid mid2 rest : list byte)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 32 -> 0x6d2000 <= lo -> usp < 2^63 -> 0 < P -> P + 80 <= lo -> 0 < copy < 2^64 ->
  shb_consts m -> (forall m' : mem, munch (pt_W usp P) m m' -> wmono asegs m m' -> shz m' P 80) ->
  rw_cells asegs m P (pd_cells pre8 impl mid tape sbuf dcap mid2 (Z_to_bv 64 copy) rest) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (j : list byte),
      ms = entry_st (Z_to_bv 64 0xb6b04) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 copy) (Z_to_bv 64 copy) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_delarr m1
      /\ munch (pt_W usp P) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -32)
      /\ rw_cells asegs m1 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m1 P (pd_cells pre8 impl mid tape sbuf dcap mid2 (Z_to_bv 64 0) rest))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_pdtor m).
Proof.
  intros until m. intros ST LO GLO SPH D0 DLO C0 (G1 & G2) SHZ PC MI.
  unfold entry_st, e_pdtor, e_delarr, pt_W, pd_cells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp); (P, P + 80)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUC : bv_unsigned (Z_to_bv 64 copy) = copy) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. zstep. zstep. clear G1 G2. zstep. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (P + 64) ltac:(lia)) as RD0 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. lstep. zstep.
  if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR| eassumption].
Qed.

Lemma pt_walk1b : forall (P : Z) (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < P < 2^63 ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb6b0c) sp gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 2147450880)
                   (Z_to_bv 64 (P + 24)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_docdtor m))
    (MS (mkR (Z_to_bv 64 0xb6b04) sp gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6b04) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros P0.
  unfold entry_st, e_docdtor in *.
  zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.
