(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA X_ixdefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition e_annot : Z := 0x88510.
Definition ANNOT_FRAME : Z := 2128.

Lemma shz_ro1 : forall (m : mem) a, shz m a 8 -> a mod 8 = 0 -> 0 <= a < 2^64 -> ro_cells bsegs m (shad a) [C1 z8].
Proof.
  intros m a SZ A8 AR. pose proof (SZ a ltac:(lia)) as H. rewrite ov_rdn in H. cbn [rdn] in H.
  split; [cbn; repeat split; exact I|]. cbn [cells_bytes cbytes app]. unfold shad, SHB.
  split; [Z.div_mod_to_equations; lia|]. split; [cbn [length]; Z.div_mod_to_equations; lia|].
  intros i Hi. destruct i as [|i]; [| cbn [length] in Hi; lia]. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. unfold mrd.
  destruct (m (wa (a / 8 + 2147450880))) as [b|]; [| destruct (seg_rom bsegs (wa (a / 8 + 2147450880))) as [b|]]; cbn in H; try discriminate; injection H as ->; reflexivity.
Qed.

Lemma annot_nopA : forall (usp lo b e mid : Z) (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - ANNOT_FRAME -> 0x100000000 <= lo -> usp < 2^63 ->
  0 <= b -> b <= mid <= e -> e < 2^63 -> e - b < 2^40 ->
  rw_cells bsegs m g_GOT_flags [C8 (wz 0x187178)] -> ro_cells bsegs m g_flags_dco [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m g_GOT_verbosity [C8 (wz g_verbosity)] -> rw_cells bsegs m g_verbosity [C4 (wz 0)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a0' a1' a3' : word) (m' : mem),
      ms = MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 a0' a1' (wz mid) a3' (Z_to_bv 64 (Z.shiftl 1 40)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(usp - ANNOT_FRAME, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp)
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz b) (wz e) (wz mid) (wz mid) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_annot m).
Proof.
  intros until m. intros ST LO GLO SPH B0 BM EH EB GF FD GV VV MI.
  unfold entry_st, e_annot, ANNOT_FRAME, g_GOT_flags, g_flags_dco, g_GOT_verbosity, g_verbosity in *. change (0x187178 + 96) with 1602008 in FD.
  pose proof (munch_refl [(usp - 2128, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. carve_frame 2032%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 2032 _ [] [1976; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. carve_frame 96%nat ST.

  zstep. zstep. zstep. zstep. cbv beta. zstep. if_false.

  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false.

  step. if_cases K; zify_cond K; [| exfalso; lia].

  step. if_cases K2; zify_cond K2; [exfalso; lia|].
  step. if_cases K3; zify_cond K3; [exfalso; lia|].
  step. if_cases K4; zify_cond K4; [exfalso; lia|].

  zstep. zstep. zstep. zstep. step. if_cases K5; zify_cond K5; [exfalso; lia|].

  zstep. if_true.

  zstep. release_frame FR0 ST (usp + -2032).
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. eexists _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ST].
Qed.
