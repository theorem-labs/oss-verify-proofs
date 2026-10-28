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
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_activewA Atp_pidwA Pj_defsA Imp_hdefs0A Imp_libifaceA Imp_gsidefsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac gfalse := first [if_false | lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false by (vm_compute; reflexivity); cbv_concl_iota end].

Lemma supportedA : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 32 -> 0x100000000 <= lo -> usp < 2^63 ->
  ro_cells bsegs m 2148333624 [C1 z8] -> ro_cells bsegs m 2147644436 [C1 z8] -> ro_cells bsegs m 2148333629 [C1 z8] ->
  vt_impl m -> client_consts m ->
  rw_cells bsegs m SJ_SINGLETON [C8 (wz 0x17a090); C8 (wz 0x29a80); C8 (wz 8); C8 (wz 0x2cda0); C8 (wz 31); C4 (wz 0)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a1' a2' a3' : word) (m' : mem),
      ms = MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz 1) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 32, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp)
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz SJ_SINGLETON) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0xc17f4 m).
Proof.
  intros until m. intros ST LO GLO SPH RD0 RD1 RD2 VT (CC1 & CC2 & _ & _) SG MI.
  unfold entry_st, vt_impl, SJ_SINGLETON, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB, z8 in *.
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  zstep.

  zstep. zstep. zstep.

  zstep. try rewrite shr3_div. zstep. shz_norm. zstep. shz_norm. zstep. if_false.

  zstep. zstep. zstep. try rewrite shr3_div. zstep. shz_norm. zstep. shz_norm. zstep. if_false. zstep. zstep.

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
  lstep. zstep. zstep. zstep. zstep. zstep. try rewrite shr3_div. zstep. shz_norm. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. release_frame FR0 ST (usp + -16). zstep.

  zstep. zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. eexists _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ST].
Qed.

Definition begin_W (usp : Z) : list ivl :=
  [(usp - 32, usp); (IMP_AVP_SPAN_A, IMP_AVP_SPAN_A + 16); (IMP_AVP_GUARD_A, IMP_AVP_GUARD_A + 2); (IMP_AVP_ARR_A, IMP_AVP_ARR_A + 8); (SJ_SINGLETON, SJ_SINGLETON + 44); (0x6bc220, 0x6bc222)].

Lemma implbeginA : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 32 -> 0x100000000 <= lo -> usp < 2^63 ->
  rw_cells bsegs m IMP_AVP_GUARD_A g00 -> rw_cells bsegs m 0x6bc220 [C1 z8; C1 z8] ->
  rw_cells bsegs m SJ_SINGLETON [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0)] ->
  rw_cells bsegs m IMP_AVP_SPAN_A [C8 (wz 0); C8 (wz 0)] -> rw_cells bsegs m IMP_AVP_ARR_A [C8 (wz 0)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a1' a2' a3' a4' a5' a6' : word) (m' : mem),
      ms = MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz IMP_AVP_ARR_A) a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch (begin_W usp) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
      /\ rw_cells bsegs m' IMP_AVP_GUARD_A g11 /\ rw_cells bsegs m' 0x6bc220 [C1 one8; C1 one8]
      /\ rw_cells bsegs m' SJ_SINGLETON [C8 (wz 0x17a090); C8 (wz 0x29a80); C8 (wz 8); C8 (wz 0x2cda0); C8 (wz 31); C4 (wz 0)]
      /\ rw_cells bsegs m' IMP_AVP_SPAN_A [C8 (wz IMP_AVP_ARR_A); C8 (wz 1)] /\ rw_cells bsegs m' IMP_AVP_ARR_A [C8 (wz SJ_SINGLETON)])
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz 0x6bc0e0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0xc1854 m).
Proof.
  intros until m. intros ST LO GLO SPH GA GS SG SP AR MI.
  unfold entry_st, begin_W, IMP_AVP_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_ARR_A, SJ_SINGLETON, g00, g11, one8, z8 in *.
  pose proof (munch_refl [(usp - 32, usp); (7061856, 7061856 + 16); (7061888, 7061888 + 2); (7061920, 7061920 + 8); (7061952, 7061952 + 44); (0x6bc220, 0x6bc222)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  zstep. zstep.

  zstep. zstep. shz_norm. zstep. zstep. zstep. zstep. if_true.

  zstep. zstep. zstep.
  zstep. shz_norm. zstep. zstep. if_true. zstep. shz_norm. zstep. zstep. if_false. zstep. zstep. if_false. zstep. ls. zstep. zstep. zstep.

  zstep. zstep. if_false. zstep.

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
  lstep. zstep. zstep. shz_norm. zstep. zstep. if_true.

  zstep. zstep. zstep.
  zstep. shz_norm. zstep. zstep. if_true. zstep. shz_norm. zstep. zstep. if_false. zstep. zstep. if_false. zstep. ls. zstep. zstep. zstep.

  zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  ls. ls. ls. ls. zstep. zstep. ls. ls.
  zstep. zstep. release_frame FR0 ST (usp + -16). zstep.
  zstep. zstep. ls. ls. zstep.

  zstep. zstep. zstep. zstep. ls. zstep. ls. ls. zstep. zstep. zstep.
  zstep. zstep. ls. ls. zstep.

  zstep. zstep. zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. eexists _, _, _, _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
  split; [eassumption| split; [eassumption| split; [eassumption| split; eassumption]]].
Qed.

Lemma getavailA : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 16 -> 0x100000000 <= lo -> usp < 2^63 ->
  rw_cells bsegs m IMP_AVL_GUARD_A g00 -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a1' a2' : word) (m' : mem),
      ms = MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz 0x6bc0e0) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 16, usp); (IMP_AVL_GUARD_A, IMP_AVL_GUARD_A + 2)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
      /\ rw_cells bsegs m' IMP_AVL_GUARD_A g11)
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0xc1bbc m).
Proof.
  intros until m. intros ST LO GLO SPH GA MI.
  unfold entry_st, IMP_AVL_GUARD_A, g00, g11, one8, z8 in *.
  pose proof (munch_refl [(usp - 16, usp); (7061760, 7061760 + 2)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  zstep. zstep. zstep. shz_norm. zstep. zstep. if_true.

  zstep. zstep. zstep.
  zstep. shz_norm. zstep. zstep. if_true. zstep. shz_norm. zstep. zstep. if_false. zstep. zstep. if_false. zstep. ls. zstep. zstep. zstep.

  zstep. zstep. if_false. zstep. zstep. zstep.
  zstep. zstep. ls. ls. zstep. zstep.

  zstep. zstep. zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. eexists _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| eassumption].
Qed.

Lemma implendA : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 16 -> 0x100000000 <= lo -> usp < 2^63 ->
  rw_cells bsegs m IMP_AVP_GUARD_A g11 -> rw_cells bsegs m IMP_AVP_SPAN_A [C8 (wz IMP_AVP_ARR_A); C8 (wz 1)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a1' a2' a3' a4' : word) (m' : mem),
      ms = MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz (IMP_AVP_ARR_A + 8)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 16, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp)
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0xc18e4 m).
Proof.
  intros until m. intros ST LO GLO SPH GA SP MI.
  unfold entry_st, IMP_AVP_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_ARR_A, g11, one8 in *.
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  zstep. zstep. zstep. zstep. cbv beta. zstep. zstep. zstep. zstep. if_false.

  zstep. zstep. zstep. zstep. zstep. zstep. zstep. gfalse.
  zstep. zstep. zstep. zstep. zstep. gfalse. zstep. gfalse.
  zstep. zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. eexists _, _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ST].
Qed.
