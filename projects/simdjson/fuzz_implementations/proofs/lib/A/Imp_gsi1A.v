(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx D_rlkit I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_activewA Atp_pidwA Pj_defsA
     Imp_hdefs0A Imp_libifaceA Imp_gsidefsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma supportedA : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 32 -> 0x100000000 <= lo -> usp < 2^63 ->
  ro_cells asegs m 2148326368 [C1 z8] -> ro_cells asegs m 2147637348 [C1 z8] -> ro_cells asegs m 2148326373 [C1 z8] ->
  vt_impl m -> client_consts m ->
  rw_cells asegs m SJ_SINGLETON [C8 (wz 0x16c310); C8 (wz 0x29900); C8 (wz 8); C8 (wz 0x2cfe0); C8 (wz 31); C4 (wz 0)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' a2' a3' : word) (m' : mem),
      ms = MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz 1) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(usp - 32, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp)
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz SJ_SINGLETON) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0xbf3d4 m).
Proof.
  intros until m. intros ST LO GLO SPH RD0 RD1 RD2 VT (CC1 & CC2 & _ & _) SG MI.
  unfold entry_st, vt_impl, SJ_SINGLETON, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB, z8 in *.
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  zstep.

  zstep. zstep. zstep.

  zstep. try rewrite shr3_div. zstep. shz_norm. zstep. shz_norm. zstep. if_false.

  zstep. zstep. zstep. try rewrite shr3_div. zstep. shz_norm. zstep. shz_norm. zstep. if_false. zstep. zstep.

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
  lstep. zstep. zstep. zstep. zstep. zstep. try rewrite shr3_div. zstep. shz_norm. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. release_frame FR0 ST (usp + -16). zstep.

  zstep. zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. eexists _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ST].
Qed.

Definition begin_W (usp : Z) : list ivl :=
  [(usp - 32, usp); (IMP_AVP_SPAN_A, IMP_AVP_SPAN_A + 16); (IMP_AVP_GUARD_A, IMP_AVP_GUARD_A + 2); (IMP_AVP_ARR_A, IMP_AVP_ARR_A + 8); (SJ_SINGLETON, SJ_SINGLETON + 44); (0x6adf60, 0x6adf62)].

Lemma implbeginA : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 32 -> 0x100000000 <= lo -> usp < 2^63 ->
  rw_cells asegs m IMP_AVP_GUARD_A g00 -> rw_cells asegs m 0x6adf60 [C1 z8; C1 z8] ->
  rw_cells asegs m SJ_SINGLETON [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0)] ->
  rw_cells asegs m IMP_AVP_SPAN_A [C8 (wz 0); C8 (wz 0)] -> rw_cells asegs m IMP_AVP_ARR_A [C8 (wz 0)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' a2' a3' a4' a5' a6' : word) (m' : mem),
      ms = MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz IMP_AVP_ARR_A) a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (begin_W usp) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
      /\ rw_cells asegs m' IMP_AVP_GUARD_A g11 /\ rw_cells asegs m' 0x6adf60 [C1 one8; C1 one8]
      /\ rw_cells asegs m' SJ_SINGLETON [C8 (wz 0x16c310); C8 (wz 0x29900); C8 (wz 8); C8 (wz 0x2cfe0); C8 (wz 31); C4 (wz 0)]
      /\ rw_cells asegs m' IMP_AVP_SPAN_A [C8 (wz IMP_AVP_ARR_A); C8 (wz 1)] /\ rw_cells asegs m' IMP_AVP_ARR_A [C8 (wz SJ_SINGLETON)])
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz 0x6ade20) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0xbf434 m).
Proof.
  intros until m. intros ST LO GLO SPH GA GS SG SP AR MI.
  unfold entry_st, begin_W, IMP_AVP_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_ARR_A, SJ_SINGLETON, g00, g11, one8, z8 in *.
  pose proof (munch_refl [(usp - 32, usp); (7003808, 7003808 + 16); (7003840, 7003840 + 2); (7003872, 7003872 + 8); (7003904, 7003904 + 44); (0x6adf60, 0x6adf62)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  zstep. zstep.

  zstep. zstep. shz_norm. zstep. zstep. zstep. zstep. if_true.

  zstep. zstep. zstep.
  zstep. shz_norm. zstep. zstep. if_true. zstep. shz_norm. zstep. zstep. if_false. zstep. zstep. if_false. zstep. ls. zstep. zstep. zstep.

  zstep. zstep. if_false. zstep.

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
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
  stk asegs m lo usp -> lo <= usp - 16 -> 0x100000000 <= lo -> usp < 2^63 ->
  rw_cells asegs m IMP_AVL_GUARD_A g00 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' a2' : word) (m' : mem),
      ms = MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz 0x6ade20) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(usp - 16, usp); (IMP_AVL_GUARD_A, IMP_AVL_GUARD_A + 2)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
      /\ rw_cells asegs m' IMP_AVL_GUARD_A g11)
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0xbf718 m).
Proof.
  intros until m. intros ST LO GLO SPH GA MI.
  unfold entry_st, IMP_AVL_GUARD_A, g00, g11, one8, z8 in *.
  pose proof (munch_refl [(usp - 16, usp); (7003712, 7003712 + 2)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
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
  stk asegs m lo usp -> lo <= usp - 16 -> 0x100000000 <= lo -> usp < 2^63 ->
  rw_cells asegs m IMP_AVP_GUARD_A g11 -> rw_cells asegs m IMP_AVP_SPAN_A [C8 (wz IMP_AVP_ARR_A); C8 (wz 1)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' : word) (m' : mem),
      ms = MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz (IMP_AVP_ARR_A + 8)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(usp - 16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp)
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0xbf4c4 m).
Proof.
  intros until m. intros ST LO GLO SPH GA SP MI.
  unfold entry_st, IMP_AVP_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_ARR_A, g11, one8 in *.
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  zstep. zstep. zstep. zstep. cbv beta. zstep. zstep. zstep. zstep. if_false.

  zstep. zstep. zstep. zstep. zstep. zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ST].
Qed.
