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
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_defsA Atp_activewA Atp_pidiA Pj_defsA Pj_hdefsA Imp_hdefsA Imp_lftoi1A Imp_lftoi2A Imp_lftoi3A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition IMP_GRSIRET_A : Z := 0xb5618.
Definition IMP_ATCXARET_A : Z := 0xb5634.
Definition IMP_DSO_A : Z := 0x181d40.
Definition IMP_XVECDTOR_A : Z := 0xb4c50.

Definition setup_st (pc : Z) (ra : word) (sp' : Z) (gp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f : Z) (s4 : word) (n : Z) (s8 s9 s10 s11 : word)
    (t3 t4 t5 t6 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 (-8)) (Z_to_bv 64 (shad f)) s4 (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 (shad f + 20)) s8 s9 s10 s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma imp_walk2c : forall (usp sp' f n : Z) (x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8x s9x s10x s11x t3 t4 t5 t6 : word) Fr fc (m : mem),
  evt bsegs (eq (setup_st IMP_BODY_A x1 sp' gp t0 t1 t2 usp (sxb (Z_to_bv 8 1)) a1 a2 a3 a4 a5 a6 a7 f (Z_to_bv 64 (-14)) n s8x s9x s10x s11x t3 t4 t5 t6 Fr fc m))
    (setup_st IMP_GTEST_A x1 sp' gp t0 t1 t2 usp (sxb (Z_to_bv 8 1)) a1 a2 a3 a4 a5 a6 a7 f (Z_to_bv 64 (-14)) n s8x s9x s10x s11x t3 t4 t5 t6 Fr fc m).
Proof.
  intros. unfold setup_st, IMP_GTEST_A, IMP_BODY_A, TPV_A, shad, SHB in *.
  zstep. if_false. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma imp_walk12a : forall (usp sp' f n : Z) (x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8x s9x s10x s11x t3 t4 t5 t6 : word) Fr fc (m : mem),
  rw_cells bsegs m IMP_GUARD_A [C1 z8; C1 z8] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a1' a2' : word),
      ms = setup_st IMP_GRSI_A (Z_to_bv 64 IMP_GRSIRET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 IMP_VEC_OBJ_A) a1' a2' a3 a4 a5 a6 a7 f (Z_to_bv 64 (-14)) n s8x s9x s10x s11x
             t3 t4 t5 t6 Fr fc m1
      /\ munch [(IMP_GUARD_A + 1, IMP_GUARD_A + 2)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 IMP_GUARD_A [C1 z8; C1 (Z_to_bv 8 2)])
    (setup_st IMP_GTEST_A x1 sp' gp t0 t1 t2 usp (sxb (Z_to_bv 8 0)) a1 a2 a3 a4 a5 a6 a7 f (Z_to_bv 64 (-14)) n s8x s9x s10x s11x t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros GB MI.
  unfold setup_st, IMP_GTEST_A, IMP_GRSI_A, IMP_GRSIRET_A, IMP_GUARD_A, IMP_VEC_OBJ_A, TPV_A, shad, SHB, z8 in *.
  pose proof (munch_refl [(7061568 + 1, 7061568 + 2)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

  zstep. if_true. zstep. zstep. zstep.

  zstep. cbv beta. zstep. zstep. if_true. zstep. cbv beta. zstep. zstep. if_false. zstep. zstep. if_false. zstep. ls. zstep. zstep. zstep.

  zstep. zstep. if_false. zstep. zstep. zstep.
  apply evt_done. eexists _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma imp_walk12b : forall (usp sp' f n : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x s8x s9x s10x s11x t3 t4 t5 t6 : word) Fr fc (m : mem),
  evt bsegs (eq (setup_st IMP_ATCXA_A (Z_to_bv 64 IMP_ATCXARET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 IMP_XVECDTOR_A) (Z_to_bv 64 IMP_VEC_OBJ_A) (Z_to_bv 64 IMP_DSO_A)
                 a3 a4 a5 a6 a7 f s4x n s8x s9x s10x s11x t3 t4 t5 t6 Fr fc m))
    (setup_st IMP_GRSIRET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s4x n s8x s9x s10x s11x t3 t4 t5 t6 Fr fc m).
Proof.
  intros. unfold setup_st, IMP_GRSIRET_A, IMP_ATCXA_A, IMP_ATCXARET_A, IMP_XVECDTOR_A, IMP_VEC_OBJ_A, IMP_DSO_A, TPV_A, shad, SHB in *.
  do 7 zstep. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma imp_walk12c : forall (usp sp' f d n : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x s6x s8x s9x s10x s11x t3 t4 t5 t6 : word) (b0 b1 : byte)
    (j0 j8 j48 j128 j152 j192 : list byte) Fr fc (m : mem),
  0x6e0000 <= sp' -> sp' + 216 < 2^63 ->
  rw_cells bsegs m IMP_GUARD_A [C1 b0; C1 b1] ->
  rw_cells bsegs m sp' (imp_locals2 j0 j8 f j48 (Z_to_bv 64 d) j128 j152 j192) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = setup_st IMP_BODY_A (Z_to_bv 64 (IMP_ATCXARET_A + 12)) sp' gp t0 t1 t2 usp (Z_to_bv 64 IMP_GUARD_A) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 f s4x n s8x s9x s10x s11x
             t3 t4 t5 t6 Fr fc m1
      /\ munch [(IMP_GUARD_A, IMP_GUARD_A + 2)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 IMP_GUARD_A [C1 one8; C1 one8])
    (MS (mkR x1 (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (-8)) (Z_to_bv 64 (shad f)) s4x (Z_to_bv 64 n) s6x (Z_to_bv 64 (shad f + 20)) s8x s9x s10x s11x t3 t4 t5 t6)
        Fr (Z_to_bv 64 IMP_ATCXARET_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros SP0 SPH GB FRl MI.
  unfold setup_st, imp_locals2, IMP_ATCXARET_A, IMP_BODY_A, IMP_GUARD_A, TPV_A, shad, SHB, one8 in *.
  replace (f / 8 + 2147450880 + 20) with (f / 8 + 2147450900) in * by lia.
  pose proof (munch_refl [(7061568, 7061568 + 2)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).

  zstep. zstep. zstep. zstep. zstep. ls. ls. zstep.

  zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma ga_walk_mid : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 32 -> 0x6e0000 <= lo -> usp < 2^63 -> libm m -> mem_inv bsegs m ->
  evt bsegs (ga_post ra usp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_getact m).
Proof.
  intros until m. intros ST LO GLO SPH (L1 & L2 & L3 & L4) MI.
  unfold entry_st, e_getact, ga_post, ga_W, libm, lib1, one8, z8 in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp); (0x6bc120, 0x6bc128); (0x6bc140, 0x6bc142); (0x6bc1c0, 0x6bc1ec); (0x6bc220, 0x6bc222)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.

  zstep. zstep. zstep. zstep. cbv beta. zstep. zstep. if_true.

  zstep. zstep. zstep.
  zstep. cbv beta. zstep. zstep. if_true. zstep. cbv beta. zstep. zstep. if_false. zstep. zstep. if_false. zstep. ls. zstep. zstep. zstep.

  zstep. zstep. if_false. zstep. zstep. zstep.

  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR0; [| reflexivity].
  cbn [mk_CB_cells app] in FR0.
  lstep. zstep. zstep. cbv beta. zstep. zstep. if_false.
  zstep. zstep.
  release_frame FR0 ST (usp + -16).
  zstep.

  zstep. zstep. lstep. zstep. zstep. zstep.
  zstep. zstep. ls. ls. zstep.
  zstep.

  zstep. zstep. zstep. zstep.
  release_frame FR ST usp.
  zstep. zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
  exact (conj L1 (conj L2 (conj L3 L4))).
Qed.

Definition pdtor0_W (P sp' : Z) : list ivl := [(sp' - 64, sp'); (P + 8, P + 16); (P + 24, P + 40); (P + 64, P + 72)].

Lemma imp_pdtor0_walk : forall (usp sp' f lo P s4 : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
  stk bsegs m lo sp' -> lo <= sp' - 64 -> 0x6e0000 <= lo -> sp' + 216 < 2^63 -> 0x6e0000 <= f -> f + 2048 <= lo -> 0 <= shad f -> shad f + 256 <= lo ->
  (f + 2048 <= shad f \/ shad f + 256 <= f) ->
  f + 168 <= P -> P + 128 <= f + 2048 -> P mod 8 = 0 ->
  client_consts m ->
  rw_cells bsegs m (P + 8) [C8 (Z_to_bv 64 0)] -> rw_cells bsegs m (P + 24) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells bsegs m (P + 64) [C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m (P / 8 + 2147450881) [C1 z8] -> ro_cells bsegs m (P / 8 + 2147450883) [C1 z8] -> ro_cells bsegs m (P / 8 + 2147450884) [C1 z8] ->
  ro_cells bsegs m (P / 8 + 2147450888) [C1 z8] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' a1' a2' t1' : word),
      ms = dtor_st IMP_PDRET_A (Z_to_bv 64 IMP_PDRET_A) sp' gp t0 t1' t2 usp a0' a1' a2' a3 a4 a5 a6 a7 f P s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m1
      /\ munch (pdtor0_W P sp') m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo sp'
      /\ rw_cells bsegs m1 (P + 8) [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs m1 (P + 24) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] /\ rw_cells bsegs m1 (P + 64) [C8 (Z_to_bv 64 0)])
    (dtor_st e_pdtor (Z_to_bv 64 IMP_PDRET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 f P s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros ST LO GLO SPH F0 FLO SH0 SLO SEP PF PH P8 (G1 & G2 & G3 & G4) C8a C24 C64 Z1 Z3 Z4 Z8 MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold dtor_st, pdtor0_W, e_pdtor, IMP_PDRET_A, TPV_A, shad, SHB in *.
  replace (f / 8 + 2147450880 + 20) with (f / 8 + 2147450900) in * by lia.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(sp' - 64, sp'); (P + 8, P + 16); (P + 24, P + 40); (P + 64, P + 72)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).

  zstep.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  ls. ls. ls. zstep. zstep. zstep. zstep. zstep.

  zstep. rewrite shr3_div. zstep. replace ((P + 64) / 8 + 2147450880) with (P / 8 + 2147450888) by (Z.div_mod_to_equations; lia).
  zstep. cbv beta. rewrite lbu_z8. zstep. if_false. zstep. ls. zstep. if_true.

  zstep. zstep.
  zstep.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
  ls. ls. ls. zstep. zstep. zstep. zstep. zstep.

  zstep. rewrite shr3_div. zstep. replace ((P + 24 + 8) / 8 + 2147450880) with (P / 8 + 2147450884) by (Z.div_mod_to_equations; lia).
  try replace ((P + 32) / 8 + 2147450880) with (P / 8 + 2147450884) by (Z.div_mod_to_equations; lia).
  zstep. cbv beta. rewrite lbu_z8. zstep. if_false. zstep. ls. zstep. if_true.

  zstep. rewrite shr3_div. zstep. replace ((P + 24) / 8 + 2147450880) with (P / 8 + 2147450883) by (Z.div_mod_to_equations; lia).
  zstep. cbv beta. rewrite lbu_z8. zstep. if_false. zstep. ls. zstep. if_true.
  zstep. zstep. zstep. zstep.
  release_frame FR0 ST (sp' + -32).
  zstep.

  zstep. zstep. rewrite shr3_div. zstep. replace ((P + 8) / 8 + 2147450880) with (P / 8 + 2147450881) by (Z.div_mod_to_equations; lia).
  zstep. cbv beta. rewrite lbu_z8. zstep. if_false. zstep. ls. zstep. if_true.
  zstep. zstep. zstep. zstep.
  release_frame FR ST sp'.
  zstep.
  apply evt_done. eexists _, _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
  split; [exact C8a| split; [exact C24| exact C64]].
Qed.
