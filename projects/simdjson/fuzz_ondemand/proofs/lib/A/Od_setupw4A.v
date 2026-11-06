(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim SjModel OdModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Str_tac Sj_stage1_kit Sj_h_arith.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Od_hbaseA
  Sj_new Sj_num_amem Sj_stage1_defs Atp_h_defsA Atp_activewA Od_hkit0A Od_createwA Od_lkitA Od_proA Od_setup_defsA Od_setupw1A Od_setupw2A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ asan_load_hook | solve_load_image | solve_load_base ].

Definition vt_impl (m : mem) : Prop :=
  ro_cells asegs m 0x109780
    [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1097e0); C8 (Z_to_bv 64 0xc59ac); C8 (Z_to_bv 64 0xc5b38); C8 (Z_to_bv 64 0xc5cc4); C8 (Z_to_bv 64 0x9cd44);
     C8 (Z_to_bv 64 0x9f334); C8 (Z_to_bv 64 0x9f4c4)].

Lemma od_walkC1 : forall (ra : word) (usp S1 F lo COPY BUF L : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word) FR fc (m : mem),
  0x66b000 <= F -> F + 512 <= lo -> 0x66b000 <= lo -> lo <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 -> 0 <= L < 2^26 ->
  rw_cells asegs m (F + 104) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (F + 136) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  cli_got_nothrow m -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) a2',
      ms = lh_regs e_newarr_nt (Z_to_bv 64 0x96d54) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (OD_SBUF L)) (Z_to_bv 64 0x2d070) a2' a3 a4 a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) (Z_to_bv 64 COPY) (Z_to_bv 64 L) (Z_to_bv 64 BUF) s10 t3 t4 t5 t6 FR fc m1
      /\ munch [(F + 112, F + 120); (F + 136, F + 144)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (F + 104) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
      /\ rw_cells asegs m1 (F + 136) [C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 0)])
    (lh_regs 0x96d18 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) (Z_to_bv 64 COPY) (Z_to_bv 64 L) (Z_to_bv 64 BUF) s10
       t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO GLO LSP LUSP SPH LR PA8 PA40 GOT MI.
  unfold lh_regs, e_newarr_nt, cli_got_nothrow in *.
  pose proof (munch_refl [(F + 112, F + 120); (F + 136, F + 144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  ls. ls. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite (sbuf_size_eq L) by lia.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma od_walkC2 : forall (ra : word) (usp S1 F lo SB : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 t3 t4 t5 t6 : word) (v40 : word) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> 0x66b000 <= lo -> lo <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 ->
  rw_cells asegs m (F + 104) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (F + 136) [C8 v40; C8 (Z_to_bv 64 0)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = lh_regs e_getact (Z_to_bv 64 0x96e68) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 SB) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) s7 s8 s9 s10 t3 t4 t5 t6 FR fc m1
      /\ munch [(F + 144, F + 152)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (F + 136) [C8 v40; C8 (Z_to_bv 64 SB)])
    (lh_regs 0x96d54 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 SB) a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) s7 s8 s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO GLO LSP LUSP SPH PA8 PA40 MI.
  unfold lh_regs, e_getact in *.
  pose proof (munch_refl [(F + 144, F + 152)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. ls. zstep. if_true. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Lemma od_walkC3 : forall (ra : word) (usp S1 F lo act L : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s9 s10 t3 t4 t5 t6 : word)
    (j0 j192 j224 j248 : list byte) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> 0x66b000 <= lo -> lo <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 ->
  shz m 0x647c80 8 -> shz m 0x647d20 8 -> shz m 0x109780 64 -> lib1 m -> vt_impl m ->
  rw_cells asegs m S1 (od_lowB F act j0 j192 j224 j248) -> mem_inv asegs m ->
  evt asegs (fun ms => exists a4',
      ms = lh_regs e_create (Z_to_bv 64 0x96ecc) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 SJ_SINGLETON) (Z_to_bv 64 L) (Z_to_bv 64 1024) (Z_to_bv 64 (F + 104)) a4' a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) s7 (Z_to_bv 64 L) s9 s10 t3 t4 t5 t6 FR fc m)
    (lh_regs 0x96e68 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 SJ_ACTIVE) a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) s7 (Z_to_bv 64 L) s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO GLO LSP LUSP SPH SZ1 SZ2 SZ3 (L1 & L2 & L3 & L4) VT LOWF MI.
  unfold lh_regs, e_create, SJ_ACTIVE, SJ_SINGLETON, vt_impl, od_lowB, wz in *.
  pose proof (SZ1 0x647c80 ltac:(lia)) as RD0. pose proof (SZ2 0x647d20 ltac:(lia)) as RD1. pose proof (SZ3 0x1097a8 ltac:(lia)) as RD2.
  change (0x647c80 / 8 + 2147450880) with 2148274064 in RD0.
  change (0x647d20 / 8 + 2147450880) with 2148274084 in RD1.
  change (0x1097a8 / 8 + 2147450880) with 2147586805 in RD2.
  zstep. zstep. zstep. rewrite ?lbu_z8. zstep. if_true.
  zstep. zstep. zstep.
  zstep. zstep. zstep. rewrite ?lbu_z8. zstep. if_true.
  zstep. zstep.
  zstep. zstep. zstep. rewrite ?lbu_z8. zstep. if_true.
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkC4 : forall (ra : word) (usp S1 F lo IMPL BUF L : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s10 t3 t4 t5 t6 : word) (v16 v24 v32 : word) FR fc (m : mem),
  0x66b000 <= F -> F + 512 <= lo -> 0x66b000 <= lo -> lo <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 -> 0 < IMPL -> IMPL + 96 <= lo ->
  (F + 512 <= IMPL \/ IMPL + 96 <= F) ->
  (forall m', munch [(F + 112, F + 120); (F + 128, F + 136)] m m' -> wmono asegs m m' -> shz m' IMPL 96) ->
  (forall m', munch [(F + 112, F + 120); (F + 128, F + 136)] m m' -> wmono asegs m m' -> shz m' 0x109840 96) -> vt_dpi m ->
  rw_cells asegs m (F + 104) [C8 (Z_to_bv 64 IMPL); C8 v16] ->
  rw_cells asegs m (F + 120) [C8 v24; C8 v32] ->
  rw_cells asegs m IMPL [C8 (Z_to_bv 64 0x109850)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) a4',
      ms = lh_regs A1_ENTRY (Z_to_bv 64 0x96e40) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 IMPL) (Z_to_bv 64 BUF) (Z_to_bv 64 L) (Z_to_bv 64 0) a4' a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) s7 (Z_to_bv 64 L) (Z_to_bv 64 BUF) s10 t3 t4 t5 t6 FR fc m1
      /\ munch [(F + 112, F + 120); (F + 128, F + 136)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (F + 104) [C8 (Z_to_bv 64 IMPL); C8 (Z_to_bv 64 L)]
      /\ rw_cells asegs m1 (F + 120) [C8 v24; C8 (Z_to_bv 64 1024)])
    (lh_regs 0x96ecc ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) s7 (Z_to_bv 64 L) (Z_to_bv 64 BUF) s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO GLO LSP LUSP SPH I0 ILO FIS SZI SZV VT PA8 PA24 IC MI.
  unfold lh_regs, A1_ENTRY, vt_dpi in *.
  pose proof (munch_refl [(F + 112, F + 120); (F + 128, F + 136)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_true.
  zstep. zstep. ls. ls.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SZV mm MU' WM' 0x109858 ltac:(lia)) as RD2 end.
  change (0x109858 / 8 + 2147450880) with 2147586827 in RD2.
  zstep. rewrite shr3_div. zstep. zstep. rewrite ?lbu_z8. zstep. if_true.
  zstep. zstep.
  zstep. zstep. zstep. rewrite ?lbu_z8. zstep. if_true.
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma od_walkC5e : forall (ra : word) (usp S1 F code : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 s10 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < code < 2^31 ->
  evt asegs (eq (lh_regs OD_ERRX ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 F s5 s7 s8 s9 s10 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96e40 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 F s5 s7 s8 s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros CR. unfold lh_regs, OD_ERRX.
  zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkC5s : forall (ra : word) (usp S1 F : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 s10 t3 t4 t5 t6 : word) FR fc (m : mem),
  evt asegs (eq (lh_regs 0x99ec8 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 F s5 s7 s8 s9 s10 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96e40 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 F s5 s7 s8 s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. unfold lh_regs.
  zstep. if_false. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.
