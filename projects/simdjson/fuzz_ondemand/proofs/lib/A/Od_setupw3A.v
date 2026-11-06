(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Od_hbaseA
  Sj_new Sj_num_amem Atp_h_defsA Od_hkit0A Od_lkitA Od_proA Od_setup_defsA Od_setupw1A Od_setupw2A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ asan_load_hook | solve_load_image | solve_load_base ].

Definition oa_WB1 (S1 F : Z) : list ivl := [(S1 + 216, S1 + 224); (F + 96, F + 97); (F / 8 + 2147450892, F / 8 + 2147450899)].

Lemma od_walkB1 : forall (ra : word) (usp S1 F lo act : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 s10 t3 t4 t5 t6 : word)
    (b12 b13 b14 b15 b16 b17 b18 : byte) (p0 j0 j192 j216 j224 j248 jp : list byte) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> F / 8 + 2147450880 + 64 <= lo -> 0 <= F / 8 ->
  (F + 512 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 64 <= F) ->
  0x66b000 <= lo -> lo <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 ->
  rw_cells asegs m S1 (od_lowA F act j0 j192 j216 j224 j248) ->
  rw_cells asegs m (F + 96) [CB 1 p0; CB 7 jp] ->
  rw_cells asegs m (F / 8 + 2147450892) [C1 b12; C1 b13; C1 b14; C1 b15; C1 b16; C1 b17; C1 b18] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = lh_regs 0x66b4c (Z_to_bv 64 0x96bf8) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (F + 104)) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) s7 s8 s9 s10 t3 t4 t5 t6 FR fc m1
      /\ munch (oa_WB1 S1 F) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 S1 (od_lowB F act j0 j192 j224 j248)
      /\ rw_cells asegs m1 (F + 96) [C1 (Z_to_bv 8 0); CB 7 jp]
      /\ rw_cells asegs m1 (F / 8 + 2147450892) (map C1 (repeat (Z_to_bv 8 0) 7)))
    (lh_regs 0x96bc0 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F s5 s7 s8 s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO SLO FD SEP GLO LSP LUSP SPH LOWF PAR SHP MI.
  unfold lh_regs, oa_WB1, od_lowA, od_lowB, wz in *. cbn [map repeat].
  pose proof (munch_refl [(S1 + 216, S1 + 224); (F + 96, F + 97); (F / 8 + 2147450892, F / 8 + 2147450899)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  do 7 ls. zstep. ls. zstep. zstep. ls. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma od_walkB2 : forall (ra : word) (usp S1 F lo : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 t3 t4 t5 t6 : word)
    (jb jc : list byte) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> 0x66b000 <= lo -> lo <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 ->
  rw_cells asegs m (F + 120) [CB 8 jb; CB 8 jc] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = lh_regs 0x66b4c (Z_to_bv 64 0x96c1c) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (F + 136)) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) s7 s8 s9 s10 t3 t4 t5 t6 FR fc m1
      /\ munch [(F + 120, F + 136)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (F + 120) [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 1024)])
    (lh_regs 0x96bf8 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) s7 s8 s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO GLO LSP LUSP SPH PAR MI.
  unfold lh_regs in *.
  pose proof (munch_refl [(F + 120, F + 136)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. ls. ls. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Lemma od_walkB3c : forall (ra : word) (usp S1 F A p0 len0 : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < A -> A + 16 < 2^63 -> 0 <= len0 <= 0xfffc0 ->
  shz m A 16 -> rw_cells asegs m A [C8 (Z_to_bv 64 p0); C8 (Z_to_bv 64 len0)] -> cli_got_nothrow m -> mem_inv asegs m ->
  evt asegs (eq (lh_regs e_newarr_nt (Z_to_bv 64 0x96c6c) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (len0 + 64)) (Z_to_bv 64 0x2d070) a2 a3 a4 a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) (Z_to_bv 64 A) (Z_to_bv 64 len0) (Z_to_bv 64 p0) s10 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96c1c ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) (Z_to_bv 64 A) s8 s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros A0 AH LR SHZ VE GOT MI.
  unfold lh_regs, e_newarr_nt, cli_got_nothrow in *.
  zstep. rewrite shr3_div. zstep. zstep. rewrite ?lbu_z8. zstep. if_true.
  zstep. zstep. rewrite shr3_div. zstep. zstep. rewrite ?lbu_z8. zstep. if_true.
  zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkB3n : forall (ra : word) (usp S1 F A p0 len0 : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < A -> A + 16 < 2^63 -> 0xfffc0 < len0 < 2^26 ->
  shz m A 16 -> rw_cells asegs m A [C8 (Z_to_bv 64 p0); C8 (Z_to_bv 64 len0)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists a0' a1',
               ms = lh_regs 0x96cec ra S1 gp tp t0 t1 t2 usp a0' a1' a2 a3 a4 a5 a6 a7 F
                      (Z_to_bv 64 (F + 96)) (Z_to_bv 64 0) (Z_to_bv 64 len0) s9 s10 t3 t4 t5 t6 FR fc m)
    (lh_regs 0x96c1c ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) (Z_to_bv 64 A) s8 s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros A0 AH LR SHZ VE MI.
  unfold lh_regs in *.
  zstep. rewrite shr3_div. zstep. zstep. rewrite ?lbu_z8. zstep. if_true.
  zstep. zstep. rewrite shr3_div. zstep. zstep. rewrite ?lbu_z8. zstep. if_true.
  zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  zstep.
  apply evt_done. do 2 eexists. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkBU : forall (ra : word) (usp S1 F lo act : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 t3 t4 t5 t6 : word)
    (b24 b25 b26 b27 b28 b29 b30 b31 : byte) (j0 j192 j224 j248 : list byte) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> F / 8 + 2147450880 + 64 <= lo -> 0 <= F / 8 ->
  0x66b000 <= lo -> lo <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 ->
  rw_cells asegs m S1 (od_lowB F act j0 j192 j224 j248) ->
  rw_cells asegs m (F / 8 + 2147450904) [C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = lh_regs 0x96d18 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (F / 8 + 2147450880)) a1 a2 a3 a4 a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) s7 (Z_to_bv 64 0) s7 s10 t3 t4 t5 t6 FR fc m1
      /\ munch [(F / 8 + 2147450904, F / 8 + 2147450912)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (F / 8 + 2147450904) (map C1 (repeat (Z_to_bv 8 0) 8)))
    (lh_regs 0x96cec ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) s7 s8 s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO SLO FD GLO LSP LUSP SPH LOWF SHD MI.
  unfold lh_regs, od_lowB, wz in *. cbn [map repeat].
  pose proof (munch_refl [(F / 8 + 2147450904, F / 8 + 2147450912)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. do 8 ls. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Lemma od_walkB4 : forall (ra : word) (usp S1 F COPY len0 : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s9 s10 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < COPY -> COPY + len0 < 2^63 -> 0 <= len0 ->
  evt asegs (eq (lh_regs 0x66b4c (Z_to_bv 64 0x96c84) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (COPY + len0)) (Z_to_bv 64 0) (Z_to_bv 64 64) a3 a4 a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) (Z_to_bv 64 COPY) (Z_to_bv 64 len0) s9 s10 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96c6c ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 COPY) a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) s7 (Z_to_bv 64 len0) s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros C0 CH L0. unfold lh_regs.
  zstep. if_cases K; zify_cond K; [exfalso; lia| clear K].
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkB5c : forall (ra : word) (usp S1 F COPY p0 len0 : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < len0 < 2^63 ->
  evt asegs (eq (lh_regs 0x666b0 (Z_to_bv 64 0x96c98) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 COPY) (Z_to_bv 64 p0) (Z_to_bv 64 len0) a3 a4 a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) (Z_to_bv 64 COPY) (Z_to_bv 64 len0) (Z_to_bv 64 p0) s10 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96c84 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) (Z_to_bv 64 COPY) (Z_to_bv 64 len0) (Z_to_bv 64 p0) s10
       t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros L0. unfold lh_regs.
  zstep. if_cases K; zify_cond K; [exfalso; lia| clear K].
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkB5z : forall (ra : word) (usp S1 F : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s9 s10 t3 t4 t5 t6 : word) FR fc (m : mem),
  evt asegs (eq (lh_regs 0x96cec ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) s7 (Z_to_bv 64 0) s9 s10 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96c84 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) s7 (Z_to_bv 64 0) s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. unfold lh_regs.
  zstep. if_true.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkB6s : forall (ra : word) (usp S1 F lo act COPY len0 : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 : word)
    (b24 b25 b26 b27 b28 b29 b30 b31 : byte) (j0 j192 j224 j248 : list byte) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> F / 8 + 2147450880 + 64 <= lo -> 0 <= F / 8 ->
  0x66b000 <= lo -> lo <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 -> 0 <= len0 < 3 ->
  rw_cells asegs m S1 (od_lowB F act j0 j192 j224 j248) ->
  rw_cells asegs m (F / 8 + 2147450904) [C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = lh_regs 0x96d18 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 3) (Z_to_bv 64 (F / 8 + 2147450880)) a2 a3 a4 a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) (Z_to_bv 64 COPY) (Z_to_bv 64 len0) (Z_to_bv 64 COPY) s10 t3 t4 t5 t6 FR fc m1
      /\ munch [(F / 8 + 2147450904, F / 8 + 2147450912)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (F / 8 + 2147450904) (map C1 (repeat (Z_to_bv 8 0) 8)))
    (lh_regs 0x96c98 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) (Z_to_bv 64 COPY) (Z_to_bv 64 len0) s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO SLO FD GLO LSP LUSP SPH LR LOWF SHD MI.
  unfold lh_regs, od_lowB, wz in *. cbn [map repeat].
  pose proof (munch_refl [(F / 8 + 2147450904, F / 8 + 2147450912)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. do 4 ls. zstep. do 4 ls. zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Lemma od_walkB6b : forall (ra : word) (usp S1 F lo act COPY len0 : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 : word)
    (b24 b25 b26 b27 b28 b29 b30 b31 : byte) (j0 j192 j224 j248 : list byte) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> F / 8 + 2147450880 + 64 <= lo -> 0 <= F / 8 ->
  0x66b000 <= lo -> lo <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 -> 3 <= len0 < 2^26 ->
  rw_cells asegs m S1 (od_lowB F act j0 j192 j224 j248) ->
  rw_cells asegs m (F / 8 + 2147450904) [C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = lh_regs e_memcmp (Z_to_bv 64 0x96cd8) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 COPY) (Z_to_bv 64 BOM_LIT) (Z_to_bv 64 3) a3 a4 a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) (Z_to_bv 64 COPY) (Z_to_bv 64 len0) s9 s10 t3 t4 t5 t6 FR fc m1
      /\ munch [(F / 8 + 2147450904, F / 8 + 2147450912)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (F / 8 + 2147450904) (map C1 (repeat (Z_to_bv 8 0) 8)))
    (lh_regs 0x96c98 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) (Z_to_bv 64 COPY) (Z_to_bv 64 len0) s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO SLO FD GLO LSP LUSP SPH LR LOWF SHD MI.
  unfold lh_regs, od_lowB, wz, e_memcmp, BOM_LIT in *. cbn [map repeat].
  pose proof (munch_refl [(F / 8 + 2147450904, F / 8 + 2147450912)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. do 4 ls. zstep. do 4 ls. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Lemma od_walkB7n : forall (ra r : word) (usp S1 F COPY len0 : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 : word) FR fc (m : mem),
  r <> Z_to_bv 64 0 ->
  evt asegs (eq (lh_regs 0x96d18 ra S1 gp tp t0 t1 t2 usp r a1 a2 a3 a4 a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) (Z_to_bv 64 COPY) (Z_to_bv 64 len0) (Z_to_bv 64 COPY) s10 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96cd8 ra S1 gp tp t0 t1 t2 usp r a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) (Z_to_bv 64 COPY) (Z_to_bv 64 len0) s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros RNZ. unfold lh_regs.
  zstep. if_cases K; [| exfalso; apply RNZ; apply bv_eq; zify_cond K; rewrite ?unsigned_lit in K by lia; rewrite unsigned_lit by lia; lia].
  zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkB7b : forall (ra : word) (usp S1 F COPY len0 : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < COPY -> COPY + 3 < 2^63 -> 3 <= len0 < 2^63 ->
  evt asegs (eq (lh_regs 0x96d18 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 F
                   (Z_to_bv 64 (F + 96)) (Z_to_bv 64 COPY) (Z_to_bv 64 (len0 - 3)) (Z_to_bv 64 (COPY + 3)) s10 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96cd8 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 F (Z_to_bv 64 (F + 96)) (Z_to_bv 64 COPY) (Z_to_bv 64 len0) s9 s10
       t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros C0 CH LR. unfold lh_regs.
  zstep. if_false. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.
