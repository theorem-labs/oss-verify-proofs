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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Od_hbaseA
  Sj_new Sj_num_amem Od_defsB Od_tailwB Od_exitwB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition OD_ERRX : Z := 0x97268.

Definition ex_regs (pc : Z) (ra : word) (S1 : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 : word) (F : Z)
    (s5 s6 s8 s9 t3 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
          s2 s3 (Z_to_bv 64 (F + 104)) s5 s6 (Z_to_bv 64 2147450880) s8 s9 (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (F + 192)) t3 t4 t5 t6)
     FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma od_walkE1 : forall (usp S1 F : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 t3 t4 t5 t6 : word) FR fc (m : mem),
  mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = ex_regs 0x66ae8 (Z_to_bv 64 0x97278) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (F + 192)) (Z_to_bv 64 0) (Z_to_bv 64 49) a3 a4 a5 a6 a7 s2 s3 F
                   s5 s6 s8 s9 t3 t4 t5 t6 FR fc m)
    (ex_regs OD_ERRX ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 F s5 s6 s8 s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros MI. unfold ex_regs, OD_ERRX.
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkE2 : forall (usp S1 F err : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 s9 t3 t4 t5 t6 : word)
    (b24 b25 b26 b27 b28 b29 b30 b31 : byte) (j248 : list byte) (c136 c112 c368 : word) FR fc (m : mem),
  0x679000 <= S1 -> S1 + 440 <= usp -> usp < 2^63 -> 0x679000 <= F -> F + 512 <= S1 -> F / 8 + 2147450880 + 64 <= S1 ->
  (F + 512 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 64 <= F) ->
  0 < err < 64 ->
  rw_cells bsegs m (F + 248) [CB 4 j248] ->
  rw_cells bsegs m (S1 + 168) [C8 (Z_to_bv 64 (F + 96))] ->
  rw_cells bsegs m (S1 + 368) [C8 c368] ->
  rw_cells bsegs m (S1 + 136) [C8 c136] ->
  rw_cells bsegs m (S1 + 112) [C8 c112] ->
  rw_cells bsegs m (S1 + 248) [C8 (Z_to_bv 64 (F / 8 + 2147450880))] ->
  rw_cells bsegs m (F / 8 + 2147450880 + 24) [C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = ex_regs 0x96fe8 ra S1 gp tp t0 t1 t2 usp c136 c112 (Z_to_bv 64 (-8)) a3 a4 c368 a6 a7 (Z_to_bv 64 (F + 96)) s3 F s5 s6 s8 s9 t3 t4 t5 t6 FR fc m1
      /\ munch [(F + 248, F + 252); (F / 8 + 2147450880 + 24, F / 8 + 2147450880 + 32)] m m1
      /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (F / 8 + 2147450880 + 24) (map C1 (repeat (Z_to_bv 8 (-8)) 8)))
    (ex_regs 0x97278 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 err) s3 F s5 s6 s8 s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros GLO SUS SPH FB FR0 FSH FSD ERR DOC FR168 FR368 FR136 FR112 FR248 SHD MI.
  unfold ex_regs in *. cbn [map repeat].
  pose proof (munch_refl [(F + 248, F + 252); (F / 8 + 2147450880 + 24, F / 8 + 2147450880 + 32)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (FD0 : 0 <= F / 8) by (apply Z.div_pos; lia).
  replace (F / 8 + 2147450880 + 24) with (F / 8 + 2147450904) in * by lia.
  replace (F / 8 + 2147450880 + 32) with (F / 8 + 2147450912) in * by lia.
  ls. zstep. zstep. zstep. zstep. rewrite (sx32_small err) by (clear - ERR; lia).
  zstep. zstep.
  utrap. zstep. zstep.
  if_cases K; zify_cond K; [exfalso; clear - K ERR; lia|]. clear K.
  zstep. zstep. do 8 ls. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Lemma od_walkE2c : forall (usp S1 F COPY : Z) (ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 t3 t4 t5 t6 : word) FR fc (m : mem),
  mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = ex_regs e_delarr (Z_to_bv 64 0x96ff0) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 COPY) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 F s5 s6 s8 s9 t3 t4 t5 t6 FR fc m)
    (ex_regs 0x96fe8 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 COPY) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 F s5 s6 s8 s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros MI. unfold ex_regs, e_delarr in *.
  zstep. if_false. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkE2n : forall (usp S1 F fl : Z) (ra gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < fl < 2^63 -> mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = ex_regs 0x96ff0 ra S1 gp tp t0 t1 t2 usp a0 (Z_to_bv 64 fl) a2 a3 a4 a5 a6 a7 s2 s3 F s5 s6 s8 s9 t3 t4 t5 t6 FR fc m)
    (ex_regs 0x96fe8 ra S1 gp tp t0 t1 t2 usp a0 (Z_to_bv 64 fl) a2 a3 a4 a5 a6 a7 s2 s3 F s5 s6 s8 s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros FL MI. unfold ex_regs in *.
  zstep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkE3 : forall (usp S1 F SB : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 s9 t3 t4 t5 t6 : word) FR fc (m : mem),
  0x679000 <= S1 -> S1 + 440 <= usp -> usp < 2^63 -> 0x679000 <= F -> F + 512 <= S1 -> 0 < SB < 2^63 ->
  rw_cells bsegs m (F + 144) [C8 (Z_to_bv 64 SB)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = ex_regs e_delarr (Z_to_bv 64 0x97000) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 SB) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (F + 96)) s3 F s5 s6 s8 s9 t3 t4 t5 t6 FR fc m1
      /\ munch [(F + 144, F + 152)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (F + 144) [C8 (Z_to_bv 64 0)])
    (ex_regs 0x96ff0 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (F + 96)) s3 F s5 s6 s8 s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros GLO SUS SPH FB FR0 SBR PSB MI.
  unfold ex_regs, e_delarr in *.
  pose proof (munch_refl [(F + 144, F + 152)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. ls. zstep.
  if_cases K; zify_cond K; [exfalso; lia|]. clear K.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| eassumption].
Qed.

Lemma od_walkE4 : forall (usp S1 F IMPL : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 t3 t4 t5 t6 : word) FR fc (m : mem),
  0x679000 <= S1 -> S1 + 440 <= usp -> usp < 2^63 -> 0x679000 <= F -> F + 512 <= S1 -> 0 < IMPL < 2^63 ->
  rw_cells bsegs m (F + 104) [C8 (Z_to_bv 64 IMPL)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = tx_regs OD_TAIL ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 IMPL) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (F + 104)) s5 s6 s8 s9 F (Z_to_bv 64 (F + 192))
                   t3 t4 t5 t6 FR fc m1
      /\ munch [(F + 104, F + 112)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (F + 104) [C8 (Z_to_bv 64 0)])
    (ex_regs 0x97000 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 F s5 s6 s8 s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros GLO SUS SPH FB FR0 IMR PIM MI.
  unfold ex_regs, tx_regs, OD_TAIL in *.
  pose proof (munch_refl [(F + 104, F + 112)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. ls. zstep.
  if_cases K; zify_cond K; [|exfalso; lia]. clear K.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| eassumption].
Qed.
