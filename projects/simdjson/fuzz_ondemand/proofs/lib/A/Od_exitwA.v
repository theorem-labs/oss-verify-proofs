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
  Sj_new Sj_num_amem Od_defsA Od_tailwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition xx_regs (pc : Z) (ra : word) (S1 : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 s2 : word) (F : Z)
    (s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
          s2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (F + 32)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     FR (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma od_walkX1 : forall (usp S1 F COPY : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (b24 b25 b26 b27 b28 b29 b30 b31 : byte) FR fc (m : mem),
  0x66b000 <= S1 -> S1 + 408 <= usp -> usp < 2^63 -> 0x66b000 <= F -> F / 8 + 2147450880 + 64 <= S1 -> 0 < COPY < 2^63 ->
  rw_cells asegs m (S1 + 240) [C8 (Z_to_bv 64 (F / 8 + 2147450880))] ->
  rw_cells asegs m (S1 + 160) [C8 (Z_to_bv 64 COPY)] ->
  rw_cells asegs m (F / 8 + 2147450880 + 24) [C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = tx_regs e_delarr (Z_to_bv 64 0x99d38) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 COPY) a1 a2 a3 a4 a5 a6 a7 s2 F s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 FR fc m1
      /\ munch [(F / 8 + 2147450880 + 24, F / 8 + 2147450880 + 32)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (F / 8 + 2147450880 + 24) (map C1 (repeat (Z_to_bv 8 (-8)) 8)))
    (xx_regs 0x99d04 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 F s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros GLO SUS SPH FB FSH CP FR240 FR160 SHD MI.
  unfold xx_regs, tx_regs, e_delarr in *. cbn [map repeat].
  pose proof (munch_refl [(F / 8 + 2147450880 + 24, F / 8 + 2147450880 + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (FD0 : 0 <= F / 8) by (apply Z.div_pos; lia).
  replace (F / 8 + 2147450880 + 24) with (F / 8 + 2147450904) in * by lia.
  replace (F / 8 + 2147450880 + 32) with (F / 8 + 2147450912) in * by lia.
  zstep. zstep. do 8 ls. zstep. zstep.
  if_cases K; zify_cond K; [exfalso; lia|]. clear K.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| eassumption].
Qed.

Lemma od_walkX2 : forall (usp S1 F SB : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) FR fc (m : mem),
  0x66b000 <= S1 -> S1 + 408 <= usp -> usp < 2^63 -> 0x66b000 <= F -> F + 512 <= S1 -> 0 < SB < 2^63 ->
  rw_cells asegs m (S1 + 208) [C8 (Z_to_bv 64 (F + 96))] ->
  rw_cells asegs m (F + 144) [C8 (Z_to_bv 64 SB)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a1' : word),
      ms = tx_regs e_delarr (Z_to_bv 64 OD_TAIL) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 SB) a1' a2 a3 a4 a5 a6 a7 s2 F s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 FR fc m1
      /\ munch [(F + 144, F + 152)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (F + 144) [C8 (Z_to_bv 64 0)])
    (tx_regs 0x99d38 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 F s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros GLO SUS SPH FB FR0 SBR FR208 PSB MI.
  unfold tx_regs, e_delarr, OD_TAIL in *.
  pose proof (munch_refl [(F + 144, F + 152)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. ls. zstep.
  if_cases K; zify_cond K; [exfalso; lia|]. clear K.
  zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| eassumption].
Qed.
