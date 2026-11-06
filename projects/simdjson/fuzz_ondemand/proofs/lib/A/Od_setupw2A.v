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
  Sj_num_amem Atp_h_defsA Od_proA Od_setupw1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition oa_locals3 (F act D n : Z) (j0 j8 j16 j24 j32 j104 j128 j176 j192 j216 j224 j240 j248 j352 j393 j400 : list byte) : list cell :=
  [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 72 j32; CB 24 j104; CB 48 j128; CB 8 j176; C8 (Z_to_bv 64 act); CB 8 j192;
   C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (F + 96)); CB 8 j216;
   CB 16 j224; CB 8 j240; CB 104 j248; CB 16 j352; C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n); C1 (Z_to_bv 8 0); CB 7 j393; CB 8 j400].

Definition oa_shadow2 (t : list byte) : list cell :=
  map C1 (repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 0) 3 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 (-8)) 7
          ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 (-8)) 8 ++ repeat (Z_to_bv 8 (-13)) 4)
  ++ [CB 28 t].

Definition oa_W1t (S1 F : Z) : list ivl := [(S1, S1 + 408); (F / 8 + 2147450880, F / 8 + 2147450880 + 36)].

Lemma od_walk1t : forall (usp S1 F lo D n act : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
    (j0 j8 j16 j24 j32 j104 j128 j176 j192 j200 j208 j216 j224 j240 j248 j352 j376 j384 j393 j400 t : list byte) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> F / 8 + 2147450880 + 64 <= lo -> 0 <= F / 8 ->
  0x66b000 <= lo -> lo <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 ->
  rw_cells asegs m S1 (oa_locals2 F act j0 j8 j16 j24 j32 j104 j128 j176 j192 j200 j208 j216 j224 j240 j248 j352 j376 j384 j393 j400) ->
  rw_cells asegs m (F / 8 + 2147450880) (oa_shadow1 t) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0x96ba4) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (S1 + 376)) a2 a3 a4 (Z_to_bv 64 F) a6 a7
                    (Z_to_bv 64 F) (Z_to_bv 64 2147450880) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 D) (Z_to_bv 64 (F + 192)) s7 s8 s9 s10
                    (Z_to_bv 64 (F / 8 + 2147450880)) t3 t4 t5 t6 FR fc ATPA_SPLITINTO m1
      /\ munch (oa_W1t S1 F) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 S1 (oa_locals3 F act D n j0 j8 j16 j24 j32 j104 j128 j176 j192 j216 j224 j240 j248 j352 j393 j400)
      /\ rw_cells asegs m1 (F / 8 + 2147450880) (oa_shadow2 t))
    (oa_st2 usp S1 F D n gp tp t0 t1 t2 a1 a2 a3 a4 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO SLO FD GLO LSP LUSP SPH FRl FS MI.
  unfold oa_W1t, oa_locals2, oa_locals3, oa_shadow1, oa_shadow2, oa_st2, entry_st, ATPA_SPLITINTO in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(S1, S1 + 408); (F / 8 + 2147450880, F / 8 + 2147450880 + 36)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. ls. ls. zstep. ls. ls. ls. ls. ls. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Definition lh_regs (pc : Z) (ra : word) (S1 : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (F : Z) (s5 s7 s8 s9 s10 : word) (t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 F) (Z_to_bv 64 2147450880) (Z_to_bv 64 (F + 32)) s5 (Z_to_bv 64 (F + 192)) s7 s8 s9 s10
          (Z_to_bv 64 (F / 8 + 2147450880)) t3 t4 t5 t6)
     FR (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma od_walkLH0 : forall (ra : word) (usp S1 F act : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 s10 t3 t4 t5 t6 : word)
    (j0 j192 j216 j224 j240 j248 : list byte) FR fc (m : mem),
  0x66b000 <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 ->
  rw_cells asegs m S1 [CB 184 j0; C8 (Z_to_bv 64 act); CB 8 j192; C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (F + 96)); CB 8 j216; CB 16 j224; CB 8 j240; CB 104 j248] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = lh_regs 0x96ba8 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F s5 s7 s8 s9 s10 t3 t4 t5 t6 FR fc m1
      /\ munch [(S1 + 240, S1 + 248)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 S1 [CB 184 j0; C8 (Z_to_bv 64 act); CB 8 j192; C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (F + 96)); CB 8 j216; CB 16 j224;
                               C8 (Z_to_bv 64 (F / 8 + 2147450880)); CB 104 j248])
    (lh_regs 0x96ba4 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F s5 s7 s8 s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros GLO LUSP SPH FRl MI. unfold lh_regs.
  pose proof (munch_refl [(S1 + 240, S1 + 248)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  ls.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Lemma od_walkLHx : forall (pc : Z) (ra : word) (usp S1 F A cap size : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 s10 t3 t4 t5 t6 : word) FR fc (m : mem),
  (pc = 0x96ba8 \/ pc = 0x96bbc) ->
  0 < F -> F + 512 < 2^63 -> 0 <= A -> A + 16 * cap < 2^63 -> 1 <= size <= cap ->
  rw_cells asegs m (F + 32) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * size)); C8 (Z_to_bv 64 (A + 16 * cap))] -> mem_inv asegs m ->
  evt asegs (eq (lh_regs 0x96bc0 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (A + 16 * size)) a1 a2 a3 a4 a5 a6 a7 F s5 (Z_to_bv 64 A) s8 s9 s10 t3 t4 t5 t6 FR fc m))
    (lh_regs pc ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F s5 s7 s8 s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros PC F0 FH A0 AH SZ SV MI. unfold lh_regs.
  assert (EF : bv_unsigned (Z_to_bv 64 (F + 32)) = F + 32) by (apply unsigned_lit; lia).
  destruct PC as [-> | ->].
  - zstep. zstep. zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia].
    apply evt_done. cbv delta [mkR]. reflexivity.
  - zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia].
    apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkLHc : forall (ra : word) (usp S1 F A cap : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 s10 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < F -> F + 512 < 2^63 -> 0 <= A -> A + 16 * cap < 2^63 ->
  rw_cells asegs m (F + 32) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * 0)); C8 (Z_to_bv 64 (A + 16 * cap))] -> mem_inv asegs m ->
  evt asegs (eq (lh_regs ATPA_EMPL (Z_to_bv 64 0x96bbc) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (F + 32)) a1 a2 a3 a4 a5 a6 a7 F s5 (Z_to_bv 64 A) s8 s9 s10 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96ba8 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 F s5 s7 s8 s9 s10 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FH A0 AH SV MI. unfold lh_regs, ATPA_EMPL.
  assert (EF : bv_unsigned (Z_to_bv 64 (F + 32)) = F + 32) by (apply unsigned_lit; lia).
  replace (A + 16 * 0) with A in SV by lia.
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.
