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
  Sj_num_amem Atp_h_defsA Atp_h_findA Od_proB Od_setupw1B.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition oa_locals3 (F act D n : Z) (j0 j8 j16 j24 j136 j176 j264 j288 j336 j376 j425 j432 : list byte) : list cell :=
  [CB 8 j0; CB 8 j8; CB 8 j16; CB 96 j24; C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F); CB 32 j136; C8 (Z_to_bv 64 (F + 96)); CB 72 j176;
   C8 (Z_to_bv 64 (F / 8 + 2147450880)); C8 (Z_to_bv 64 act); CB 16 j264; C8 (Z_to_bv 64 (F + 224)); CB 40 j288; C8 (Z_to_bv 64 (F + 208)); CB 32 j336;
   C8 (Z_to_bv 64 (F + 200)); CB 24 j376; C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n); C1 (Z_to_bv 8 0); CB 7 j425; CB 8 j432].
Definition oa_shadow2 (t : list byte) : list cell :=
  map C1 (repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 0) 3 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 (-8)) 7
          ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 (-8)) 8 ++ repeat (Z_to_bv 8 (-13)) 4)
  ++ [CB 28 t].
Definition oa_W1t (S1 F : Z) : list ivl := [(S1, S1 + 440); (F / 8 + 2147450880, F / 8 + 2147450880 + 36)].

Lemma od_walk1t : forall (usp S1 F lo D n act : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j416 j425 j432 t : list byte) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> F / 8 + 2147450880 + 64 <= lo -> 0 <= F / 8 ->
  0x679000 <= lo -> lo <= S1 -> S1 + 440 <= usp - 104 -> usp < 2^63 ->
  rw_cells bsegs m S1 (oa_locals2 F D j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j416 j425 j432) ->
  rw_cells bsegs m (F / 8 + 2147450880) (oa_shadow1 t) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0x96b68) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (S1 + 408)) a2 a3 a4 a5 a6 (Z_to_bv 64 F)
                    (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 2147450880) (Z_to_bv 64 (F + 228)) s9 (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (F + 192))
                    t3 t4 t5 t6 FR fc ATPA_SPLITINTO m1
      /\ munch (oa_W1t S1 F) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 S1 (oa_locals3 F act D n j0 j8 j16 j24 j136 j176 j264 j288 j336 j376 j425 j432)
      /\ rw_cells bsegs m1 (F / 8 + 2147450880) (oa_shadow2 t))
    (oa_st1 0x96b14 usp S1 F gp tp t0 t1 t2 (Z_to_bv 64 act) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 n) s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO SLO FD GLO LSP LUSP SPH FRl FS MI.
  unfold oa_locals2, oa_locals3, oa_shadow1, oa_shadow2, oa_W1t, oa_st1, entry_st, ATPA_SPLITINTO in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(S1, S1 + 440); (F / 8 + 2147450880, F / 8 + 2147450880 + 36)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.

  ls. zstep. zstep. ls. zstep. zstep. zstep. ls. zstep. ls. ls. zstep. ls. ls. zstep. ls. ls. ls. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Definition lh_regs (pc : Z) (ra : word) (S1 : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 : word) (F : Z) (s9 : word)
    (t3 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
          s2 s3 s4 s5 s6 (Z_to_bv 64 2147450880) (Z_to_bv 64 (F + 228)) s9 (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (F + 192)) t3 t4 t5 t6)
     FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma od_walkLH0 : forall (ra : word) (usp S1 F : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 t3 t4 t5 t6 : word) FR fc (m : mem),
  evt bsegs (eq (lh_regs 0x96b70 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-16)) (Z_to_bv 64 16) s4 s5 s6 F s9 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96b68 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros. unfold lh_regs. zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkLHx : forall (ra : word) (usp S1 F A cap size : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < F -> F + 512 < 2^63 -> 0 <= A -> A + 16 * cap < 2^63 -> 1 <= size <= cap ->
  rw_cells bsegs m (F + 32) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * size)); C8 (Z_to_bv 64 (A + 16 * cap))] -> mem_inv bsegs m ->
  evt bsegs (eq (lh_regs 0x96bc0 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (A + 16 * size)) (Z_to_bv 64 A) s6 F s9 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96b70 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FH A0 AH SZ VC MI. unfold lh_regs.
  zstep. zstep. zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkLHs : forall (ra : word) (usp S1 F A : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < F -> F + 512 < 2^63 -> 0 <= A < 2^63 ->
  rw_cells bsegs m (F + 32) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * 0)); C8 (Z_to_bv 64 (A + 16 * 0))] -> mem_inv bsegs m ->
  evt bsegs (eq (lh_regs ATPA_EMPLS (Z_to_bv 64 0x96ba4) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (F + 32)) a1 a2 a3 a4 a5 a6 a7 s2 s3
                         (Z_to_bv 64 (A + 16 * 0)) (Z_to_bv 64 A) s6 F s9 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96b70 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FH A0 VC MI. unfold lh_regs, ATPA_EMPLS.

  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].
  zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].
  zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkLHr : forall (ra : word) (usp S1 F A E C : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s9 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < F -> F + 512 < 2^63 -> 16 < E < 2^63 -> E mod 8 = 0 ->
  rw_cells bsegs m (F + 32) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 E); C8 (Z_to_bv 64 C)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' : word),
      ms = lh_regs 0x96b70 ra S1 gp tp t0 t1 t2 usp a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-16)) (Z_to_bv 64 16) s4 s5 s6 F s9 t3 t4 t5 t6 FR fc m1
      /\ munch [(F + 40, F + 48)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (F + 32) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 E); C8 (Z_to_bv 64 C)])
    (lh_regs 0x96ba4 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-16)) (Z_to_bv 64 16) s4 s5 s6 F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FH ER E8 VC MI. unfold lh_regs.
  pose proof (munch_refl [(F + 40, F + 48)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

  ls. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. rewrite ?Sj_num_amem.land7_mod8.
  replace ((E + -16) mod 8) with 0 by (Z.div_mod_to_equations; lia).
  zstep. if_true.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.
