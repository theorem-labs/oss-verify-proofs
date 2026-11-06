(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ZBridge ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Od_hbaseA
  Sj_new Sj_num_amem Atp_h_defsA Od_hkit0A Od_lkitB Od_proB Od_setup_defsB Od_setupw1B Od_setupw2B.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ asan_load_hook | solve_load_image | solve_load_base ].

Definition od_lowM (F act : Z) (j0 j112 j136 j144 j176 j264 j288 j336 j376 : list byte) : list cell :=
  [CB 112 j0; CB 8 j112; C8 (wz F); C8 (wz F); CB 8 j136; CB 24 j144; C8 (wz (F + 96)); CB 72 j176; C8 (wz (F / 8 + 2147450880)); C8 (wz act); CB 16 j264;
   C8 (wz (F + 224)); CB 40 j288; C8 (wz (F + 208)); CB 32 j336; C8 (wz (F + 200)); CB 8 j376].

Definition oa_WB1 (F : Z) : list ivl := [(F + 96, F + 97); (F / 8 + 2147450892, F / 8 + 2147450899)].

Lemma od_walkB1 : forall (ra : word) (usp S1 F lo act : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 t3 t4 t5 t6 : word)
    (b12 b13 b14 b15 b16 b17 b18 : byte) (p0 j0 j112 j136 j144 j176 j264 j288 j336 j376 jp : list byte) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> F / 8 + 2147450880 + 64 <= lo -> 0 <= F / 8 ->
  (F + 512 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 64 <= F) ->
  0x679000 <= lo -> lo <= S1 -> S1 + 440 <= usp - 104 -> usp < 2^63 ->
  rw_cells bsegs m S1 (od_lowM F act j0 j112 j136 j144 j176 j264 j288 j336 j376) ->
  rw_cells bsegs m (F + 96) [CB 1 p0; CB 7 jp] ->
  rw_cells bsegs m (F / 8 + 2147450892) [C1 b12; C1 b13; C1 b14; C1 b15; C1 b16; C1 b17; C1 b18] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = lh_regs 0x66ae8 (Z_to_bv 64 0x96bfc) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (F + 104)) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7
                   (Z_to_bv 64 (F + 96)) s3 (Z_to_bv 64 (F + 104)) s5 s6 F s9 t3 t4 t5 t6 FR fc m1
      /\ munch (oa_WB1 F) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (F + 96) [C1 (Z_to_bv 8 0); CB 7 jp]
      /\ rw_cells bsegs m1 (F / 8 + 2147450892) (map C1 (repeat (Z_to_bv 8 0) 7)))
    (lh_regs 0x96bc0 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO SLO FD SEP GLO LSP LUSP SPH LOWF PAR SHP MI.
  unfold lh_regs, oa_WB1, od_lowM, wz in *. cbn [map repeat].
  pose proof (munch_refl [(F + 96, F + 97); (F / 8 + 2147450892, F / 8 + 2147450899)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  zstep. do 7 ls. zstep. ls. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma od_walkB2 : forall (ra : word) (usp S1 F lo : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s9 t3 t4 t5 t6 : word)
    (jb jc : list byte) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> 0x679000 <= lo -> lo <= S1 -> S1 + 440 <= usp - 104 -> usp < 2^63 ->
  rw_cells bsegs m (F + 120) [CB 8 jb; CB 8 jc] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = lh_regs 0x66ae8 (Z_to_bv 64 0x96c24) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (F + 136)) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7
                   (Z_to_bv 64 (F + 96)) s3 s4 s5 (Z_to_bv 64 (F + 136)) F s9 t3 t4 t5 t6 FR fc m1
      /\ munch [(F + 120, F + 136)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (F + 120) [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 1024)])
    (lh_regs 0x96bfc ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (F + 96)) s3 s4 s5 s6 F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO GLO LSP LUSP SPH PAR MI.
  unfold lh_regs in *.
  pose proof (munch_refl [(F + 120, F + 136)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. zstep. zstep. ls. ls. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Lemma od_walkB3c : forall (ra : word) (usp S1 F A p0 len0 : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s9 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < A -> A + 16 < 2^63 -> A mod 8 = 0 -> 0 <= len0 <= 0xfffc0 ->
  shz m A 16 -> rw_cells bsegs m A [C8 (Z_to_bv 64 p0); C8 (Z_to_bv 64 len0)] -> cli_got_nothrow m -> mem_inv bsegs m ->
  evt bsegs (eq (lh_regs e_newarr_nt (Z_to_bv 64 0x96c84) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (len0 + 64)) (Z_to_bv 64 0x2cd30) a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 len0) s3 s4 (Z_to_bv 64 (len0 + 64)) s6 F (Z_to_bv 64 p0) t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96c24 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 A) s6 F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros A0 AH A8 LR SHZ VE GOT MI.
  unfold lh_regs, e_newarr_nt, cli_got_nothrow in *.

  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. rewrite ?Sj_num_amem.land7_mod8. rewrite A8. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. rewrite ?lbu_z8. zstep. if_true.
  zstep. rewrite shr3_div. zstep. zstep. rewrite ?lbu_z8. zstep. if_true.
  zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkB3n : forall (ra : word) (usp S1 F A p0 len0 : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s9 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < A -> A + 16 < 2^63 -> A mod 8 = 0 -> 0xfffc0 < len0 < 2^26 ->
  shz m A 16 -> rw_cells bsegs m A [C8 (Z_to_bv 64 p0); C8 (Z_to_bv 64 len0)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists a0' a1',
               ms = lh_regs 0x96ce8 ra S1 gp tp t0 t1 t2 usp a0' a1' a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 len0) s3 s4 (Z_to_bv 64 A) s6 F s9 t3 t4 t5 t6 FR fc m)
    (lh_regs 0x96c24 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 A) s6 F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros A0 AH A8 LR SHZ VE MI.
  unfold lh_regs in *.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. rewrite ?Sj_num_amem.land7_mod8. rewrite A8. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. rewrite ?lbu_z8. zstep. if_true.
  zstep. rewrite shr3_div. zstep. zstep. rewrite ?lbu_z8. zstep. if_true.
  zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  apply evt_done. do 2 eexists. cbv delta [mkR]. reflexivity.
Qed.

Definition oa_WBU (S1 F : Z) : list ivl := [(S1 + 112, S1 + 144); (F + 136, F + 144); (F / 8 + 2147450904, F / 8 + 2147450912)].

Lemma od_walkBU : forall (ra : word) (usp S1 F lo act : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s9 t3 t4 t5 t6 : word)
    (b24 b25 b26 b27 b28 b29 b30 b31 : byte) (j0 j112 j136 j144 j176 j264 j288 j336 j376 : list byte) (x40 x48 : word) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> F / 8 + 2147450880 + 64 <= lo -> 0 <= F / 8 ->
  (F + 512 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 64 <= F) ->
  0x679000 <= lo -> lo <= S1 -> S1 + 440 <= usp - 104 -> usp < 2^63 ->
  rw_cells bsegs m S1 (od_lowM F act j0 j112 j136 j144 j176 j264 j288 j336 j376) ->
  rw_cells bsegs m (F + 136) [C8 x40; C8 x48] ->
  rw_cells bsegs m (F / 8 + 2147450904) [C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' a1' : word),
      ms = lh_regs 0x96dac ra S1 gp tp t0 t1 t2 usp a0' a1' a2 a3 a4 a5 a6 (Z_to_bv 64 0)
                   (Z_to_bv 64 0) s3 s4 (Z_to_bv 64 0) (Z_to_bv 64 (F + 136)) F s9 t3 t4 t5 t6 FR fc m1
      /\ munch (oa_WBU S1 F) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 S1 (od_lowB F act 1 0 j0 j144 j176 j264 j288 j336 j376)
      /\ rw_cells bsegs m1 (F + 136) [C8 (Z_to_bv 64 0); C8 x48]
      /\ rw_cells bsegs m1 (F / 8 + 2147450904) (map C1 (repeat (Z_to_bv 8 0) 8)))
    (lh_regs 0x96ce8 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (F + 136)) F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO SLO FD SEP GLO LSP LUSP SPH LOWF PAR SHD MI.
  unfold lh_regs, oa_WBU, od_lowM, od_lowB, wz in *. cbn [map repeat].
  pose proof (munch_refl [(S1 + 112, S1 + 144); (F + 136, F + 144); (F / 8 + 2147450904, F / 8 + 2147450912)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.

  zstep. zstep. zstep. do 8 ls. zstep. zstep. ls.

  zstep. zstep. ls. zstep. if_false. zstep. zstep. if_false. ls. zstep. zstep.
  apply evt_done. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma od_walkB4 : forall (ra : word) (usp S1 F COPY len0 : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s9 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < COPY -> COPY + len0 < 2^63 -> 0 <= len0 ->
  evt bsegs (eq (lh_regs 0x66ae8 (Z_to_bv 64 0x96ca4) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (COPY + len0)) (Z_to_bv 64 0) (Z_to_bv 64 64) a3 a4 a5 a6 a7
                   (Z_to_bv 64 len0) (Z_to_bv 64 COPY) s4 s5 s6 F s9 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96c84 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 COPY) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len0) s3 s4 s5 s6 F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros C0 CH L0. unfold lh_regs.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep.
  rewrite (zb_lxor_ones COPY) by lia.
  if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkB5c : forall (ra : word) (usp S1 F COPY p0 len0 : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) FR fc (m : mem),
  0 < len0 < 2^63 ->
  evt bsegs (eq (lh_regs 0x6664c (Z_to_bv 64 0x96cb8) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 COPY) (Z_to_bv 64 p0) (Z_to_bv 64 len0) a3 a4 a5 a6 a7
                   (Z_to_bv 64 len0) (Z_to_bv 64 COPY) s4 s5 s6 F (Z_to_bv 64 p0) t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96ca4 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len0) (Z_to_bv 64 COPY) s4 s5 s6 F (Z_to_bv 64 p0) t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros L0. unfold lh_regs.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkB5z : forall (ra : word) (usp S1 F len0 : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s9 t3 t4 t5 t6 : word) FR fc (m : mem),
  len0 = 0 ->
  evt bsegs (eq (lh_regs 0x96cb8 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len0) s3 s4 s5 s6 F s9 t3 t4 t5 t6 FR fc m))
    (lh_regs 0x96ca4 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len0) s3 s4 s5 s6 F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros ->. unfold lh_regs.
  zstep. if_true.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Definition oa_WB6 (S1 F : Z) : list ivl := [(S1 + 112, S1 + 144); (F / 8 + 2147450904, F / 8 + 2147450912)].

Lemma od_walkB6s : forall (ra : word) (usp S1 F lo act COPY len0 : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s9 t3 t4 t5 t6 : word)
    (b24 b25 b26 b27 b28 b29 b30 b31 : byte) (j0 j112 j136 j144 j176 j264 j288 j336 j376 : list byte) (x40 x48 : word) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> F / 8 + 2147450880 + 64 <= lo -> 0 <= F / 8 ->
  (F + 512 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 64 <= F) ->
  0x679000 <= lo -> lo <= S1 -> S1 + 440 <= usp - 104 -> usp < 2^63 -> 0 <= len0 < 3 -> 0 <= COPY < 2^63 ->
  rw_cells bsegs m S1 (od_lowM F act j0 j112 j136 j144 j176 j264 j288 j336 j376) ->
  rw_cells bsegs m (F + 136) [C8 x40; C8 x48] ->
  rw_cells bsegs m (F / 8 + 2147450904) [C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' a1' : word),
      ms = lh_regs 0x96dac ra S1 gp tp t0 t1 t2 usp a0' a1' a2 a3 a4 a5 a6 (Z_to_bv 64 COPY)
                   (Z_to_bv 64 len0) (Z_to_bv 64 COPY) s4 (Z_to_bv 64 COPY) (Z_to_bv 64 (F + 136)) F s9 t3 t4 t5 t6 FR fc m1
      /\ munch (oa_WBU S1 F) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 S1 (od_lowB F act 0 COPY j0 j144 j176 j264 j288 j336 j376)
      /\ rw_cells bsegs m1 (F + 136) [C8 (Z_to_bv 64 len0); C8 x48]
      /\ rw_cells bsegs m1 (F / 8 + 2147450904) (map C1 (repeat (Z_to_bv 8 0) 8)))
    (lh_regs 0x96cb8 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len0) (Z_to_bv 64 COPY) s4 (Z_to_bv 64 (len0 + 64)) (Z_to_bv 64 (F + 136))
       F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO SLO FD SEP GLO LSP LUSP SPH LR CR LOWF PAR SHD MI.
  unfold lh_regs, oa_WBU, od_lowM, od_lowB, wz in *. cbn [map repeat].
  pose proof (munch_refl [(S1 + 112, S1 + 144); (F + 136, F + 144); (F / 8 + 2147450904, F / 8 + 2147450912)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.

  ls. zstep. do 8 ls. zstep. zstep.

  zstep. zstep. ls. zstep.
  replace (len0 + 64 + - len0) with 64 by lia. if_false.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  ls. zstep. zstep.
  apply evt_done. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma od_walkB6b : forall (ra : word) (usp S1 F lo act COPY len0 : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s9 t3 t4 t5 t6 : word)
    (b24 b25 b26 b27 b28 b29 b30 b31 : byte) (j0 j112 j136 j144 j176 j264 j288 j336 j376 : list byte) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> F / 8 + 2147450880 + 64 <= lo -> 0 <= F / 8 ->
  (F + 512 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 64 <= F) ->
  0x679000 <= lo -> lo <= S1 -> S1 + 440 <= usp - 104 -> usp < 2^63 -> 3 <= len0 < 2^26 -> 0 <= COPY < 2^63 ->
  rw_cells bsegs m S1 (od_lowM F act j0 j112 j136 j144 j176 j264 j288 j336 j376) ->
  rw_cells bsegs m (F / 8 + 2147450904) [C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = lh_regs e_memcmp (Z_to_bv 64 0x96d88) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 COPY) (Z_to_bv 64 BOM_LIT) (Z_to_bv 64 3) a3 a4 a5 a6 (Z_to_bv 64 COPY)
                   (Z_to_bv 64 len0) (Z_to_bv 64 3) s4 (Z_to_bv 64 COPY) (Z_to_bv 64 (F + 136)) F s9 t3 t4 t5 t6 FR fc m1
      /\ munch (oa_WB6 S1 F) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 S1 (od_lowB F act 0 COPY j0 j144 j176 j264 j288 j336 j376)
      /\ rw_cells bsegs m1 (F / 8 + 2147450904) (map C1 (repeat (Z_to_bv 8 0) 8)))
    (lh_regs 0x96cb8 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len0) (Z_to_bv 64 COPY) s4 (Z_to_bv 64 (len0 + 64)) (Z_to_bv 64 (F + 136))
       F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO SLO FD SEP GLO LSP LUSP SPH LR CR LOWF SHD MI.
  unfold lh_regs, oa_WB6, od_lowM, od_lowB, wz, e_memcmp, BOM_LIT in *. cbn [map repeat].
  pose proof (munch_refl [(S1 + 112, S1 + 144); (F / 8 + 2147450904, F / 8 + 2147450912)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  ls. zstep. do 8 ls. zstep. zstep.
  zstep. zstep. ls. zstep. replace (len0 + 64 + - len0) with 64 by lia. if_false.
  zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].

  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma od_walkB7n : forall (ra r : word) (usp S1 F lo COPY len0 : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s9 t3 t4 t5 t6 : word)
    (x40 x48 : word) FR fc (m : mem),
  r <> Z_to_bv 64 0 -> 0 < F -> F + 512 <= lo -> 0x679000 <= lo -> lo <= S1 -> S1 + 440 <= usp - 104 -> usp < 2^63 -> 0 <= len0 < 2^26 ->
  rw_cells bsegs m (F + 136) [C8 x40; C8 x48] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' : word),
      ms = lh_regs 0x96dac ra S1 gp tp t0 t1 t2 usp a0' a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 len0) s3 s4 (Z_to_bv 64 COPY) (Z_to_bv 64 (F + 136)) F s9 t3 t4 t5 t6 FR fc m1
      /\ munch [(F + 136, F + 144)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (F + 136) [C8 (Z_to_bv 64 len0); C8 x48])
    (lh_regs 0x96d88 ra S1 gp tp t0 t1 t2 usp r a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len0) s3 s4 (Z_to_bv 64 COPY) (Z_to_bv 64 (F + 136)) F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros RNZ F0 FLO GLO LSP LUSP SPH LR PAR MI. unfold lh_regs.
  pose proof (munch_refl [(F + 136, F + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (SH32 : Z.shiftr len0 32 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  zstep. if_cases K; [| exfalso; apply RNZ; apply bv_eq; zify_cond K; rewrite ?unsigned_lit in K by lia; rewrite unsigned_lit by lia; lia].

  zstep. rewrite ?SH32. ls. zstep. if_true.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Lemma od_walkB7b : forall (ra : word) (usp S1 F lo COPY len0 : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s9 t3 t4 t5 t6 : word)
    (x40 x48 : word) FR fc (m : mem),
  0 < COPY -> COPY + 3 < 2^63 -> 3 <= len0 < 2^26 ->
  0 < F -> F + 512 <= lo -> 0x679000 <= lo -> lo <= S1 -> S1 + 440 <= usp - 104 -> usp < 2^63 ->
  rw_cells bsegs m (F + 136) [C8 x40; C8 x48] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' : word),
      ms = lh_regs 0x96dac ra S1 gp tp t0 t1 t2 usp a0' a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (len0 - 3)) (Z_to_bv 64 3) s4 (Z_to_bv 64 (COPY + 3)) (Z_to_bv 64 (F + 136)) F s9 t3 t4 t5 t6 FR fc m1
      /\ munch [(F + 136, F + 144)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (F + 136) [C8 (Z_to_bv 64 (len0 - 3)); C8 x48])
    (lh_regs 0x96d88 ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len0) (Z_to_bv 64 3) s4 (Z_to_bv 64 COPY) (Z_to_bv 64 (F + 136))
       F s9 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros C0 CH LR F0 FLO GLO LSP LUSP SPH PAR MI. unfold lh_regs.
  pose proof (munch_refl [(F + 136, F + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (SH32 : Z.shiftr (len0 + -3) 32 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).

  zstep. if_false. zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. rewrite ?SH32. ls. zstep. if_true.
  replace (len0 + -3) with (len0 - 3) in * by lia.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.
