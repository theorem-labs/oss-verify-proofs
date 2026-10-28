(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_new Sj_h_dtor Sj_h_alloc Atp_fzwA Pj_pidwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation PIREG8 sp gp tp t0 t1 t2 RES P d len a0 a1 a2 a3 a4 a5 a6 a7 s8v s9v t3 t4 t5 t6 :=
  (mkR (Z_to_bv 64 0xb7aa0) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 ((P + 64) / 8 + 2147450880))
       a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) s8v s9v
       (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6) (only parsing).

Lemma pi_walk5a : forall (RES P d len : Z) (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= len <= 1048512 -> cli_got_nothrow m ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0xb7754) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 ((P + 64) / 8 + 2147450880))
                   (Z_to_bv 64 (len + 64)) (Z_to_bv 64 0x31890) a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24))
                   (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc e_newarr_nt m))
    (MS (PIREG8 sp gp tp t0 t1 t2 RES P d len (Z_to_bv 64 1048512) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (P + 24)) t3 t4 t5 t6)
        F (Z_to_bv 64 0xb7740) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LEN GN.
  unfold entry_st, e_newarr_nt, cli_got_nothrow in *.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pi_walk5b : forall (RES P d len : Z) (b0 b16 nas : byte) (p1 p17 p57 : list byte) (impl err tape sbuf dcap maxcap lbcap : word)
    (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  1048512 < len < 2^63 -> 0x6e0000 <= P -> P + 80 < 2^63 -> 0 < RES -> RES + 24 < 2^63 ->
  (forall m' : mem, munch [(P, P + 80)] m m' -> wmono bsegs m m' -> shz m' P 80) ->
  rw_cells bsegs m P (pid_cells b0 p1 impl b16 p17 err tape sbuf dcap maxcap nas p57 (Z_to_bv 64 0) lbcap) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0xb7a1c) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 (RES + 16))
             (Z_to_bv 64 RES) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7
             (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 0)
             (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc e_asan_memset m1
      /\ munch [(P, P + 80)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 P (pid_cells b0 p1 impl b16 p17 err tape sbuf dcap maxcap nas p57 (Z_to_bv 64 0) lbcap))
    (MS (PIREG8 sp gp tp t0 t1 t2 RES P d len (Z_to_bv 64 1048512) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (P + 24)) t3 t4 t5 t6)
        F (Z_to_bv 64 0xb7740) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LEN P0 PH R0 RH SHZ PC MI.
  unfold entry_st, e_asan_memset, pid_cells in *.
  pose proof (munch_refl [(P, P + 80)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (SHZ m MU WM (P + 64) ltac:(lia)) as RD0.
  zstep. if_cases K; zify_cond K; [| exfalso; lia].
  zstep.
  zstep. shz_norm. zstep. if_false.
  lstep. zstep. if_true.
  zstep. if_true.
  zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Lemma pi_walk6 : forall (RES P d len copy : Z) (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < copy -> copy + len + 64 < 2^63 -> 0 <= len ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0xb7774) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 ((P + 64) / 8 + 2147450880))
                   (Z_to_bv 64 (copy + len)) (Z_to_bv 64 0) (Z_to_bv 64 64) a3 a4 a5 a6 a7
                   (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 copy)
                   (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc e_asan_memset m))
    (MS (mkR (Z_to_bv 64 0xb7754) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 ((P + 64) / 8 + 2147450880))
             (Z_to_bv 64 copy) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24))
             (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6) F (Z_to_bv 64 0xb7754) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros C0 CH LEN.
  unfold entry_st, e_asan_memset in *.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. rewrite (ZBridge.zb_lxor_ones copy) by lia.
  zstep. if_cases KN; zify_cond KN; [exfalso; rewrite ?unsigned_lit in KN by lia; lia|].
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pi_walk7 : forall (usp RES P d len copy : Z) (b0 b16 nas : byte) (p1 p17 p57 : list byte) (impl err tape sbuf dcap maxcap lbcap : word)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c : word) F fc (m : mem),
  0 < copy < 2^63 -> 0 <= len < 2^63 -> 0x6e0000 <= P -> P + 80 <= usp - 112 -> usp < 2^63 ->
  (forall m' : mem, munch [(P, P + 80)] m m' -> wmono bsegs m m' -> shz m' P 80) ->
  rw_cells bsegs m P (pid_cells b0 p1 impl b16 p17 err tape sbuf dcap maxcap nas p57 (Z_to_bv 64 0) lbcap) ->
  rw_cells bsegs m (usp + -112) (pid_frame (C8 (Z_to_bv 64 (P + 24))) rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0xb7828) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 ((P + 64) / 8 + 2147450880))
             (Z_to_bv 64 copy) (Z_to_bv 64 d) (Z_to_bv 64 len) a3 a4 a5 a6 a7
             (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24))
             (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc e_asan_memcpy m1
      /\ munch [(P, P + 80)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 P (pid_cells b0 p1 impl b16 p17 err tape sbuf dcap maxcap nas p57 (Z_to_bv 64 copy) (Z_to_bv 64 len))
      /\ rw_cells bsegs m1 (usp + -112) (pid_frame (C8 (Z_to_bv 64 (P + 24))) rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c))
    (MS (mkR (Z_to_bv 64 0xb7774) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 ((P + 64) / 8 + 2147450880))
             a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 copy)
             (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6) F (Z_to_bv 64 0xb7774) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros C0 LEN P0 PLO SPH SHZ PC FR MI.
  unfold entry_st, e_asan_memcpy, pid_cells, pid_frame in *.
  pose proof (munch_refl [(P, P + 80)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUC : bv_unsigned (Z_to_bv 64 copy) = copy) by (apply unsigned_lit; lia).
  pose proof (SHZ m MU WM (P + 64) ltac:(lia)) as RD0.
  zstep.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_true.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (P + 72) ltac:(lia)) as RD1 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (P + 64) ltac:(lia)) as RD2 end.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Notation PIREGF ra sp gp tp t0 t1 t2 s1 RES P BUF blen a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
  (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1
       a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 blen) (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24))
       (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6) (only parsing).

Lemma pi_walk8a : forall (RES P d len copy : Z) (b0 b16 nas : byte) (p1 p17 p57 : list byte) (impl err tape sbuf dcap maxcap lbcap : word)
    (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  3 <= len < 2^63 -> 0x6e0000 <= P -> P + 80 < 2^63 ->
  rw_cells bsegs m P (pid_cells b0 p1 impl b16 p17 err tape sbuf dcap maxcap nas p57 (Z_to_bv 64 copy) lbcap) ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0xb784c) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 3)
                   (Z_to_bv 64 copy) (Z_to_bv 64 0x23a60) (Z_to_bv 64 3) a3 a4 a5 a6 a7
                   (Z_to_bv 64 len) (Z_to_bv 64 copy) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24))
                   (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc e_memcmp m))
    (MS (PIREGF (Z_to_bv 64 0xb7828) sp gp tp t0 t1 t2 (Z_to_bv 64 ((P + 64) / 8 + 2147450880)) RES P d len a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb7828) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LEN P0 PH PC.
  unfold entry_st, e_memcmp, pid_cells in *.
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pi_walk8b : forall (RES P d len copy : Z) (b0 b16 nas : byte) (p1 p17 p57 : list byte) (impl err tape sbuf dcap maxcap lbcap : word)
    (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= len < 3 -> 0x6e0000 <= P -> P + 80 < 2^63 ->
  rw_cells bsegs m P (pid_cells b0 p1 impl b16 p17 err tape sbuf dcap maxcap nas p57 (Z_to_bv 64 copy) lbcap) ->
  evt bsegs (eq (MS (PIREGF (Z_to_bv 64 0xb7828) sp gp tp t0 t1 t2 (Z_to_bv 64 ((P + 64) / 8 + 2147450880)) RES P copy len (Z_to_bv 64 3) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xb785c) fc None m (seg_rom bsegs)))
    (MS (PIREGF (Z_to_bv 64 0xb7828) sp gp tp t0 t1 t2 (Z_to_bv 64 ((P + 64) / 8 + 2147450880)) RES P d len a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb7828) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LEN P0 PH PC.
  unfold pid_cells in *.
  zstep. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pi_walk8c : forall (RES P len copy : Z) (r : word)
    (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  3 <= len < 2^63 -> 0 < copy -> copy + len < 2^63 ->
  evt bsegs (fun ms => exists BUF blen, ((BUF = copy /\ blen = len) \/ (BUF = copy + 3 /\ blen = len - 3)) /\
                ms = MS (PIREGF (Z_to_bv 64 0xb784c) sp gp tp t0 t1 t2 (Z_to_bv 64 3) RES P BUF blen r a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xb785c) fc None m (seg_rom bsegs))
    (MS (PIREGF (Z_to_bv 64 0xb784c) sp gp tp t0 t1 t2 (Z_to_bv 64 3) RES P copy len r a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb784c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LEN C0 CH.
  zstep. if_cases K.
  - apply evt_done. exists copy, len. split; [left; split; reflexivity|]. cbv delta [mkR]. reflexivity.
  - zstep. zstep. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|]. zstep.
    apply evt_done. exists (copy + 3), (len - 3). split; [right; split; reflexivity|]. cbv delta [mkR]. reflexivity.
Qed.
