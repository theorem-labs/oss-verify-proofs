(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zvw Z4d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks Zkt Zi4 D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2 Zq3
  Sj_new Zpo Z4a Z4e Z4l Z4m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition fa_shadow2 (t : list byte) : list cell :=
  map C1 (repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 0) 3 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 0) 10 ++ repeat (Z_to_bv 8 (-13)) 6)
  ++ [CB 4 t].

Lemma fa_walk3 : forall (usp sp' f : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word)
    (t p1 p8 p16 p17 p20 p24 p48 p56 p57 p64 : list byte) (p0 : list byte) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= f / 8 -> f / 8 + 2147450880 + 32 < 2^63 ->
  (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) ->
  rw_cells asegs m (f / 8 + 2147450880) (fa_shadow1 t) ->
  rw_cells asegs m (f + 96) (fz_parser (CB 1 p0) p1 (CB 8 p8) (CB 1 p16) p17 (CB 4 p20) (CB 24 p24) (CB 8 p48) (CB 1 p56) p57 (CB 16 p64)) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0x96ba0) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 (f + 120)) (Z_to_bv 64 0) (Z_to_bv 64 24)
             a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6 s7 s8
             (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6 F fc e_asan_memset m1
      /\ munch [(f + 96, f + 120); (f / 8 + 2147450880 + 12, f / 8 + 2147450880 + 22)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (fa_shadow2 t)
      /\ rw_cells asegs m1 (f + 96) (fz_parser (C1 (Z_to_bv 8 0)) p1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) p17 (C4 (Z_to_bv 64 12)) (CB 24 p24) (CB 8 p48) (CB 1 p56) p57 (CB 16 p64)))
    (MS (mkR x1 (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 16) s6 s7 s8
             (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
        F (Z_to_bv 64 0x96b50) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH FD SH SEP FS FP MI.
  unfold entry_st, e_asan_memset, fa_shadow1, fa_shadow2, fz_parser in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f + 96, f + 120); (f / 8 + 2147450880 + 12, f / 8 + 2147450880 + 22)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 96)) = f + 96) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  do 10 ls.
  zstep. ls. ls. ls. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; eassumption.
Qed.

Lemma fa_walk4 : forall (usp sp' f : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word)
    (p1 p17 p24 p48 p56 p57 p64 : list byte) F fc (m : mem),
  0 < f -> f + 256 < 2^63 ->
  rw_cells asegs m (f + 96) (fz_parser (C1 (Z_to_bv 8 0)) p1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) p17 (C4 (Z_to_bv 64 12)) (CB 24 p24) (CB 8 p48) (CB 1 p56) p57 (CB 16 p64)) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0x96bc0) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 (f + 160)) (Z_to_bv 64 0) (Z_to_bv 64 16)
             a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6 s7 s8
             (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6 F fc e_asan_memset m1
      /\ munch [(f + 144, f + 153)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f + 96) (fz_parser (C1 (Z_to_bv 8 0)) p1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) p17 (C4 (Z_to_bv 64 12)) (CB 24 p24)
                                              (C8 (Z_to_bv 64 4294967295)) (C1 (Z_to_bv 8 0)) p57 (CB 16 p64)))
    (MS (mkR x1 (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6 s7 s8
             (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
        F (Z_to_bv 64 0x96ba0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH FP MI.
  unfold entry_st, e_asan_memset, fz_parser in *.
  pose proof (munch_refl [(f + 144, f + 153)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 96)) = f + 96) by (apply unsigned_lit; lia).
  zstep. zstep.
  ls. ls. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma fa_walk5_big : forall (usp sp' f A p0 l0 : Z) (rest : list cell) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= sp' -> sp' + 120 < 2^63 -> 0 <= A -> A + 16 < 2^63 -> 0 <= p0 < 2^64 -> 1048512 < l0 < 2^64 ->
  shz m A 16 -> rw_cells asegs m A (C8 (Z_to_bv 64 p0) :: C8 (Z_to_bv 64 l0) :: rest) -> mem_inv asegs m ->
  evt asegs (eq (entry_st (Z_to_bv 64 0x96c78) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
                   (Z_to_bv 64 (sp' + 56)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) a6 a7
                   (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 A) (Z_to_bv 64 l0) s8
                   (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6 F fc e_pid m))
    (MS (mkR x1 (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 A) s7 s8
             (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
        F (Z_to_bv 64 0x96bc0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH SP0 SPH A0 AH P0R L0R SHZ EL MI.
  unfold entry_st, e_pid in *.
  pose proof (SHZ A ltac:(lia)) as RD0. pose proof (SHZ (A + 8) ltac:(lia)) as RD1.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma fa_walk5_small : forall (usp sp' f A p0 l0 : Z) (rest : list cell) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= A -> A + 16 < 2^63 -> 0 <= p0 < 2^64 -> 0 <= l0 <= 1048512 ->
  shz m A 16 -> rw_cells asegs m A (C8 (Z_to_bv 64 p0) :: C8 (Z_to_bv 64 l0) :: rest) -> cli_got_nothrow m -> mem_inv asegs m ->
  evt asegs (eq (entry_st (Z_to_bv 64 0x96c08) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
                   (Z_to_bv 64 (l0 + 64)) (Z_to_bv 64 0x2cd70) a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 A) (Z_to_bv 64 l0) (Z_to_bv 64 p0)
                   (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6 F fc e_newarr_nt m))
    (MS (mkR x1 (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 A) s7 s8
             (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
        F (Z_to_bv 64 0x96bc0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH A0 AH P0R L0R SHZ EL GOT MI.
  unfold entry_st, e_newarr_nt, cli_got_nothrow in *.
  pose proof (SHZ A ltac:(lia)) as RD0. pose proof (SHZ (A + 8) ltac:(lia)) as RD1.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Definition sa_regs (pc : Z) (ra : word) (sp' : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f : Z) (s6 s7 s8 : word) (t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6 s7 s8
          (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma fa_walk6 : forall (usp sp' f A buf l0 p0 : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 < buf -> buf + l0 + 64 < 2^63 -> 0 <= l0 ->
  evt asegs (eq (sa_regs e_asan_memset (Z_to_bv 64 0x96c20) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (buf + l0)) (Z_to_bv 64 0) (Z_to_bv 64 64) a3 a4 a5 a6 a7 f
                        (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 p0) t3 t4 t5 t6 F fc m))
    (sa_regs 0x96c08 (Z_to_bv 64 0x96c08) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 f (Z_to_bv 64 A) (Z_to_bv 64 l0) (Z_to_bv 64 p0) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH B0 BH L0. unfold sa_regs, e_asan_memset.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma fa_walk7z : forall (usp sp' f buf p0 : Z) (ra : word) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= sp' -> sp' + 120 < 2^63 ->
  evt asegs (eq (sa_regs e_pid (Z_to_bv 64 0x96c50) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (sp' + 56)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 buf)
                        (Z_to_bv 64 0) (Z_to_bv 64 0) a6 a7 f (Z_to_bv 64 buf) (Z_to_bv 64 0) (Z_to_bv 64 p0) t3 t4 t5 t6 F fc m))
    (sa_regs 0x96c20 ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (Z_to_bv 64 buf) (Z_to_bv 64 0) (Z_to_bv 64 p0) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH. unfold sa_regs, e_pid.
  zstep. if_true.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma fa_walk7c : forall (usp sp' f buf l0 p0 : Z) (ra : word) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 < l0 < 2^64 ->
  evt asegs (eq (sa_regs e_asan_memcpy (Z_to_bv 64 0x96c34) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 buf) (Z_to_bv 64 p0) (Z_to_bv 64 l0) a3 a4 a5 a6 a7 f
                        (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 p0) t3 t4 t5 t6 F fc m))
    (sa_regs 0x96c20 ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 p0) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH L0. unfold sa_regs, e_asan_memcpy.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma fa_walk8 : forall (usp sp' f buf l0 p0 : Z) (ra : word) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= sp' -> sp' + 120 < 2^63 ->
  evt asegs (eq (sa_regs e_pid (Z_to_bv 64 0x96c50) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (sp' + 56)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 buf)
                        (Z_to_bv 64 l0) (Z_to_bv 64 0) a6 a7 f (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 p0) t3 t4 t5 t6 F fc m))
    (sa_regs 0x96c34 ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 p0) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH. unfold sa_regs, e_pid.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma fa_walk9 : forall (usp sp' f buf l0 p0 : Z) (ra : word) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 256 < 2^63 ->
  evt asegs (eq (sa_regs e_delarr (Z_to_bv 64 0x96c58) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 f
                        (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 p0) t3 t4 t5 t6 F fc m))
    (sa_regs 0x96c50 ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 p0) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH. unfold sa_regs, e_delarr.
  zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma fa_walk10 : forall (usp sp' f : Z) (ra : word) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word) F fc (m : mem),
  evt asegs (eq (sa_regs 0x96c78 ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m))
    (sa_regs 0x96c58 ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. unfold sa_regs. zstep. apply evt_done. reflexivity.
Qed.
