(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface Sj_akit Sj_acps Sj_hkit Atp_fzwA Pj_lftoi1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition pj_shadow0 (ls : list (list byte)) (t : list byte) : list cell := map (fun l => CB 1 l) ls ++ [CB 48 t].
Definition pj_shadow_bytes : list byte :=
  repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 (-8)) 11 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 0) 10 ++ repeat (Z_to_bv 8 (-14)) 4
  ++ repeat (Z_to_bv 8 (-8)) 36 ++ repeat (Z_to_bv 8 (-13)) 10.
Definition pj_shadow1 (t : list byte) : list cell := map C1 pj_shadow_bytes ++ [CB 48 t].

Definition pj_locals1 (j0 j1 j2 j3 j4 j5 j6 : list byte) (f : Z) (jr : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; C8 (Z_to_bv 64 f); CB 24 jr].

Definition pj_W1 (sp' f : Z) : list ivl := [(sp', sp' + 88); (f, f + 24); (f + 160, f + 184); (f / 8 + 2147450880, f / 8 + 2147450880 + 80)].

Definition lf_regs (pc : Z) (ra : word) (sp' : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f n d : Z) (s7 s8 s9 : word)
    (t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 (f + 160)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 n) (Z_to_bv 64 d) s7 s8 s9 (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma pj_walk1 : forall (usp sp' f lo d n : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s7 s8 s9 s10x t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 j4 j5 j6 j7 jr h0 h1 h2 h3 t : list byte) (ls : list (list byte))
    (p0 p1 p8 p16 p17 p20 p24 p48 p56 p57 p64 : list byte) F fc (m : mem),
  length ls = 80%nat ->
  0 < f -> f + 1024 <= lo -> f / 8 + 2147450880 + 128 <= lo -> 0 <= f / 8 ->
  (f + 1024 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 128 <= f) ->
  0x6d6000 <= lo -> lo <= sp' -> sp' + 88 <= usp - 104 -> usp < 2^63 -> 0 <= d < 2^64 -> 0 <= n < 2^64 ->
  rw_cells bsegs m sp' (pj_locals0 j0 j1 j2 j3 j4 j5 j6 j7 jr) ->
  rw_cells bsegs m f (fz_hdr (CB 8 h0) (CB 8 h1) (CB 8 h2) h3) ->
  rw_cells bsegs m (f + 160) (fz_parser (CB 1 p0) p1 (CB 8 p8) (CB 1 p16) p17 (CB 4 p20) (CB 24 p24) (CB 8 p48) (CB 1 p56) p57 (CB 16 p64)) ->
  rw_cells bsegs m (f / 8 + 2147450880) (pj_shadow0 ls t) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = lf_regs e_asan_memset (Z_to_bv 64 0xb184c) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (f + 184)) (Z_to_bv 64 0) (Z_to_bv 64 24)
             (Z_to_bv 64 12) (Z_to_bv 64 0x13300) (Z_to_bv 64 0xb15fc) a6 a7 f n d (Z_to_bv 64 (f + 184)) s8 s9 t3 t4 t5 t6 F fc m1
      /\ munch (pj_W1 sp' f) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 sp' (pj_locals1 j0 j1 j2 j3 j4 j5 j6 f jr)
      /\ rw_cells bsegs m1 f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x13300)) (C8 (Z_to_bv 64 0xb15fc)) h3)
      /\ rw_cells bsegs m1 (f + 160) (fz_parser (C1 (Z_to_bv 8 0)) p1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) p17 (C4 (Z_to_bv 64 12)) (CB 24 p24) (CB 8 p48) (CB 1 p56) p57 (CB 16 p64))
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (pj_shadow1 t))
    (MS (mkR (Z_to_bv 64 0xb1670) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
             s2x s3x s4x (Z_to_bv 64 n) (Z_to_bv 64 d) s7 s8 s9 s10x (Z_to_bv 64 2147450880) t3 t4 t5 t6)
        F (Z_to_bv 64 0xb1670) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS F0 FLO SLO FD SEP GLO LSP LUSP SPH DR NR FRl FH FP FS MI.
  do 80 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold lf_regs, e_asan_memset, pj_W1, pj_locals0, pj_locals1, fz_hdr, fz_parser, pj_shadow0, pj_shadow1, pj_shadow_bytes in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(sp', sp' + 88); (f, f + 24); (f + 160, f + 184); (f / 8 + 2147450880, f / 8 + 2147450880 + 80)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).

  zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; [| exfalso; lia].

  zstep. zstep. zstep. zstep. zstep. zstep. rewrite shr3_div.

  zstep. zstep. zstep. zstep. zstep. zstep.
  ls. ls. ls.

  zstep. zstep. ls. ls. ls. ls.
  zstep. do 76 ls.

  assert (EP : bv_unsigned (Z_to_bv 64 (f + 160)) = f + 160) by (apply unsigned_lit; lia).
  ls. ls. ls. ls. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma pj_walk2 : forall (usp sp' f d n : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
    (p1 p17 p24 p48 p56 p57 p64 : list byte) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 ->
  rw_cells bsegs m (f + 160) (fz_parser (C1 (Z_to_bv 8 0)) p1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) p17 (C4 (Z_to_bv 64 12)) (CB 24 p24) (CB 8 p48) (CB 1 p56) p57 (CB 16 p64)) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = lf_regs e_asan_memset (Z_to_bv 64 0xb186c) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (f + 224)) (Z_to_bv 64 0) (Z_to_bv 64 16)
             a3 a4 a5 a6 a7 f n d (Z_to_bv 64 (f + 184)) s8 s9 t3 t4 t5 t6 F fc m1
      /\ munch [(f + 208, f + 217)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (f + 160) (fz_parser (C1 (Z_to_bv 8 0)) p1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) p17 (C4 (Z_to_bv 64 12)) (CB 24 p24)
                                              (C8 (Z_to_bv 64 4294967295)) (C1 (Z_to_bv 8 0)) p57 (CB 16 p64)))
    (lf_regs 0xb184c x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f n d (Z_to_bv 64 (f + 184)) s8 s9 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH FP MI.
  unfold lf_regs, e_asan_memset, fz_parser in *.
  pose proof (munch_refl [(f + 208, f + 217)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  zstep. zstep.
  ls. ls. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma pj_walk3 : forall (usp sp' f d n : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 <= sp' -> sp' + 88 < 2^63 -> mem_inv bsegs m ->
  evt bsegs (eq (lf_regs e_pid (Z_to_bv 64 0xb1888) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (sp' + 64)) (Z_to_bv 64 (f + 160)) (Z_to_bv 64 (f + 184))
                 (Z_to_bv 64 d) (Z_to_bv 64 n) (Z_to_bv 64 1) a6 a7 f n d (Z_to_bv 64 (f + 184)) s8 s9 t3 t4 t5 t6 F fc m))
    (lf_regs 0xb186c x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f n d (Z_to_bv 64 (f + 184)) s8 s9 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH MI. unfold lf_regs, e_pid.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.
