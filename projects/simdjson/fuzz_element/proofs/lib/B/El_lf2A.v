(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_h_defsA Pj_lftoi1A El_defsA El_lf1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition el_shadow0 (ls : list (list byte)) (t : list byte) : list cell := map (fun l => CB 1 l) ls ++ [CB 52 t].

Definition el_locals1 (j0 j1 j2 j3 j4 j5 j6 j7 j8 : list byte) (f : Z) (j10 j11 j12 j13 j15 jr : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 24 j8; C8 (Z_to_bv 64 f); CB 4 j10; CB 4 j11; CB 8 j12; CB 8 j13;
   C1 (Z_to_bv 8 0); CB 7 j15; CB 24 jr].

Definition el_W1 (sp' f : Z) : list ivl := [(sp' + 88, sp' + 96); (sp' + 120, sp' + 121); (f, f + 24); (shad f, shad f + 76)].

Definition lf0_st (pc : Z) (ra : word) (sp' : Z) (gp tp t0 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f n d : Z) (s6 s7 s8 : word) (s10 s11 : word)
    (t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp t0 (Z_to_bv 64 f) t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 n) (Z_to_bv 64 d) s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma el_walk1 : forall (usp sp' f lo d n : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2x s3x s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 jr h0 h1 h2 h3 t : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 76%nat ->
  0 < f -> f + 1024 <= lo -> shad f + 128 <= lo -> 0 <= f / 8 ->
  (f + 1024 <= shad f \/ shad f + 128 <= f) ->
  SEGTOP_A <= lo -> lo <= sp' -> sp' + 152 <= usp - 104 -> usp < 2^63 -> 0 <= d < 2^64 -> 0 <= n < 2^64 ->
  rw_cells bsegs m sp' (el_locals0 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 jr) ->
  rw_cells bsegs m f (fz_hdr (CB 8 h0) (CB 8 h1) (CB 8 h2) h3) ->
  rw_cells bsegs m (shad f) (el_shadow0 ls t) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = lf0_st 0xb1ed0 (Z_to_bv 64 0xb1d2c) sp' gp tp t0 t2 usp (Z_to_bv 64 (-8)) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-13))
             (Z_to_bv 64 0x12737) (Z_to_bv 64 0xb1cb8) a5 a6 a7 f n d s6 s7 s8 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch (el_W1 sp' f) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 sp' (el_locals1 j0 j1 j2 j3 j4 j5 j6 j7 j8 f j10 j11 j12 j13 j15 jr)
      /\ rw_cells bsegs m1 f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x12737)) (C8 (Z_to_bv 64 0xb1cb8)) h3)
      /\ rw_cells bsegs m1 (shad f) (el_shadowA (-8) (-8) (-8) (-8) t))
    (MS (mkR (Z_to_bv 64 0xb1d2c) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
             s2x s3x (Z_to_bv 64 n) (Z_to_bv 64 d) s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb1d2c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS F0 FLO SLO FD SEP GLO LSP LUSP SPH DR NR FRl FH FS MI.
  do 76 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold lf0_st, el_W1, el_locals0, el_locals1, fz_hdr, el_shadow0, el_shadowA, el_shbytesA, shad, SHB, SEGTOP_A in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(sp' + 88, sp' + 96); (sp' + 120, sp' + 121); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 76)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).

  zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; [| exfalso; lia].

  ls. zstep. zstep. zstep. zstep. rewrite shr3_div.

  zstep. zstep. zstep. zstep. zstep.
  ls. ls. ls.

  zstep. zstep. ls. ls. ls. ls.
  zstep. do 72 ls.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  ls.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.
