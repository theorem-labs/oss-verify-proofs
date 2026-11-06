(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zvw.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks D_defs D_kit D_clx Z87 Z82 Zpm Zpl Zq2 Z4a
  Z4e Z4l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition fa_shadow0 (ls : list (list byte)) (t : list byte) : list cell := map (fun l => CB 1 l) ls ++ [CB 4 t].
Definition fa_shadow1 (t : list byte) : list cell :=
  map C1 (repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 0) 3 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 (-8)) 10 ++ repeat (Z_to_bv 8 (-13)) 6)
  ++ [CB 4 t].

Definition fa_locals1 (j0 j1 j2 : list byte) (f : Z) (jo jr : list byte) (d n : Z) (j13 jn : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 f); CB 24 jo; CB 24 jr; C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 n); C1 (Z_to_bv 8 0); CB 7 j13; CB 16 jn].

Definition fa_W1 (sp' f : Z) : list ivl := [(sp', sp' + 120); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 28)].

Lemma fa_walk1 : forall (usp sp' f lo d n : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s7 s8 s9x s10x t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 jo jr j10 j11 j12 j13 jn h0 h1 h2 h3 t : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 28%nat ->
  0 < f -> f + 256 <= lo -> f / 8 + 2147450880 + 32 <= lo -> 0 <= f / 8 ->
  (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) ->
  0x669000 <= lo -> lo <= sp' -> sp' + 120 <= usp - 104 -> usp < 2^63 -> 0 <= d < 2^64 -> 0 <= n < 2^64 ->
  rw_cells asegs m sp' (fa_locals0 j0 j1 j2 j3 jo jr j10 j11 j12 j13 jn) ->
  rw_cells asegs m f (fz_hdr (CB 8 h0) (CB 8 h1) (CB 8 h2) h3) ->
  rw_cells asegs m (f / 8 + 2147450880) (fa_shadow0 ls t) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a2' a3' a4' : word),
      ms = entry_st (Z_to_bv 64 0x96b30) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (sp' + 80))
             a2' a3' a4' a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 n) (Z_to_bv 64 d) s7 s8
             (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6 F fc ATPA_SPLITINTO m1
      /\ munch (fa_W1 sp' f) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 sp' (fa_locals1 j0 j1 j2 f jo jr d n j13 jn)
      /\ rw_cells asegs m1 f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x1e899)) (C8 (Z_to_bv 64 0x969b0)) h3)
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (fa_shadow1 t))
    (MS (mkR (Z_to_bv 64 0x96a24) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
             s2x s3x s4x (Z_to_bv 64 n) (Z_to_bv 64 d) s7 s8 s9x s10x (Z_to_bv 64 2147450880) t3 t4 t5 t6)
        F (Z_to_bv 64 0x96a24) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS F0 FLO SLO FD SEP GLO LSP LUSP SPH DR NR FRl FH FS MI.
  do 28 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold entry_st, ATPA_SPLITINTO, fa_W1, fa_locals0, fa_locals1, fz_hdr, fa_shadow0, fa_shadow1 in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(sp', sp' + 120); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 28)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).

  zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; [| exfalso; lia].

  zstep. zstep. zstep. zstep. zstep. zstep. zstep. rewrite shr3_div.

  zstep. zstep. zstep. zstep. zstep.
  ls. ls. ls.

  zstep. zstep. ls. ls. ls. ls.
  zstep. do 24 ls.

  zstep. zstep. ls. ls. ls. ls. zstep. zstep. zstep.
  apply evt_done. do 4 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition eh_regs (pc : Z) (ra : word) (sp' : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f : Z) (s5 s6 s7 s8 : word) (t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) s5 s6 s7 s8
          (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma eh_exit : forall (pc : Z) (ra : word) (sp' : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f A cap size : Z)
    (s5 s6 s7 s8 t3 t4 t5 t6 : word) F fc (m : mem),
  (pc = 0x96b30 \/ (pc = 0x96b4c /\ s5 = Z_to_bv 64 16)) ->
  0 < f -> f + 256 < 2^63 -> 0 <= A -> A + 16 * cap < 2^63 -> 2 <= size <= cap ->
  rw_cells asegs m (f + 32) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * size)); C8 (Z_to_bv 64 (A + 16 * cap))] -> mem_inv asegs m ->
  evt asegs (eq (eh_regs 0x96b50 ra sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (16 * size)) a1 a2 a3 a4 a5 a6 a7 f (Z_to_bv 64 16) (Z_to_bv 64 A) s7 s8 t3 t4 t5 t6 F fc m))
    (eh_regs pc ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s5 s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros PC F0 FH A0 AH SZ SV MI. unfold eh_regs.
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  destruct PC as [-> | [-> ->]].
  - zstep. zstep. zstep. zstep. replace (A + 16 * size + - A) with (16 * size) by lia.
    zstep. if_cases K; zify_cond K; [| exfalso; lia].
    apply evt_done. cbv delta [mkR]. reflexivity.
  - zstep. zstep. zstep. zstep. replace (A + 16 * size + - A) with (16 * size) by lia.
    zstep. if_cases K; zify_cond K; [| exfalso; lia].
    apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma eh_call : forall (pc : Z) (ra : word) (sp' : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f A cap size : Z)
    (s5 s6 s7 s8 t3 t4 t5 t6 : word) F fc (m : mem),
  (pc = 0x96b30 \/ (pc = 0x96b4c /\ s5 = Z_to_bv 64 16)) ->
  0 < f -> f + 256 < 2^63 -> 0 <= A -> A + 16 * cap < 2^63 -> 0 <= size <= cap -> size < 2 ->
  rw_cells asegs m (f + 32) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * size)); C8 (Z_to_bv 64 (A + 16 * cap))] -> mem_inv asegs m ->
  evt asegs (eq (eh_regs ATPA_EMPL (Z_to_bv 64 0x96b4c) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (f + 32)) a1 a2 a3 a4 a5 a6 a7 f (Z_to_bv 64 16) (Z_to_bv 64 A) s7 s8 t3 t4 t5 t6 F fc m))
    (eh_regs pc ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s5 s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros PC F0 FH A0 AH SZ S2 SV MI. unfold eh_regs, ATPA_EMPL.
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  destruct PC as [-> | [-> ->]].
  - zstep. zstep. zstep. zstep. replace (A + 16 * size + - A) with (16 * size) by lia.
    zstep. if_cases K; zify_cond K; [exfalso; lia|].
    zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity.
  - zstep. zstep. zstep. zstep. replace (A + 16 * size + - A) with (16 * size) by lia.
    zstep. if_cases K; zify_cond K; [exfalso; lia|].
    zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.
