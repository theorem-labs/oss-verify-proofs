(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_h_defsA Pj_lftoi1A El_defsA El_lf1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition el_shadow0 (ls : list (list byte)) (t : list byte) : list cell := map (fun l => CB 1 l) ls ++ [CB 52 t].

Definition el_locals1 (j0 j1 j2 j3 j4 j5 j6 j7 j8 : list byte) (f : Z) (j10 j11 j12 j13 j15 jr : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 24 j8; C8 (Z_to_bv 64 f); CB 24 jr; CB 4 j10; CB 4 j11; CB 8 j12; CB 8 j13;
   C1 (Z_to_bv 8 0); CB 7 j15].

Definition el_W1 (sp' f : Z) : list ivl := [(sp' + 88, sp' + 96); (sp' + 144, sp' + 145); (f, f + 24); (shad f, shad f + 76)].

Definition lf0_st (pc : Z) (ra : word) (sp' : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f n d : Z) (s6 s9 : word) (s10 s11 : word)
    (t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 n) (Z_to_bv 64 d) s6 (Z_to_bv 64 SHB) (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma el_walk1 : forall (usp sp' f lo d n : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2x s3x s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 jr h0 h1 h2 h3 t : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 76%nat ->
  0 < f -> f + 1024 <= lo -> shad f + 128 <= lo -> 0 <= f / 8 ->
  (f + 1024 <= shad f \/ shad f + 128 <= f) ->
  SEGTOP_A <= lo -> lo <= sp' -> sp' + 152 <= usp - 104 -> usp < 2^63 -> 0 <= d < 2^64 -> 0 <= n < 2^64 ->
  rw_cells asegs m sp' (el_locals0 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 jr) ->
  rw_cells asegs m f (fz_hdr (CB 8 h0) (CB 8 h1) (CB 8 h2) h3) ->
  rw_cells asegs m (shad f) (el_shadow0 ls t) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = lf0_st 0xb1820 (Z_to_bv 64 0xb167c) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (-8)) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-13))
             (Z_to_bv 64 0x126fb) (Z_to_bv 64 0xb1608) a5 a6 a7 f n d s6 s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch (el_W1 sp' f) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 sp' (el_locals1 j0 j1 j2 j3 j4 j5 j6 j7 j8 f (j14 ++ firstn 3 j15) (skipn 3 j15) (firstn 8 jr) (firstn 8 (skipn 8 jr))
                                           (skipn 17 jr) (j10 ++ j11 ++ j12 ++ j13))
      /\ rw_cells asegs m1 f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x126fb)) (C8 (Z_to_bv 64 0xb1608)) h3)
      /\ rw_cells asegs m1 (shad f) (el_shadowA (-8) (-8) (-8) (-8) t))
    (MS (mkR (Z_to_bv 64 0xb167c) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
             s2x s3x (Z_to_bv 64 n) (Z_to_bv 64 d) s6 (Z_to_bv 64 SHB) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb167c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS F0 FLO SLO FD SEP GLO LSP LUSP SPH DR NR FRl FH FS MI.
  do 76 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold lf0_st, el_W1, el_locals0, el_locals1, fz_hdr, el_shadow0, el_shadowA, el_shbytesA, shad, SHB, SEGTOP_A in *. cbn [map app repeat] in *.
  pose proof FRl as [[WF _] _]. cbn [cells_wf cell_wf] in WF.
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L10 & L11 & L12 & L13 & L14 & L15 & LR & _).
  assert (FRl' : rw_cells asegs m sp' [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 24 j8; CB 8 j9;
      CB 24 (j10 ++ j11 ++ j12 ++ j13); CB 4 (j14 ++ firstn 3 j15); CB 4 (skipn 3 j15); CB 8 (firstn 8 jr); CB 8 (firstn 8 (skipn 8 jr));
      CB 1 (firstn 1 (skipn 16 jr)); CB 7 (skipn 17 jr)]).
  { destruct FRl as [[W B] R].
    do 1 (destruct j14 as [|? j14]; [discriminate L14|]). destruct j14; [| discriminate L14].
    do 7 (destruct j15 as [|? j15]; [discriminate L15|]). destruct j15; [| discriminate L15].
    do 24 (destruct jr as [|? jr]; [discriminate LR|]). destruct jr; [| discriminate LR].
    split; [split|].
    - cbn [cells_wf cell_wf firstn skipn app] in *. rewrite !length_app. destruct W as (W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & _).
      repeat split; try assumption; lia.
    - cbn [cells_bytes cbytes firstn skipn] in *. rewrite <- !app_assoc. cbn [app] in *. exact B.
    - exact R. }
  clear FRl L10 L11 L12 L13 L14 L15 LR. rename FRl' into FRl.
  set (k10 := j14 ++ firstn 3 j15) in *. set (k11 := skipn 3 j15) in *. set (k12 := firstn 8 jr) in *. set (k13 := firstn 8 (skipn 8 jr)) in *.
  set (k14 := firstn 1 (skipn 16 jr)) in *. set (k15 := skipn 17 jr) in *. set (kr := j10 ++ j11 ++ j12 ++ j13) in *.
  clearbody k10 k11 k12 k13 k14 k15 kr.
  pose proof (munch_refl [(sp' + 88, sp' + 96); (sp' + 144, sp' + 145); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 76)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
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
