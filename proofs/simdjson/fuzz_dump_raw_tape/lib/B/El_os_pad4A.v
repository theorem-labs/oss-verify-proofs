(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_num_walk Sj_stage1_kit Pj_os_kit El_os_pad.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_defsA Atp_fzwA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_os_put1A Pj_os_put2A Pj_os_put3A.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import El_os_pad3A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma pad_segAW : forall (S sp2 f OS BUF N FILL W lo : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s7 s9 s11 t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 j4 j5 j6 j8 j9 j10 h0 h1 h2 : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 16%nat ->
  0 < f -> f + 128 <= lo -> 0xd9c00 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < OS -> OS + 288 <= lo -> OS mod 16 = 0 -> OS / 8 + 2147450880 + 37 <= lo ->
  (OS + 288 <= f \/ f + 128 <= OS) -> (f + 128 <= OS / 8 + 2147450880 \/ (OS + 288) / 8 + 2147450880 <= f) ->
  (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= OS) ->
  0x7fff7f800000 <= lo -> lo <= sp2 -> S - 208 <= sp2 <= S - 192 -> S < 2^63 -> 0 < BUF -> 0 < N -> BUF + N < 2^63 -> 0 <= FILL < 256 -> N < W -> W < 2^62 ->
  bytes_at bsegs m (OS / 8 + 2147450880) (repeat z8 36) ->
  rw_cells bsegs m sp2 (pad_locals0 j0 j1 j2 j3 j4 j5 j6 (BUF + N) j8 j9 j10) -> rw_cells bsegs m (OS + 160) [C8 (wz W)] ->
  rw_cells bsegs m f [CB 8 h0; CB 8 h1; CB 8 h2] -> rw_cells bsegs m (f / 8 + 2147450880) (map (fun l => CB 1 l) ls) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a0' a1' a2' : word) (m1 : mem),
      ms = MS (mkR (wz 0xb1a28) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0' a1' a2' (wz (-13)) (wz (-8)) a5 a6 a7
                   (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz 0) (wz f) (wz BUF) (wz (W - N)) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
              F (wz 0xb1b68) fc None m1 (seg_rom bsegs)
      /\ munch [(sp2, sp2 + 88); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 sp2 [CB 8 j0; CB 8 j1; CB 8 j2; C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz (OS + 160)); C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j8; CB 8 j9; C8 (wz f)]
      /\ rw_cells bsegs m1 (OS + 160) [C8 (wz W)]
      /\ rw_cells bsegs m1 f [C8 (wz 0x41b58ab3); C8 (wz 0x16a74); C8 (wz 0xb19a4)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 pad_sh12 ++ map (fun l => CB 1 l) (skipn 12 ls)))
    (MS (mkR (wz 0xb1a28) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz f) a1 a2 a3 a4 a5 a6 a7
             s2 (wz OS) (wz 2147450880) (wz FILL) (wz (OS + 136)) s7 (wz BUF) s9 (wz BUF) s11 t3 t4 t5 t6)
        F (wz 0xb1a28) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS F0 FLO FD8 SLO SEP O0 OLO O16 OSLO OF OSH OSH2 LOW LSP SP2R SPH B0 N0 BNH FIR NW WR SHZ0 FRl WID FH FS MI.
  do 16 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold pad_sh12, pad_locals0 in *. cbn [map app repeat skipn] in *.
  pose proof (munch_refl [(sp2, sp2 + 88); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp2) = sp2) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (OS + 160)) = OS + 160) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (SHZ : forall m', munch [(sp2, sp2 + 88); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m' -> wmono bsegs m m' -> shz m' OS 288).
  { intros m' MU' _. change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run m' OS 36); [clear - O16; Z.div_mod_to_equations; lia| lia|].
    eapply bytes_at_agree; [exact SHZ0|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx OSLO LSP OSH OF FD8 F0 O0. split; [| split; [| split; [| exact I]]]; Z.div_mod_to_equations; lia. }
  change (id (bytes_at bsegs m (OS / 8 + 2147450880) (repeat z8 36))) in SHZ0.
  do 3 zstep.
  zstep. if_cases K0; zify_cond K0; [| exfalso; lia].
  lstep.
  do 3 zstep. zstep. rewrite shr3_div. do 5 zstep.
  do 3 lstep.
  zstep. zstep.
  do 12 ls.
  zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
  zstep.    replace (OS + 136 + 24) with (OS + 160) by lia.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ (OS + 160). zstep. shz_norm. zstep. if_false.
  lstep.
  zstep.
  zstep.
  zstep.    replace (BUF + N - BUF) with N by lia.
  lstep.
  zstep. if_lia.
  zstep.
  zstep.
  zstep.
  zstep. if_cases Kc; zify_cond Kc; change 9223372036854775808 with (2^63) in Kc; rewrite !zb_lxor_pow2_small in Kc by lia;
    (replace (2 ^ 63 <? N + 2 ^ 63) with true in Kc by (symmetry; apply Z.ltb_lt; lia));
    (replace (W - N + 2 ^ 63 <? W + 2 ^ 63) with true in Kc by (symmetry; apply Z.ltb_lt; lia)); [clear Kc| exfalso; apply Kc; reflexivity].
  lstep.
  zstep.    replace (BUF - BUF) with 0 by lia.
  zstep.
  replace (Z.land OS 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - O16; Z.div_mod_to_equations; lia).
  zstep. rewrite shr3_div. lstep.
  zstep. if_true.
  apply evt_done. eexists _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma sn_loopB : forall (k : nat) (p D : Z) (c : Z) (ra sp gp tp t0 t1 t2 s0 a0 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  D + 1 <= p -> p + Z.of_nat (S k) <= D + 24 -> 0 < D -> D + 24 < 2^63 -> 0 <= c < 256 ->
  (forall m', munch [(p, p + Z.of_nat (S k))] m m' -> wmono bsegs m m' -> shz m' D 24) ->
  wr_at bsegs m p (Z.of_nat (S k)) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a5' : word) (m1 : mem),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (wz c) a0 (wz (p + Z.of_nat (S k))) (wz (-1)) (wz (p + Z.of_nat (S k))) (wz 0) a5' a6 a7
                   s2 s3 (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz 0xb1fc4) fc None m1 (seg_rom bsegs)
      /\ munch [(p, p + Z.of_nat (S k))] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ bytes_at bsegs m1 p (repeat (Z_to_bv 8 c) (S k)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (wz c) a0 (wz p) (wz (-1)) (wz p) (wz (Z.of_nat (S k))) a5 a6 a7
             s2 s3 (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xb1f9c) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros p D c ra sp gp tp t0 t1 t2 s0 a0 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LP HP D0 DH RC SHZ WR MI.
  -
    change (Z.of_nat 1) with 1 in *.
    pose proof (munch_refl [(p, p + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
    destruct (wr_at_rw_CB m p 1 WR ltac:(lia)) as (j & X). change (Z.to_nat 1) with 1%nat in X.
    zstep. rewrite shr3_div. zstep.
    shz_pose SHZ p. zstep. shz_norm. zstep. if_false.
    ls.
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?Z.mod_small in K0 by lia; lia|].
    do 3 zstep.
    zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?Z.mod_small in K1 by lia; lia|].
    apply evt_done. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [assumption|].
    cbn [repeat]. lazymatch goal with |- bytes_at _ ?mm _ _ => lazymatch goal with X' : rw_cells _ mm p _ |- _ => exact (rw_cells_bytes_at _ _ _ _ X') end end.
  -
    pose proof (munch_refl [(p, p + Z.of_nat (S (S k)))] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
    destruct (wr_at_rw_CB m p 1 (wr_at_sub m p (Z.of_nat (S (S k))) p 1 WR ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (j & X). change (Z.to_nat 1) with 1%nat in X.
    zstep. rewrite shr3_div. zstep.
    shz_pose SHZ p. zstep. shz_norm. zstep. if_false.
    ls.
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?Z.mod_small in K0 by lia; lia|].
    do 3 zstep.
    zstep. if_cases K1; zify_cond K1; [| exfalso; rewrite ?Z.mod_small in K1 by lia; lia].
    replace (Z.of_nat (S (S k)) + -1) with (Z.of_nat (S k)) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MU1 : munch _ m m1, WM1 : wmono _ m m1, X1 : rw_cells _ m1 p _ |- _ =>
      eapply evt_cut; [eapply (IH (p + 1) D c);
        [lia| lia| lia| lia| lia
        | intros m' MU' WM'; apply SHZ; [eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; cbn [outside] in *; lia| eapply munch_weaken; [| exact MU']; intros x Hx; cbn [outside] in *; lia]
                                        | eapply wmono_trans; [exact WM1| exact WM']]
        | eapply (wr_at_sub _ _ _ _ _ WR); lia
        | assumption]|];
      cbv beta; intros ms2 (a5' & m2 & -> & MU2 & WM2 & MI2 & BY2); apply evt_done;
      replace (p + 1 + Z.of_nat (S k)) with (p + Z.of_nat (S (S k))) by lia;
      eexists _, _; (split; [reflexivity|]);
      (split; [eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; cbn [outside] in *; lia| eapply munch_weaken; [| exact MU2]; intros x Hx; cbn [outside] in *; lia]|]);
      (split; [eapply wmono_trans; [exact WM1| exact WM2]|]); (split; [exact MI2|]);
      change (repeat (Z_to_bv 8 c) (S (S k))) with ([Z_to_bv 8 c] ++ repeat (Z_to_bv 8 c) (S k));
      apply (proj2 (bytes_at_app _ _ _ _ _)); split;
        [ apply (rw_cells_bytes_at bsegs m2 p [C1 (Z_to_bv 8 c)]); eapply rw_cells_agree_nw; [exact X1|]; apply (agree_of_munch _ _ _ _ MU2); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [lia| exact I]
        | cbn [length]; replace (p + Z.of_nat 1) with (p + 1) by lia; exact BY2 ]
      end end.
Qed.

Definition padW_locals (OS BUF N f : Z) (j0 j1 j2 j8 j9 : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz (OS + 160)); C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j8; CB 8 j9; C8 (wz f)].
Definition pad_sh12u : list byte := repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 0) 3 ++ repeat (Z_to_bv 8 (-13)) 5.

Lemma pad_w1 : forall (S sp2 f OS FILL ns lo : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word) (ls4 : list (list byte)) F fc (m : mem),
  length ls4 = 4%nat -> 0 < f -> f + 128 <= lo -> 0 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> lo < 2^63 -> 0 < ns < 2^63 ->
  rw_cells bsegs m (f / 8 + 2147450880) (map C1 pad_sh12 ++ map (fun l => CB 1 l) ls4) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb1b8c) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz (f + 32)) (wz ns) (wz FILL) a3 a4 a5 a6 a7
                   (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz 0) (wz f) (wz (f + 32)) (wz ns) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
              F (wz 0xb1e80) fc None m1 (seg_rom bsegs)
      /\ munch [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 7)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 pad_sh12u ++ map (fun l => CB 1 l) ls4))
    (MS (mkR (wz 0xb1a28) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0 a1 a2 a3 a4 a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz 0) (wz f) s8 (wz ns) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
        F (wz 0xb1b68) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS4 F0 FLO FD SLO LOH NS FS MI.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  unfold pad_sh12 in FS. cbn [map app repeat] in FS.
  pose proof (munch_refl [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 7)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep. if_cases K0; zify_cond K0; [exfalso; apply Bool.andb_false_iff in K0; destruct K0 as [K0|K0]; apply Z.ltb_ge in K0; lia|].
  zstep.
  do 3 ls.
  do 3 zstep.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  unfold pad_sh12u. cbn [map app repeat]. eassumption.
Qed.

Lemma sn_walk1B : forall (sp D n c lo : Z) (ra gp tp t0 t1 t2 a3 a4 a5 a6 a7 xs0 xs1 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (b1 : list byte) F fc (m : mem),
  stk bsegs m lo sp -> lo <= sp - 48 -> 0x6ce000 <= lo -> sp < 2^63 -> 0 < D -> D + 24 <= lo -> D mod 8 = 0 -> D / 8 + 2147450880 + 3 <= lo ->
  (D + 24 <= D / 8 + 2147450880 \/ D / 8 + 2147450880 + 3 <= D) ->
  1 <= n < 23 -> 0 <= c < 256 ->
  client_consts m -> bytes_at bsegs m (D / 8 + 2147450880) [z8; z8; z8] -> rw_cells bsegs m D [CB 1 b1] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR ra (wz (sp - 48)) gp tp t0 t1 t2 (wz n) (wz c) (wz (D + 1)) (wz (D + 1)) (wz (-1)) (wz (D + 1)) (wz n) a5 a6 a7
                   (wz D) xs3 (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz 0xb1f9c) fc None m1 (seg_rom bsegs)
      /\ munch [(sp - 48, sp); (D, D + 1)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (sp - 48)
      /\ rw_cells bsegs m1 (sp - 48) [C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 ra]
      /\ rw_cells bsegs m1 D [C1 (Z_to_bv 8 (2 * n))])
    (MS (mkR ra (wz sp) gp tp t0 t1 t2 xs0 xs1 (wz D) (wz n) (wz c) a3 a4 a5 a6 a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xb1e80) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH D0 DLO D8 SLO DSH RN RC (G1 & G2 & G3 & G4) SHD X1 MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  pose proof (munch_refl [(sp - 48, sp); (D, D + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (SHZ : forall m', munch [(sp - 48, sp); (D, D + 1)] m m' -> wmono bsegs m m' -> shz m' D 24).
  { intros m' MU' _. change 24 with (8 * Z.of_nat 3). apply (shz_of_zero_run m' D 3); [exact D8| lia|].
    eapply bytes_at_agree; [exact SHD|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [repeat length] in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx SLO DSH LO D8. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  change (id (bytes_at bsegs m (D / 8 + 2147450880) [z8; z8; z8])) in SHD.
  zstep. carve_frame 48%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR. forget_junk FR.
  do 6 lstep.
  zstep. zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?Z.mod_small in K0 by lia; lia|].
  do 2 zstep.
  do 3 zstep.
  clear G1 G2 G3 G4.
  zstep.
  zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?Z.mod_small in K1 by lia; lia|].
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ D. zstep. shz_norm. zstep. if_false.
  zstep.    replace (Z.shiftl n 1) with (2 * n) by (rewrite Z.shiftl_mul_pow2; lia).
  ls.
  zstep.
  zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?Z.mod_small in K2 by lia; lia].
  do 4 zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
  split; [eassumption| eassumption].
Qed.

Lemma sn_walk2B : forall (sp D n c lo : Z) (ra gp tp t0 t1 t2 a1 a3 a5 a6 a7 xs0 xs1 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (b4 : list byte) F fc (m : mem),
  stk bsegs m lo (sp - 48) -> lo <= sp - 48 -> 0x6ce000 <= lo -> sp < 2^63 -> 0 < D -> D + 24 <= lo -> D mod 8 = 0 -> D / 8 + 2147450880 + 3 <= lo ->
  (D + 24 <= D / 8 + 2147450880 \/ D / 8 + 2147450880 + 3 <= D) ->
  1 <= n < 23 ->
  bytes_at bsegs m (D / 8 + 2147450880) [z8; z8; z8] ->
  rw_cells bsegs m (sp - 48) [C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 ra] ->
  rw_cells bsegs m (D + 1 + n) [CB 1 b4] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR ra (wz sp) gp tp t0 t1 t2 xs0 xs1 (wz (D + 1 + n)) (wz 0) (wz (-1)) a3 (wz 0) a5 a6 a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom bsegs)
      /\ munch [(D + 1 + n, D + 1 + n + 1)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo sp
      /\ rw_cells bsegs m1 (D + 1 + n) [C1 (Z_to_bv 8 0)])
    (MS (mkR ra (wz (sp - 48)) gp tp t0 t1 t2 (wz n) (wz c) (wz (D + 1)) a1 (wz (-1)) a3 (wz 0) a5 a6 a7
             (wz D) xs3 (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xb1fc4) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH D0 DLO D8 SLO DSH RN SHD FR X4 MI.
  pose proof (munch_refl [(D + 1 + n, D + 1 + n + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 (sp - 48)) = sp - 48) by (apply unsigned_lit; lia).
  assert (SHZ : forall m', munch [(D + 1 + n, D + 1 + n + 1)] m m' -> wmono bsegs m m' -> shz m' D 24).
  { intros m' MU' _. change 24 with (8 * Z.of_nat 3). apply (shz_of_zero_run m' D 3); [exact D8| lia|].
    eapply bytes_at_agree; [exact SHD|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [repeat length] in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx SLO DSH LO D8 RN. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  change (id (bytes_at bsegs m (D / 8 + 2147450880) [z8; z8; z8])) in SHD.
  zstep.
  zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite zb_lxor_ones in K0 by lia; lia|].
  clear K0.
  zstep.    replace (D + 1 + n) with (D + (1 + n)) in X4 |- * by lia.
  set (E1 := D + (1 + n)) in *.
  assert (EE : bv_unsigned (Z_to_bv 64 E1) = E1) by (apply unsigned_lit; lia).
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ E1. zstep. shz_norm. zstep. if_false.
  ls.
  replace (sp - 48) with (sp + -48) in * by lia.
  do 6 zstep. zstep.
  replace (sp + -48 + 48) with sp by lia.
  pose proof (stk_release bsegs _ _ _ _ ST FR ltac:(lia)) as ST1. cbn [cells_size csize Nat.add] in ST1. replace (sp + -48 + Z.of_nat 48) with sp in ST1 by lia.
  zstep.
  subst E1.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST1| eassumption].
Qed.

Lemma sn_loopZ : forall (p D cnt c : Z) (ra sp gp tp t0 t1 t2 s0 a0 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  1 <= cnt -> D + 1 <= p -> p + cnt <= D + 24 -> 0 < D -> D + 24 < 2^63 -> 0 <= c < 256 ->
  (forall m', munch [(p, p + cnt)] m m' -> wmono bsegs m m' -> shz m' D 24) ->
  wr_at bsegs m p cnt -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a5' : word) (m1 : mem),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (wz c) a0 (wz (p + cnt)) (wz (-1)) (wz (p + cnt)) (wz 0) a5' a6 a7
                   s2 s3 (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz 0xb1fc4) fc None m1 (seg_rom bsegs)
      /\ munch [(p, p + cnt)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ bytes_at bsegs m1 p (repeat (Z_to_bv 8 c) (Z.to_nat cnt)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (wz c) a0 (wz p) (wz (-1)) (wz p) (wz cnt) a5 a6 a7
             s2 s3 (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xb1f9c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros C1 LP HP D0 DH RC SHZ WR MI.
  set (k := Z.to_nat (cnt - 1)). assert (EK : cnt = Z.of_nat (S k)) by lia. clearbody k.
  replace (Z.to_nat cnt) with (S k) by lia. rewrite EK in SHZ, WR, HP |- *.
  eapply (sn_loopB k p D c); first [exact SHZ| exact WR| exact MI| lia].
Qed.

Lemma snB : forall (sp D n c lo : Z) (ra gp tp t0 t1 t2 a3 a4 a5 a6 a7 xs0 xs1 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (b1 b4 : list byte) F fc (m : mem),
  stk bsegs m lo sp -> lo <= sp - 48 -> 0x6ce000 <= lo -> sp < 2^63 -> 0 < D -> D + 24 <= lo -> D mod 8 = 0 -> D / 8 + 2147450880 + 3 <= lo ->
  (D + 24 <= D / 8 + 2147450880 \/ D / 8 + 2147450880 + 3 <= D) ->
  1 <= n < 23 -> 0 <= c < 256 ->
  client_consts m -> bytes_at bsegs m (D / 8 + 2147450880) [z8; z8; z8] ->
  rw_cells bsegs m D [CB 1 b1] -> wr_at bsegs m (D + 1) n -> rw_cells bsegs m (D + 1 + n) [CB 1 b4] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a5' : word) (m1 : mem),
      ms = MS (mkR ra (wz sp) gp tp t0 t1 t2 xs0 xs1 (wz (D + 1 + n)) (wz 0) (wz (-1)) (wz (D + 1 + n)) (wz 0) a5' a6 a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom bsegs)
      /\ munch [(sp - 48, sp); (D, D + 1 + n + 1)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo sp
      /\ rw_cells bsegs m1 D [C1 (Z_to_bv 8 (2 * n))] /\ bytes_at bsegs m1 (D + 1) (repeat (Z_to_bv 8 c) (Z.to_nat n))
      /\ rw_cells bsegs m1 (D + 1 + n) [C1 (Z_to_bv 8 0)])
    (MS (mkR ra (wz sp) gp tp t0 t1 t2 xs0 xs1 (wz D) (wz n) (wz c) a3 a4 a5 a6 a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xb1e80) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH D0 DLO D8 SLO DSH RN RC CC SHD X1 WR X4 MI.
  Local Ltac mv H m' MU := lazymatch type of H with
    | rw_cells _ _ ?a ?cs => let Hn := fresh "T" in assert (Hn : rw_cells bsegs m' a cs)
        by (eapply rw_cells_agree_nw; [exact H|]; apply (agree_of_munch _ _ _ _ MU); intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbn [outside]; lia); clear H; rename Hn into H
    | stk _ _ ?a ?b => let Hn := fresh "T" in assert (Hn : stk bsegs m' a b)
        by (eapply stk_agree_nw; [exact H|]; apply (agree_of_munch _ _ _ _ MU); intros x Hx; cbv beta in Hx; cbn [outside]; lia); clear H; rename Hn into H
    | bytes_at _ _ ?a ?bs => let Hn := fresh "T" in assert (Hn : bytes_at bsegs m' a bs)
        by (eapply bytes_at_agree; [exact H|]; apply (agree_of_munch _ _ _ _ MU); intros x Hx; rewrite ?repeat_length in Hx; cbn [repeat length] in Hx; cbn [outside]; unfold shad, SHB in *; lia); clear H; rename Hn into H
    end.
  eapply evt_cut; [eapply (sn_walk1B sp D n c lo); first [exact ST| exact CC| exact SHD| exact X1| exact MI| lia]|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & X0). clear X1 CC.
  pose proof (wr_at_transport bsegs m m1 (D + 1) n WR WM1) as WR1. clear WR.
  mv X4 m1 MU1. mv SHD m1 MU1.
  eapply evt_cut; [eapply (sn_loopZ (D + 1) D n c); first [exact WR1| exact MI1| lia| idtac]|].
  { intros m' MU' _. change 24 with (8 * Z.of_nat 3). apply (shz_of_zero_run m' D 3); [exact D8| lia|].
    eapply bytes_at_agree; [exact SHD|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [repeat length] in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx SLO DSH LO D8 RN. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  cbv beta. intros ms2 (a5' & m2 & -> & MU2 & WM2 & MI2 & BY2). clear WR1.
  mv ST1 m2 MU2. mv FR1 m2 MU2. mv X4 m2 MU2. mv SHD m2 MU2. mv X0 m2 MU2.
  eapply evt_cut; [eapply (sn_walk2B sp D n c lo); first [exact ST1| exact SHD| exact FR1| exact X4| exact MI2| lia]|].
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & ST3 & X43). clear X4.
  mv X0 m3 MU3. mv BY2 m3 MU3.
  apply evt_done. eexists _, _. split; [reflexivity|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; cbn [outside] in *; lia|].
           eapply munch_trans; [eapply munch_weaken; [| exact MU2]; intros x Hx; cbn [outside] in *; lia|].
           eapply munch_weaken; [| exact MU3]; intros x Hx; cbn [outside] in *; lia. }
  split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|].
  split; [exact MI3|]. split; [exact ST3|]. split; [exact X0|]. split; [exact BY2| exact X43].
Qed.

Lemma pad_ws : forall (S sp2 f OS FILL ns lo : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word) (ls4 : list (list byte)) (b1 b4 : list byte) F fc (m : mem),
  length ls4 = 4%nat ->
  stk bsegs m lo sp2 -> lo <= sp2 - 48 -> 0x6ce000 <= lo -> sp2 < 2^63 ->
  0 < f -> f + 128 <= lo -> f mod 8 = 0 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  1 <= ns < 23 -> 0 <= FILL < 256 ->
  client_consts m ->
  rw_cells bsegs m (f / 8 + 2147450880) (map C1 pad_sh12 ++ map (fun l => CB 1 l) ls4) ->
  rw_cells bsegs m (f + 32) [CB 1 b1] -> wr_at bsegs m (f + 33) ns -> rw_cells bsegs m (f + 33 + ns) [CB 1 b4] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a5' : word) (m1 : mem),
      ms = MS (mkR (wz 0xb1b8c) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz (f + 33 + ns)) (wz 0) (wz (-1)) (wz (f + 33 + ns)) (wz 0) a5' a6 a7
                   (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz 0) (wz f) (wz (f + 32)) (wz ns) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
              F (wz 0xb1b8c) fc None m1 (seg_rom bsegs)
      /\ munch [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 7); (sp2 - 48, sp2); (f + 32, f + 33 + ns + 1)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ stk bsegs m1 lo sp2
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 pad_sh12u ++ map (fun l => CB 1 l) ls4)
      /\ rw_cells bsegs m1 (f + 32) [C1 (Z_to_bv 8 (2 * ns))] /\ bytes_at bsegs m1 (f + 33) (repeat (Z_to_bv 8 FILL) (Z.to_nat ns))
      /\ rw_cells bsegs m1 (f + 33 + ns) [C1 (Z_to_bv 8 0)])
    (MS (mkR (wz 0xb1a28) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0 a1 a2 a3 a4 a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz 0) (wz f) s8 (wz ns) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
        F (wz 0xb1b68) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS4 ST LO GLO SPH F0 FLO F8 SLO SEP NS FIR CC FS X1 WR X4 MI.
  Local Ltac mv1 H m' MU := lazymatch type of H with
    | rw_cells _ _ ?a ?cs => let Hn := fresh "T" in assert (Hn : rw_cells bsegs m' a cs)
        by (eapply rw_cells_agree_nw; [exact H|]; apply (agree_of_munch _ _ _ _ MU); intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbn [outside]; lia); clear H; rename Hn into H
    | ro_cells _ _ ?a ?cs => let Hn := fresh "T" in assert (Hn : ro_cells bsegs m' a cs)
        by (eapply ro_cells_agree; [exact H|]; apply (agree_of_munch _ _ _ _ MU); intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbn [outside]; lia); clear H; rename Hn into H
    | stk _ _ ?a ?b => let Hn := fresh "T" in assert (Hn : stk bsegs m' a b)
        by (eapply stk_agree_nw; [exact H|]; apply (agree_of_munch _ _ _ _ MU); intros x Hx; cbv beta in Hx; cbn [outside]; lia); clear H; rename Hn into H
    | bytes_at _ _ ?a ?bs => let Hn := fresh "T" in assert (Hn : bytes_at bsegs m' a bs)
        by (eapply bytes_at_agree; [exact H|]; apply (agree_of_munch _ _ _ _ MU); intros x Hx; rewrite ?repeat_length in Hx; cbn [repeat length] in Hx; cbn [outside]; unfold shad, SHB in *; lia); clear H; rename Hn into H
    end.
  eapply evt_cut; [eapply (pad_w1 S sp2 f OS FILL ns lo); first [exact LS4| exact FS| exact MI| lia| apply Z.div_pos; lia]|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FS1).
  pose proof (wr_at_transport bsegs m m1 (f + 33) ns WR WM1) as WR1. clear WR.
  destruct CC as (G1 & G2 & G3 & G4). unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in G1, G2, G3, G4.
  mv1 ST m1 MU1. mv1 X1 m1 MU1. mv1 X4 m1 MU1. mv1 G1 m1 MU1. mv1 G2 m1 MU1. mv1 G3 m1 MU1. mv1 G4 m1 MU1.
  assert (SHD1 : bytes_at bsegs m1 ((f + 32) / 8 + 2147450880) [z8; z8; z8]).
  { replace ((f + 32) / 8 + 2147450880) with (f / 8 + 2147450880 + 4) by (clear - F8; Z.div_mod_to_equations; lia).
    pose proof FS1 as T. unfold pad_sh12u in T. cbn [map app repeat] in T. takeZ T 4%nat (f / 8 + 2147450880 + 4)%Z T0. clear T0.
    takeZ T 3%nat (f / 8 + 2147450880 + 7)%Z T1. clear T. exact (rw_cells_bytes_at _ _ _ _ T1). }
  replace (f + 33) with (f + 32 + 1) in WR1, X4 |- * by lia.
  eapply evt_cut; [eapply (snB sp2 (f + 32) ns FILL lo); first [exact ST| exact SHD1| exact X1| exact WR1| exact X4| exact MI1| split; [exact G1| split; [exact G2| split; [exact G3| exact G4]]]| lia
                   | clear - F8; Z.div_mod_to_equations; lia]|].
  cbv beta. intros ms2 (a5' & m2 & -> & MU2 & WM2 & MI2 & ST2 & X12 & BY2 & X42). clear X1 X4 WR1 SHD1 G1 G2 G3 G4.
  rewrite (ret_pc_even 0xb1b8c) by lia.
  lazymatch type of FS1 with rw_cells _ _ ?a ?cs =>
      assert (FS2 : rw_cells bsegs m2 a cs) by (eapply rw_cells_agree_nw; [exact FS1|]; apply (agree_of_munch _ _ _ _ MU2); intros x Hx;
        rewrite cells_size_app, cells_size_map_C1p, cells_size_map_CB1, LS4 in Hx; cbn [length pad_sh12u app repeat Nat.add] in Hx; cbn [outside]; lia) end.
  apply evt_done. eexists _, _. split; [reflexivity|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; cbn [outside] in *; lia|].
           eapply munch_weaken; [| exact MU2]; intros x Hx; cbn [outside] in *; lia. }
  split; [eapply wmono_trans; [exact WM1| exact WM2]|].
  split; [exact MI2|]. split; [exact ST2|]. split; [exact FS2|]. split; [exact X12|]. split; [exact BY2| exact X42].
Qed.

Lemma pad_w2 : forall (S sp2 f OS BUF N FILL ns : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j0 j1 j2 j8 j9 : list byte) F fc (m : mem),
  0 < f -> f + 128 < 2^63 -> 0 < OS -> OS + 288 < 2^63 -> OS mod 16 = 0 -> 0 <= sp2 -> sp2 + 88 < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 -> 1 <= ns < 23 ->
  shz m OS 288 -> shz m PJ_NULSB_VT_A 24 ->
  rw_cells bsegs m sp2 (padW_locals OS BUF N f j0 j1 j2 j8 j9) -> rw_cells bsegs m (f + 32) [C1 (Z_to_bv 8 (2 * ns))] ->
  rw_cells bsegs m OS [C8 (wz PJ_SB_VPTR_A)] ->
  ro_cells bsegs m PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)] ->
  mem_inv bsegs m ->
  evt bsegs (eq (MS (mkR (wz 0xb1be0) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz OS) (wz (f + 33)) (wz ns) (wz PJ_XSPUTN_A) a4 a5 a6 a7
                        (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz 0) (wz f) (wz (f + 32)) (wz ns) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
                   F (wz PJ_XSPUTN_A) fc None m (seg_rom bsegs)))
    (MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0 a1 a2 a3 a4 a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz 0) (wz f) (wz (f + 32)) (wz ns) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
        F (wz 0xb1b8c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FH O0 OH O16 S0 SP2R B0 N0 BNH NS SHZ0 SHV FRl STR SB VT MI.
  unfold PJ_NULSB_VT_A, PJ_XSPUTN_A, PJ_OVERFLOW_A, PJ_SB_VPTR_A, padW_locals in *.
  assert (ES : bv_unsigned (Z_to_bv 64 sp2) = sp2) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 OS) = OS) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  zstep. if_false.
  zstep.
  zstep.    rewrite (land1_double ns) by lia.
  zstep. if_false.
  zstep.    replace (f + 32 + 1) with (f + 33) by lia.
  zstep.
  zstep. zstep.
  shz_pose SHZ0 OS. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. zstep.
  pose proof (SHV 0x168e08 ltac:(lia)) as RD. change (0x168e08 / 8 + 2147450880) with 2147635649 in RD.
  zstep. shz_norm. zstep. if_false.
  zstep.
  do 3 zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pad_w3 : forall (S sp2 f OS BUF N FILL ns lo : Z) (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j0 j1 j2 j8 j9 : list byte) (ls4 : list (list byte)) F fc (m : mem),
  length ls4 = 4%nat -> 0 < f -> f + 128 <= lo -> 0 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> lo <= sp2 -> sp2 + 88 < 2^63 ->
  (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < BUF -> 0 <= N -> BUF + N < 2^63 -> 1 <= ns < 23 ->
  rw_cells bsegs m sp2 (padW_locals OS BUF N f j0 j1 j2 j8 j9) -> rw_cells bsegs m (f + 32) [C1 (Z_to_bv 8 (2 * ns))] ->
  rw_cells bsegs m (f / 8 + 2147450880) (map C1 pad_sh12u ++ map (fun l => CB 1 l) ls4) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz BUF) (wz (BUF + N)) a2 a3 a4 a5 a6 a7
                   (wz f) (wz OS) (wz 2147450880) (wz N) (wz 0) (wz f) (wz (f + 32)) (wz ns) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
              F (wz 0xb1c1c) fc None m1 (seg_rom bsegs)
      /\ munch [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 7)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 pad_sh12 ++ map (fun l => CB 1 l) ls4))
    (MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz ns) a1 a2 a3 a4 a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz 0) (wz f) (wz (f + 32)) (wz ns) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
        F (wz 0xb1be0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS4 F0 FLO FD SLO LSP SPH SEP B0 N0 BNH NS FRl STR FS MI.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  unfold pad_sh12u, padW_locals in *. cbn [map app repeat] in FS.
  pose proof (munch_refl [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 7)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp2) = sp2) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep.
  zstep.    rewrite (land1_double ns) by lia.
  zstep. if_false.
  zstep. if_true.
  zstep. do 3 ls.
  zstep. zstep.
  zstep.    replace (BUF + N - BUF) with N by lia.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  unfold pad_sh12. cbn [map app repeat]. eassumption.
Qed.

Lemma pad_segBW : forall (S sp2 f OS BUF N : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word) (j0 j1 j2 j8 j9 : list byte) F fc (m : mem),
  0 < f -> f + 128 < 2^63 -> 0 < OS -> OS + 288 < 2^63 -> OS mod 16 = 0 -> 0 <= sp2 -> S - 208 <= sp2 <= S - 192 -> S < 2^63 -> 0 < BUF -> BUF + N < 2^63 -> 0 < N < 2^63 ->
  shz m OS 288 -> shz m PJ_NULSB_VT_A 24 ->
  rw_cells bsegs m sp2 (padW_locals OS BUF N f j0 j1 j2 j8 j9) ->
  rw_cells bsegs m OS [C8 (wz PJ_SB_VPTR_A)] ->
  ro_cells bsegs m PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)] ->
  mem_inv bsegs m ->
  evt bsegs (eq (MS (mkR (wz 0xb1c60) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz OS) (wz BUF) (wz N) (wz PJ_XSPUTN_A) a4 a5 a6 a7
                        (wz f) (wz OS) (wz 2147450880) (wz N) (wz 0) (wz f) s8 s9 (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
                   F (wz PJ_XSPUTN_A) fc None m (seg_rom bsegs)))
    (MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0 a1 a2 a3 a4 a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) (wz N) (wz 0) (wz f) s8 s9 (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
        F (wz 0xb1c1c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FH O0 OH O16 S0 SP2R SPH B0 BNH NR SHZ0 SHV FRl SB VT MI. unfold padW_locals in FRl.
  unfold PJ_NULSB_VT_A, PJ_XSPUTN_A, PJ_OVERFLOW_A, PJ_SB_VPTR_A in *.
  assert (ES : bv_unsigned (Z_to_bv 64 sp2) = sp2) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 OS) = OS) by (apply unsigned_lit; lia).
  zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
  zstep. if_false.
  zstep. zstep.
  shz_pose SHZ0 OS. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. zstep.
  pose proof (SHV 0x168e08 ltac:(lia)) as RD. change (0x168e08 / 8 + 2147450880) with 2147635649 in RD.
  zstep. shz_norm.
  zstep.
  zstep. if_false.
  zstep.
  do 3 zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pad_exit1W : forall (S sp2 f lo OS N W : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 h0 : word) (sh : list byte) (ls4 : list (list byte)) F fc (m : mem),
  length sh = 12%nat -> length ls4 = 4%nat ->
  0 < f -> f + 128 <= lo -> 0 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 <= OS -> OS + 288 <= lo -> (OS + 288 <= f \/ f + 128 <= OS) -> (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= OS) ->
  lo <= sp2 -> sp2 + 40 < 2^63 -> 0 <= N < 2^64 -> 0 <= W < 2^64 ->
  shz m OS 288 ->
  rw_cells bsegs m (sp2 + 24) [C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz (OS + 160))] -> rw_cells bsegs m (OS + 160) [C8 (wz W)] ->
  rw_cells bsegs m f [C8 h0] -> rw_cells bsegs m (f / 8 + 2147450880) (map C1 sh ++ map (fun l => CB 1 l) ls4) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz (-11)) a1 a2 a3 a4 a5 a6 a7
                   (wz f) (wz OS) (wz 2147450880) (wz N) (wz 0) (wz f) s8 s9 (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
              F (wz 0xb1d00) fc None m1 (seg_rom bsegs)
      /\ munch [(OS + 160, OS + 168); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (OS + 160) [C8 (wz 0)] /\ rw_cells bsegs m1 f [C8 (wz 0x45e0360e)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 f5x16))
    (MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0 a1 a2 a3 a4 a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) (wz N) (wz 0) (wz f) s8 s9 (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
        F (wz 0xb1c64) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS LS4 F0 FLO FD SLO SEP O0 OLO OF OSH LSP SPH NR WR SHZ0 L0 WID FH FS MI.
  do 12 (destruct sh as [|? sh]; [discriminate LS|]). destruct sh; [| discriminate LS]. clear LS.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  cbn [map app repeat] in FS.
  pose proof (munch_refl [(OS + 160, OS + 168); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp2) = sp2) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (OS + 160)) = OS + 160) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (ES24 : bv_unsigned (Z_to_bv 64 (sp2 + 24)) = sp2 + 24) by (apply unsigned_lit; lia).
  zstep.
  shz_pose SHZ0 (OS + 160). zstep. shz_norm. zstep. if_false.
  zstep.
  lstep.
  zstep.
  zstep. zstep. lstep.
  zstep. if_cases K'; zify_cond K'; [exfalso; lia|].
  zstep.
  do 16 ls.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. unfold f5x16. cbn [map app repeat]. eassumption.
Qed.
