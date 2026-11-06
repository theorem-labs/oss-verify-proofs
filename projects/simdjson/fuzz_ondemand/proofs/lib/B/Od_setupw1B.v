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
  Sj_num_amem Atp_h_defsA Atp_h_findA Od_proB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition oa_shadow0 (ls : list (list byte)) (t : list byte) : list cell := map (fun l => CB 1 l) ls ++ [CB 28 t].

Definition oa_shadow1 (t : list byte) : list cell :=
  map C1 (repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 (-8)) 3 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 (-8)) 7
          ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 (-8)) 8 ++ repeat (Z_to_bv 8 (-13)) 4)
  ++ [CB 28 t].

Definition oa_locals1 (F : Z) (j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j408 j416 j425 j432 : list byte) : list cell :=
  [CB 8 j0; CB 8 j8; CB 8 j16; CB 96 j24; CB 8 j120; C8 (Z_to_bv 64 F); CB 32 j136; CB 8 j168; CB 72 j176; C8 (Z_to_bv 64 (F / 8 + 2147450880));
   CB 8 j256; CB 16 j264; CB 8 j280; CB 40 j288; CB 8 j328; CB 32 j336; CB 8 j368; CB 24 j376; C8 (Z_to_bv 64 F); CB 8 j408; CB 8 j416;
   C1 (Z_to_bv 8 0); CB 7 j425; CB 8 j432].

Definition oa_W1h (S1 F : Z) : list ivl := [(S1, S1 + 440); (F, F + 24); (F / 8 + 2147450880, F / 8 + 2147450880 + 36)].

Definition oa_st1 (pc : Z) (usp S1 F : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state :=
  MS (mkR (Z_to_bv 64 0x969b4) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1)
          a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 F)
          s2 s3 s4 s5 s6 (Z_to_bv 64 2147450880) s8 s9 s10 s11 t3 t4 t5 t6)
     FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma od_walk1h : forall (usp S1 F lo d n : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (j0 j8 j16 j24 j120 j128 j136 j168 j176 j248 j256 j264 j280 j288 j328 j336 j368 j376 j400 j408 j416 j424 j425 j432 h0 h1 h2 h3 t : list byte)
    (ls : list (list byte)) FR fc (m : mem),
  length ls = 36%nat ->
  0 < F -> F + 512 <= lo -> F / 8 + 2147450880 + 64 <= lo -> 0 <= F / 8 ->
  (F + 512 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 64 <= F) ->
  0x679000 <= lo -> lo <= S1 -> S1 + 440 <= usp - 104 -> usp < 2^63 -> 0 <= d < 2^64 -> 0 <= n < 2^64 ->
  rw_cells bsegs m S1 (od_locals0 j0 j8 j16 j24 j120 j128 j136 j168 j176 j248 j256 j264 j280 j288 j328 j336 j368 j376 j400 j408 j416 j424 j425 j432) ->
  rw_cells bsegs m F [CB 8 h0; CB 8 h1; CB 8 h2; CB 8 h3] ->
  rw_cells bsegs m (F / 8 + 2147450880) (oa_shadow0 ls t) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a1' a2' a3' a4' a5' a6' : word),
      ms = oa_st1 0x96abc usp S1 F gp tp t0 t1 t2 (Z_to_bv 64 F) a1' a2' a3' a4' a5' a6' (Z_to_bv 64 n) (Z_to_bv 64 d) s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m1
      /\ munch (oa_W1h S1 F) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 S1 (oa_locals1 F j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j408 j416 j425 j432)
      /\ rw_cells bsegs m1 F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1ce89); C8 (Z_to_bv 64 0x96940); CB 8 h3]
      /\ rw_cells bsegs m1 (F / 8 + 2147450880) (oa_shadow1 t))
    (MS (mkR (Z_to_bv 64 0x969b4) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 n) (Z_to_bv 64 d) s4 s5 s6 (Z_to_bv 64 2147450880) s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x969b4) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS F0 FLO SLO FD SEP GLO LSP LUSP SPH DR NR FRl FH FS MI.
  do 36 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold oa_W1h, od_locals0, oa_locals1, oa_shadow0, oa_shadow1, oa_st1 in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(S1, S1 + 440); (F, F + 24); (F / 8 + 2147450880, F / 8 + 2147450880 + 36)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 F) = F) by (apply unsigned_lit; lia).

  zstep. zstep. zstep.
  if_cases K; zify_cond K; [| exfalso; lia].

  ls. zstep. zstep. zstep. zstep. rewrite shr3_div. zstep. zstep. zstep. zstep. zstep.

  ls. ls. ls. zstep. zstep.

  ls. ls. ls. ls. zstep.
  do 31 ls.
  ls. ls. ls. ls.
  apply evt_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition oa_locals2 (F D : Z) (j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j416 j425 j432 : list byte) : list cell :=
  [CB 8 j0; CB 8 j8; CB 8 j16; CB 96 j24; CB 8 j120; C8 (Z_to_bv 64 F); CB 32 j136; CB 8 j168; CB 72 j176; C8 (Z_to_bv 64 (F / 8 + 2147450880));
   CB 8 j256; CB 16 j264; CB 8 j280; CB 40 j288; CB 8 j328; CB 32 j336; CB 8 j368; CB 24 j376; C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 D); CB 8 j416;
   C1 (Z_to_bv 8 0); CB 7 j425; CB 8 j432].

Lemma od_walk1e : forall (usp S1 F d : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j408 j416 j425 j432 : list byte) FR fc (m : mem),
  0x679000 <= S1 -> S1 + 440 <= usp - 104 -> usp < 2^63 ->
  rw_cells bsegs m S1 (oa_locals1 F j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j408 j416 j425 j432) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = oa_st1 0x96b14 usp S1 F gp tp t0 t1 t2 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 0) (Z_to_bv 64 d) s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m1
      /\ munch [(S1, S1 + 440)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 S1 (oa_locals2 F 0 j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j416 j425 j432))
    (oa_st1 0x96abc usp S1 F gp tp t0 t1 t2 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 0) (Z_to_bv 64 d) s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros GLO LUSP SPH FRl MI.
  unfold oa_locals1, oa_locals2, oa_st1 in *.
  pose proof (munch_refl [(S1, S1 + 440)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

  zstep. if_true. zstep. ls.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma oa_action_arith : forall b, 0 <= b < 256 ->
  Z.land (Z.land (bv_swrap 32 (b - Z.land ((b * 79) ≫ 10 * 13) 18446744073709551615)) 18446744073709551615) 255 = b mod 13.
Proof.
  intros b Hb.
  assert (H : forallb (fun n => Z.land (Z.land (bv_swrap 32 (Z.of_nat n - Z.land ((Z.of_nat n * 79) ≫ 10 * 13) 18446744073709551615)) 18446744073709551615) 255 =? Z.of_nat n mod 13) (seq 0 256) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat b)). rewrite Z2Nat.id in H by lia.
  apply Z.eqb_eq. apply H. apply in_seq. lia.
Qed.

Lemma od_walk1b : forall (usp S1 F d n : Z) (b0 b : byte) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j408 j416 j425 j432 : list byte) FR fc (m : mem),
  0x679000 <= S1 -> S1 + 440 <= usp - 104 -> usp < 2^63 -> 0 < d -> d + n <= S1 -> 1 <= n < 2^26 -> 0 <= d / 8 -> d / 8 + 2147450880 + 1 <= S1 ->
  rw_cells bsegs m S1 (oa_locals1 F j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j408 j416 j425 j432) ->
  bytes_at bsegs m d [b0] -> bytes_at bsegs m (d / 8 + 2147450880) [b] -> sh_ok b d ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a1' a2' : word),
      ms = oa_st1 0x96b14 usp S1 F gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned b0 mod 13)) a1' a2' a3 a4 a5 a6 (Z_to_bv 64 (n - 1)) (Z_to_bv 64 (d + 1))
                  s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m1
      /\ munch [(S1, S1 + 440)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 S1 (oa_locals2 F (d + 1) j0 j8 j16 j24 j120 j136 j168 j176 j256 j264 j280 j288 j328 j336 j368 j376 j416 j425 j432))
    (oa_st1 0x96abc usp S1 F gp tp t0 t1 t2 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 n) (Z_to_bv 64 d) s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros GLO LUSP SPH D0 DN NR SD0 SDS FRl BY SHB0 SOK MI.
  unfold oa_locals1, oa_locals2, oa_st1 in *.
  pose proof (munch_refl [(S1, S1 + 440)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bv_unsigned_in_range 8 b0) as B0R. unfold bv_modulus in B0R. change (2 ^ Z.of_N 8) with 256 in B0R.

  zstep. if_cases K; zify_cond K; [exfalso; lia| clear K].
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  pose proof (bytes_at_read bsegs m _ _ 0 1 SHB0 ltac:(lia) ltac:(cbn; lia)) as RDS.
  pose proof (bytes_at_read bsegs m _ _ 0 1 BY ltac:(lia) ltac:(cbn; lia)) as RDB.
  rewrite Z.add_0_r in RDS, RDB. cbn [firstn skipn Z.to_nat] in RDS, RDB.
  lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mx _) =>
    assert (REST : forall xa1 xa2 : word,
      evt bsegs QQ (MS (mkR (Z_to_bv 64 0x969b4) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) (Z_to_bv 64 F) xa1 xa2 a3 a4 a5 a6 (Z_to_bv 64 F)
             (Z_to_bv 64 n) (Z_to_bv 64 d) s4 s5 s6 (Z_to_bv 64 2147450880) s8 s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 0x96adc) fc None mx (seg_rom bsegs))) end.
  2:{ destruct (f_sh_ok_cases b d SOK) as [-> | (k & -> & K17 & KM)].
      -
        zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_true. apply REST.
      - zstep. rewrite shr3_div. zstep. zstep. rewrite (f_sxb_small7 k) by lia. zstep.
        if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|].

        zstep. zstep. rewrite Sj_num_amem.land7_mod8. zstep.
        pose proof (Z.mod_pos_bound d 8 ltac:(lia)) as DM.
        if_cases K3; zify_cond K3; [exfalso; rewrite !a_signed_small in K3 by lia; lia|].
        zstep. apply REST. }
  intros xa1 xa2.

  zstep. zstep. zstep. zstep. ls. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite (oa_action_arith (bv_unsigned b0) B0R) in *.
  apply evt_done. do 3 eexists. split; [cbv delta [mkR]; first [reflexivity | repeat f_equal; lia]|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.
