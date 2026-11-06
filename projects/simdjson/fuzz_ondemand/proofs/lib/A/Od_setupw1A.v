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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Od_hbaseA
  Sj_num_amem Atp_h_defsA Atp_h_findA Od_proA.
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

Definition oa_locals1 (F : Z) (j0 j8 j16 j24 j32 j104 j128 j176 j184 j192 j200 j208 j216 j224 j240 j248 j352 j376 j384 j392 j393 j400 : list byte) : list cell :=
  [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 72 j32; CB 24 j104; CB 48 j128; CB 8 j176; CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j208; CB 8 j216;
   CB 16 j224; CB 8 j240; CB 104 j248; CB 16 j352; C8 (Z_to_bv 64 F); CB 8 j376; CB 8 j384; CB 1 j392; CB 7 j393; CB 8 j400].

Definition oa_W1h (S1 F : Z) : list ivl := [(S1, S1 + 408); (F, F + 24); (F / 8 + 2147450880, F / 8 + 2147450880 + 36)].

Lemma od_walk1h : forall (usp S1 F lo d n : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (j0 j8 j16 j24 j32 j104 j128 j176 j184 j192 j200 j208 j216 j224 j240 j248 j352 j368 j376 j384 j392 j393 j400 h0 h1 h2 h3 t : list byte)
    (ls : list (list byte)) FR fc (m : mem),
  length ls = 36%nat ->
  0 < F -> F + 512 <= lo -> F / 8 + 2147450880 + 64 <= lo -> 0 <= F / 8 ->
  (F + 512 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 64 <= F) ->
  0x66b000 <= lo -> lo <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 -> 0 <= d < 2^64 -> 0 <= n < 2^64 ->
  rw_cells asegs m S1 (od_locals0 j0 j8 j16 j24 j32 j104 j128 j176 j184 j192 j200 j208 j216 j224 j240 j248 j352 j368 j376 j384 j392 j393 j400) ->
  rw_cells asegs m F [CB 8 h0; CB 8 h1; CB 8 h2; CB 8 h3] ->
  rw_cells asegs m (F / 8 + 2147450880) (oa_shadow0 ls t) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (Z_to_bv 64 0x96a18) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1)
                   (Z_to_bv 64 (-8)) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-13)) (Z_to_bv 64 0x1cf0b) (Z_to_bv 64 0x969a4) (Z_to_bv 64 F) a6 a7
                   (Z_to_bv 64 F) (Z_to_bv 64 2147450880) (Z_to_bv 64 n) (Z_to_bv 64 d) s6 s7 s8 s9 s10 (Z_to_bv 64 (F / 8 + 2147450880)) t3 t4 t5 t6)
              FR (Z_to_bv 64 0x96b18) fc None m1 (seg_rom asegs)
      /\ munch (oa_W1h S1 F) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 S1 (oa_locals1 F j0 j8 j16 j24 j32 j104 j128 j176 j184 j192 j200 j208 j216 j224 j240 j248 j352 j376 j384 j392 j393 j400)
      /\ rw_cells asegs m1 F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1cf0b); C8 (Z_to_bv 64 0x969a4); CB 8 h3]
      /\ rw_cells asegs m1 (F / 8 + 2147450880) (oa_shadow1 t))
    (MS (mkR (Z_to_bv 64 0x96a18) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 2147450880) (Z_to_bv 64 n) (Z_to_bv 64 d) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x96a18) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS F0 FLO SLO FD SEP GLO LSP LUSP SPH DR NR FRl FH FS MI.
  do 36 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold oa_W1h, od_locals0, oa_locals1, oa_shadow0, oa_shadow1 in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(S1, S1 + 408); (F, F + 24); (F / 8 + 2147450880, F / 8 + 2147450880 + 36)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 F) = F) by (apply unsigned_lit; lia).

  zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; [| exfalso; lia].

  ls. zstep. zstep. zstep. zstep. rewrite shr3_div. zstep. zstep. zstep. zstep. zstep.

  ls. ls. ls. zstep. zstep.

  ls. ls. ls. ls. zstep.
  do 32 ls.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition oa_locals2 (F act : Z) (j0 j8 j16 j24 j32 j104 j128 j176 j192 j200 j208 j216 j224 j240 j248 j352 j376 j384 j393 j400 : list byte) : list cell :=
  [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 72 j32; CB 24 j104; CB 48 j128; CB 8 j176; C8 (Z_to_bv 64 act); CB 8 j192; CB 8 j200; CB 8 j208; CB 8 j216;
   CB 16 j224; CB 8 j240; CB 104 j248; CB 16 j352; C8 (Z_to_bv 64 F); CB 8 j376; CB 8 j384; C1 (Z_to_bv 8 0); CB 7 j393; CB 8 j400].

Definition oa_st2 (usp S1 F D n : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 0x96a18) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1)
          (Z_to_bv 64 n) a1 a2 a3 a4 (Z_to_bv 64 F) a6 a7
          (Z_to_bv 64 F) (Z_to_bv 64 2147450880) s4 (Z_to_bv 64 D) s6 s7 s8 s9 s10 (Z_to_bv 64 (F / 8 + 2147450880)) t3 t4 t5 t6)
     FR (Z_to_bv 64 0x96b70) fc None m (seg_rom asegs).

Lemma od_walk1e : forall (usp S1 F d : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a6 a7 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
    (j0 j8 j16 j24 j32 j104 j128 j176 j184 j192 j200 j208 j216 j224 j240 j248 j352 j376 j384 j392 j393 j400 : list byte) FR fc (m : mem),
  0x66b000 <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 ->
  rw_cells asegs m S1 (oa_locals1 F j0 j8 j16 j24 j32 j104 j128 j176 j184 j192 j200 j208 j216 j224 j240 j248 j352 j376 j384 j392 j393 j400) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = oa_st2 usp S1 F 0 0 gp tp t0 t1 t2 a1 a2 a3 a4 a6 a7 (Z_to_bv 64 0) s6 s7 s8 s9 s10 t3 t4 t5 t6 FR fc m1
      /\ munch [(S1, S1 + 408)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 S1 (oa_locals2 F 0 j0 j8 j16 j24 j32 j104 j128 j176 j192 j200 j208 j216 j224 j240 j248 j352 j376 j384 j393 j400))
    (MS (mkR (Z_to_bv 64 0x96a18) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 (Z_to_bv 64 F) a6 a7
             (Z_to_bv 64 F) (Z_to_bv 64 2147450880) (Z_to_bv 64 0) (Z_to_bv 64 d) s6 s7 s8 s9 s10 (Z_to_bv 64 (F / 8 + 2147450880)) t3 t4 t5 t6)
        FR (Z_to_bv 64 0x96b18) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros GLO LUSP SPH FRl MI.
  unfold oa_locals1, oa_locals2, oa_st2 in *.
  pose proof (munch_refl [(S1, S1 + 408)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  ls. zstep. if_true.
  zstep. zstep. ls.
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

Lemma od_walk1b : forall (usp S1 F d n : Z) (b0 b : byte) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a6 a7 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
    (j0 j8 j16 j24 j32 j104 j128 j176 j184 j192 j200 j208 j216 j224 j240 j248 j352 j376 j384 j392 j393 j400 : list byte) FR fc (m : mem),
  0x66b000 <= S1 -> S1 + 408 <= usp - 104 -> usp < 2^63 -> 0 < d -> d + n <= S1 -> 1 <= n < 2^26 -> 0 <= d / 8 -> d / 8 + 2147450880 + 1 <= S1 ->
  rw_cells asegs m S1 (oa_locals1 F j0 j8 j16 j24 j32 j104 j128 j176 j184 j192 j200 j208 j216 j224 j240 j248 j352 j376 j384 j392 j393 j400) ->
  bytes_at asegs m d [b0] -> bytes_at asegs m (d / 8 + 2147450880) [b] -> sh_ok b d ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a1' a2' a3' : word),
      ms = oa_st2 usp S1 F (d + 1) (n - 1) gp tp t0 t1 t2 a1' a2' a3' a4 a6 a7 (Z_to_bv 64 n) s6 s7 s8 s9 s10 t3 t4 t5 t6 FR fc m1
      /\ munch [(S1, S1 + 408)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 S1 (oa_locals2 F (bv_unsigned b0 mod 13) j0 j8 j16 j24 j32 j104 j128 j176 j192 j200 j208 j216 j224 j240 j248 j352 j376 j384 j393 j400))
    (MS (mkR (Z_to_bv 64 0x96a18) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 (Z_to_bv 64 F) a6 a7
             (Z_to_bv 64 F) (Z_to_bv 64 2147450880) (Z_to_bv 64 n) (Z_to_bv 64 d) s6 s7 s8 s9 s10 (Z_to_bv 64 (F / 8 + 2147450880)) t3 t4 t5 t6)
        FR (Z_to_bv 64 0x96b18) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros GLO LUSP SPH D0 DN NR SD0 SDS FRl BY SHB0 SOK MI.
  unfold oa_locals1, oa_locals2, oa_st2 in *.
  pose proof (munch_refl [(S1, S1 + 408)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 8 b0) as B0R. unfold bv_modulus in B0R. change (2 ^ Z.of_N 8) with 256 in B0R.
  ls. zstep. if_cases K; zify_cond K; [exfalso; lia| clear K].
  lazymatch goal with H : bytes_at asegs ?mm (d / 8 + 2147450880) [b] |- _ =>
    pose proof (bytes_at_read asegs mm _ _ 0 1 H ltac:(lia) ltac:(cbn; lia)) as RDS end.
  lazymatch goal with H : bytes_at asegs ?mm d [b0] |- _ =>
    pose proof (bytes_at_read asegs mm _ _ 0 1 H ltac:(lia) ltac:(cbn; lia)) as RDB end.
  rewrite Z.add_0_r in RDS, RDB. cbn [firstn skipn Z.to_nat] in RDS, RDB.
  lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mx _) =>
    assert (REST : forall xa0 xa1 : word,
      evt asegs QQ (MS (mkR (Z_to_bv 64 0x96a18) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) xa0 xa1 a2 a3 a4 (Z_to_bv 64 F) a6 a7
             (Z_to_bv 64 F) (Z_to_bv 64 2147450880) (Z_to_bv 64 n) (Z_to_bv 64 d) s6 s7 s8 s9 s10 (Z_to_bv 64 (F / 8 + 2147450880)) t3 t4 t5 t6)
                 FR (Z_to_bv 64 0x96b34) fc None mx (seg_rom asegs))) end.
  2:{ destruct (f_sh_ok_cases b d SOK) as [-> | (k & -> & K17 & KM)].
      - zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_true. apply REST.
      - zstep. rewrite shr3_div. zstep. zstep. rewrite (f_sxb_small7 k) by lia. zstep.
        if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|].
        zstep. zstep. rewrite land7_mod8. zstep.
        pose proof (Z.mod_pos_bound d 8 ltac:(lia)) as DM.
        if_cases K3; zify_cond K3; [exfalso; rewrite !a_signed_small in K3 by lia; lia|].
        zstep. apply REST. }
  intros xa0 xa1.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. ls. zstep.
  rewrite (oa_action_arith (bv_unsigned b0) B0R) in *.
  apply evt_done. do 4 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.
