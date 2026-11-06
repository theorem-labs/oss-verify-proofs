(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


Notation BD_W datad n := [(datad, datad + n)]%Z (only parsing).

(* [comment removed for export] *)
Definition band_geom (sa fr datas datad wpls wpld w h d : Z) : Prop :=
  0 < w <= 20000 /\ w * d <= 32 * wpls /\ w <= 32 * wpld /\ 0 < wpls <= 2^20 /\ 0 < wpld <= 2^20 /\ 0 < h <= 2^20
  /\ wpls * h <= 2^24 /\ wpld * h <= 2^24
  /\ 0 < datas /\ datas mod 8 = 0 /\ datas + 4 * (wpls * h) <= 2^47 /\ (datas + 4 * (wpls * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datas)
  /\ (datas + 4 * (wpls * h) <= 0x10000 \/ SEGTOP_A <= datas)
  /\ 0 < datad /\ datad mod 8 = 0 /\ datad + 4 * (wpld * h) <= 2^47 /\ (datad + 4 * (wpld * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datad)
  /\ (datad + 4 * (wpld * h) <= 0x10000 \/ SEGTOP_A <= datad)
  /\ (datas + 4 * (wpls * h) <= datad \/ datad + 4 * (wpld * h) <= datas)
  /\ 0 < fr /\ fr + 128 <= 2^47 /\ (fr + 128 <= datad \/ datad + 4 * (wpld * h) <= fr)
  /\ 0 < sa /\ sa + 64 <= 2^47 /\ (sa + 64 <= datad \/ datad + 4 * (wpld * h) <= sa).

(* [comment removed for export] *)
Definition band_inv (m : mem) (sa fr datas datad wpls wpld w h d : Z) (bs : list byte) (wd : list word) (c48 : word) (p0 p1 : list byte) : Prop :=
  mem_inv asegs m
  /\ bytes_at asegs m datas bs /\ Z.of_nat (length bs) = 4 * (wpls * h) /\ acc asegs m datas (4 * (wpls * h))
  /\ u32arr asegs m datad wd /\ Z.of_nat (length wd) = wpld * h /\ acc asegs m datad (4 * (wpld * h))
  /\ rw_cells asegs m (fr + 32) [C4 (Z_to_bv 64 w); CB 12 p0; C4 (Z_to_bv 64 h); CB 12 p1; C4 (Z_to_bv 64 d)]
  /\ rw_cells asegs m (sa + 32) [C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 datas); C8 c48; C8 (Z_to_bv 64 (fr + 48))].

(* [comment removed for export] *)
Definition band_row_exit (sp gp tp t0 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (sa fr datas datad wpls wpld w h d : Z) (bs : list byte) (c48 : word) (p0 p1 : list byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t1' t2' a1' s11' t3' t4' t5' t6' : word) (m' : mem) (wd' : list word),
    ms' = MS (mkR ra' sp gp tp t0 t1' t2' s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 SHB) s9 s10 s11' t3' t4' t5' t6')
             F (Z_to_bv 64 0x9da6c) fc None m' (seg_rom asegs)
    /\ munch (BD_W datad (4 * (wpld * h))) m m' /\ wmono asegs m m'
    /\ band_inv m' sa fr datas datad wpls wpld w h d bs wd' c48 p0 p1.

(* [comment removed for export] *)
Definition band_px_stmt (d : Z) : Prop := forall (k : nat) (j : Z)
    (ra sp gp tp s0 a1 a5 s2 s3 s4 s6 s9 s11 : word) F fc (m : mem)
    (sa fr datas datad wpls wpld w h i : Z) (bs : list byte) (wd : list word) (c48 : word) (p0 p1 : list byte),
  Z.of_nat k = w - j -> 0 <= j -> (1 <= k)%nat -> 0 <= i < h -> band_geom sa fr datas datad wpls wpld w h d ->
  band_inv m sa fr datas datad wpls wpld w h d bs wd c48 p0 p1 ->
  evt asegs (band_row_exit sp gp tp (Z_to_bv 64 (datas + 4 * (i * wpls))) s0 (Z_to_bv 64 sa) (Z_to_bv 64 wpld) (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpls))
               (Z_to_bv 64 4) a5 (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 8) s2 s3 s4 (Z_to_bv 64 (fr + 64)) s6 (Z_to_bv 64 (fr + 32)) s9 (Z_to_bv 64 wpls)
               F fc m sa fr datas datad wpls wpld w h d bs c48 p0 p1)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (datas + 4 * (i * wpls))) (Z_to_bv 64 (4 * j)) (Z_to_bv 64 (2 * j)) s0 (Z_to_bv 64 sa)
             (Z_to_bv 64 wpld) a1 (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpls)) (Z_to_bv 64 4) a5 (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 8)
             s2 s3 s4 (Z_to_bv 64 (fr + 64)) s6 (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 SHB) s9 (Z_to_bv 64 wpls) s11
             (Z_to_bv 64 j) (Z_to_bv 64 j) (Z_to_bv 64 (datas + 4 * (i * wpls))) (Z_to_bv 64 (datad + 4 * (i * wpld))))
        F (Z_to_bv 64 0x9dae4) fc None m (seg_rom asegs)).

Lemma band_px8 : band_px_stmt 8.
Proof.
  unfold band_px_stmt.
  induction k as [|k IH]; intros j ra sp gp tp s0 a1 a5 s2 s3 s4 s6 s9 s11 F fc m sa fr datas datad wpls wpld w h i bs wd c48 p0 p1
    HK HJ HK1 HI GEO INV.
  { lia. }
  pose proof GEO as (HW & WS & WD & WPLS & WPLD & HH & SH & DH & S0 & S8 & SHI & SSH & SSEG & D0 & D8 & DHI & DSH & DSEG & SEP
                     & FR0 & FRHI & FRD & SA0 & SAHI & SAD).
  destruct INV as (MI & HB & HBL & ACCS & UA & UAL & ACCD & FC & SL).
  assert (NS : i * wpls + wpls <= wpls * h) by (clear - HI WPLS; nia).
  assert (NS0 : 0 <= i * wpls) by (clear - HI WPLS; nia).
  assert (ND : i * wpld + wpld <= wpld * h) by (clear - HI WPLD; nia).
  assert (ND0 : 0 <= i * wpld) by (clear - HI WPLD; nia).
  assert (JD : 0 <= j / 32 < wpld) by (clear - HJ HK WD HW; Z.div_mod_to_equations; lia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (BD_W datad (4 * (wpld * h))) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (CONT : forall (ra' a1' s11' : word) (mm : mem) (wd' : list word),
    munch (BD_W datad (4 * (wpld * h))) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    bytes_at asegs mm datas bs -> acc asegs mm datas (4 * (wpls * h)) ->
    u32arr asegs mm datad wd' -> Z.of_nat (length wd') = wpld * h -> acc asegs mm datad (4 * (wpld * h)) ->
    rw_cells asegs mm (fr + 32) [C4 (Z_to_bv 64 w); CB 12 p0; C4 (Z_to_bv 64 h); CB 12 p1; C4 (Z_to_bv 64 8)] ->
    rw_cells asegs mm (sa + 32) [C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 datas); C8 c48; C8 (Z_to_bv 64 (fr + 48))] ->
    evt asegs (band_row_exit sp gp tp (Z_to_bv 64 (datas + 4 * (i * wpls))) s0 (Z_to_bv 64 sa) (Z_to_bv 64 wpld) (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpls))
               (Z_to_bv 64 4) a5 (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 8) s2 s3 s4 (Z_to_bv 64 (fr + 64)) s6 (Z_to_bv 64 (fr + 32)) s9 (Z_to_bv 64 wpls)
               F fc m sa fr datas datad wpls wpld w h 8 bs c48 p0 p1)
      (MS (mkR ra' sp gp tp (Z_to_bv 64 (datas + 4 * (i * wpls))) (Z_to_bv 64 (4 * j)) (Z_to_bv 64 (2 * j)) s0 (Z_to_bv 64 sa)
             (Z_to_bv 64 wpld) a1' (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpls)) (Z_to_bv 64 4) a5 (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 8)
             s2 s3 s4 (Z_to_bv 64 (fr + 64)) s6 (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 2147450880) s9 (Z_to_bv 64 wpls) s11'
             (Z_to_bv 64 j) (Z_to_bv 64 j) (Z_to_bv 64 (datas + 4 * (i * wpls))) (Z_to_bv 64 (datad + 4 * (i * wpld))))
          F (Z_to_bv 64 0x9dacc) fc None mm (seg_rom asegs))).
  { intros ra' a1' s11' mm wd' MU1 WM1 MI1 HB1 ACCS1 UA1 UAL1 ACCD1 FC1 SL1.
    clear MI HB ACCS UA UAL ACCD FC SL MU WM.
    lwalk [0x9dae4; 0x9da6c]. sx32_fix.
    replace (4 * j + 4) with (4 * (j + 1)) by lia. replace (2 * j + 2) with (2 * (j + 1)) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w) by lia. rewrite EJ in *.
      brT. apply evt_done. unfold band_row_exit, band_inv, SHB. do 9 eexists. exists mm, wd'. split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    - brF.
      eapply evt_cut.
      + eapply (IH (j + 1)) with (bs := bs) (wd := wd') (h := h) (w := w) (c48 := c48) (p0 := p0) (p1 := p1); try eassumption; try lia.
        unfold band_inv. repeat (split; [assumption|]). assumption.
      + intros ms' PO. apply evt_done. unfold band_row_exit in PO |- *.
        destruct PO as (ra'' & t1'' & t2'' & a1'' & s11'' & t3'' & t4'' & t5'' & t6'' & m' & wd'' & E & MU' & WM' & R).
        exists ra'', t1'', t2'', a1'', s11'', t3'', t4'', t5'', t6'', m', wd''.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }
  (* [comment removed for export] *)
  pose proof (lxor3_eq (datas + 4 * (i * wpls) + j)) as LX.
  lwalk [0x9db08; 0x9dc88; 0x9db10; 0x9db44].
  destruct (bytes_at_read1 m datas bs (Z.lxor (datas + 4 * (i * wpls) + j) 3 - datas) HB ltac:(lia)) as (bv & R).
  replace (datas + (Z.lxor (datas + 4 * (i * wpls) + j) 3 - datas)) with (Z.lxor (datas + 4 * (i * wpls) + j) 3) in R by lia.
  lstep. clear R.
  (* [comment removed for export] *)
  lwalk [0x9db80].
  lwalk [0x9dacc; 0x9dabc; 0x9dc80].
  brfork B1; [solve [eapply CONT; eassumption]|].
  (* [comment removed for export] *)
  lwalk [0x9dabc; 0x9dc80].
  rewrite !(srliw_idx j 32) by lia.
  replace (datad + 4 * (i * wpld) + j / 32 * 4) with (datad + 4 * (i * wpld + j / 32)) by lia.
  rewrite (Z.mod_small (datad + 4 * (i * wpld + j / 32)) 18446744073709551616) by lia.
  lwalk [0x9dabc; 0x9dc80].
  destruct (u32arr_nth wd (i * wpld + j / 32) ltac:(lia)) as (dv & NTHD).
  pose proof (u32arr_read asegs m datad wd (i * wpld + j / 32) dv _ UA NTHD ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9dac8].
  arr_sw datad (i * wpld + j / 32) (datad + 4 * (i * wpld + j / 32)).
  eapply CONT; eassumption.
Qed.

Lemma band_px4 : band_px_stmt 4.
Proof.
  unfold band_px_stmt.
  induction k as [|k IH]; intros j ra sp gp tp s0 a1 a5 s2 s3 s4 s6 s9 s11 F fc m sa fr datas datad wpls wpld w h i bs wd c48 p0 p1
    HK HJ HK1 HI GEO INV.
  { lia. }
  pose proof GEO as (HW & WS & WD & WPLS & WPLD & HH & SH & DH & S0 & S8 & SHI & SSH & SSEG & D0 & D8 & DHI & DSH & DSEG & SEP
                     & FR0 & FRHI & FRD & SA0 & SAHI & SAD).
  destruct INV as (MI & HB & HBL & ACCS & UA & UAL & ACCD & FC & SL).
  assert (NS : i * wpls + wpls <= wpls * h) by (clear - HI WPLS; nia).
  assert (NS0 : 0 <= i * wpls) by (clear - HI WPLS; nia).
  assert (ND : i * wpld + wpld <= wpld * h) by (clear - HI WPLD; nia).
  assert (ND0 : 0 <= i * wpld) by (clear - HI WPLD; nia).
  assert (JD : 0 <= j / 32 < wpld) by (clear - HJ HK WD HW; Z.div_mod_to_equations; lia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (BD_W datad (4 * (wpld * h))) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (CONT : forall (ra' a1' s11' : word) (mm : mem) (wd' : list word),
    munch (BD_W datad (4 * (wpld * h))) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    bytes_at asegs mm datas bs -> acc asegs mm datas (4 * (wpls * h)) ->
    u32arr asegs mm datad wd' -> Z.of_nat (length wd') = wpld * h -> acc asegs mm datad (4 * (wpld * h)) ->
    rw_cells asegs mm (fr + 32) [C4 (Z_to_bv 64 w); CB 12 p0; C4 (Z_to_bv 64 h); CB 12 p1; C4 (Z_to_bv 64 4)] ->
    rw_cells asegs mm (sa + 32) [C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 datas); C8 c48; C8 (Z_to_bv 64 (fr + 48))] ->
    evt asegs (band_row_exit sp gp tp (Z_to_bv 64 (datas + 4 * (i * wpls))) s0 (Z_to_bv 64 sa) (Z_to_bv 64 wpld) (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpls))
               (Z_to_bv 64 4) a5 (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 8) s2 s3 s4 (Z_to_bv 64 (fr + 64)) s6 (Z_to_bv 64 (fr + 32)) s9 (Z_to_bv 64 wpls)
               F fc m sa fr datas datad wpls wpld w h 4 bs c48 p0 p1)
      (MS (mkR ra' sp gp tp (Z_to_bv 64 (datas + 4 * (i * wpls))) (Z_to_bv 64 (4 * j)) (Z_to_bv 64 (2 * j)) s0 (Z_to_bv 64 sa)
             (Z_to_bv 64 wpld) a1' (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpls)) (Z_to_bv 64 4) a5 (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 8)
             s2 s3 s4 (Z_to_bv 64 (fr + 64)) s6 (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 2147450880) s9 (Z_to_bv 64 wpls) s11'
             (Z_to_bv 64 j) (Z_to_bv 64 j) (Z_to_bv 64 (datas + 4 * (i * wpls))) (Z_to_bv 64 (datad + 4 * (i * wpld))))
          F (Z_to_bv 64 0x9dacc) fc None mm (seg_rom asegs))).
  { intros ra' a1' s11' mm wd' MU1 WM1 MI1 HB1 ACCS1 UA1 UAL1 ACCD1 FC1 SL1.
    clear MI HB ACCS UA UAL ACCD FC SL MU WM.
    lwalk [0x9dae4; 0x9da6c]. sx32_fix.
    replace (4 * j + 4) with (4 * (j + 1)) by lia. replace (2 * j + 2) with (2 * (j + 1)) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w) by lia. rewrite EJ in *.
      brT. apply evt_done. unfold band_row_exit, band_inv, SHB. do 9 eexists. exists mm, wd'. split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    - brF.
      eapply evt_cut.
      + eapply (IH (j + 1)) with (bs := bs) (wd := wd') (h := h) (w := w) (c48 := c48) (p0 := p0) (p1 := p1); try eassumption; try lia.
        unfold band_inv. repeat (split; [assumption|]). assumption.
      + intros ms' PO. apply evt_done. unfold band_row_exit in PO |- *.
        destruct PO as (ra'' & t1'' & t2'' & a1'' & s11'' & t3'' & t4'' & t5'' & t6'' & m' & wd'' & E & MU' & WM' & R).
        exists ra'', t1'', t2'', a1'', s11'', t3'', t4'', t5'', t6'', m', wd''.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }
  (* [comment removed for export] *)
  assert (JS : 0 <= j / 8 < wpls) by (clear - HJ HK WS HW; Z.div_mod_to_equations; lia).
  lwalk [0x9db1c].
  rewrite !(srliw_idx j 8) by lia.
  replace (datas + 4 * (i * wpls) + j / 8 * 4) with (datas + 4 * (i * wpls + j / 8)) by lia.
  lwalk [0x9db2c; 0x9dc90].
  destruct (bytes_at_read4w m datas bs (4 * (i * wpls + j / 8)) HB ltac:(lia) ltac:(lia)) as (wv & R).
  lstep. clear R.
  lwalk [0x9db80].
  lwalk [0x9dacc; 0x9dabc; 0x9dc80].
  brfork B1; [solve [eapply CONT; eassumption]|].
  (* [comment removed for export] *)
  lwalk [0x9dabc; 0x9dc80].
  rewrite !(srliw_idx j 32) by lia.
  replace (datad + 4 * (i * wpld) + j / 32 * 4) with (datad + 4 * (i * wpld + j / 32)) by lia.
  rewrite (Z.mod_small (datad + 4 * (i * wpld + j / 32)) 18446744073709551616) by lia.
  lwalk [0x9dabc; 0x9dc80].
  destruct (u32arr_nth wd (i * wpld + j / 32) ltac:(lia)) as (dv & NTHD).
  pose proof (u32arr_read asegs m datad wd (i * wpld + j / 32) dv _ UA NTHD ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9dac8].
  arr_sw datad (i * wpld + j / 32) (datad + 4 * (i * wpld + j / 32)).
  eapply CONT; eassumption.
Qed.

Lemma band_px2 : band_px_stmt 2.
Proof.
  unfold band_px_stmt.
  induction k as [|k IH]; intros j ra sp gp tp s0 a1 a5 s2 s3 s4 s6 s9 s11 F fc m sa fr datas datad wpls wpld w h i bs wd c48 p0 p1
    HK HJ HK1 HI GEO INV.
  { lia. }
  pose proof GEO as (HW & WS & WD & WPLS & WPLD & HH & SH & DH & S0 & S8 & SHI & SSH & SSEG & D0 & D8 & DHI & DSH & DSEG & SEP
                     & FR0 & FRHI & FRD & SA0 & SAHI & SAD).
  destruct INV as (MI & HB & HBL & ACCS & UA & UAL & ACCD & FC & SL).
  assert (NS : i * wpls + wpls <= wpls * h) by (clear - HI WPLS; nia).
  assert (NS0 : 0 <= i * wpls) by (clear - HI WPLS; nia).
  assert (ND : i * wpld + wpld <= wpld * h) by (clear - HI WPLD; nia).
  assert (ND0 : 0 <= i * wpld) by (clear - HI WPLD; nia).
  assert (JD : 0 <= j / 32 < wpld) by (clear - HJ HK WD HW; Z.div_mod_to_equations; lia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (BD_W datad (4 * (wpld * h))) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (CONT : forall (ra' a1' s11' : word) (mm : mem) (wd' : list word),
    munch (BD_W datad (4 * (wpld * h))) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    bytes_at asegs mm datas bs -> acc asegs mm datas (4 * (wpls * h)) ->
    u32arr asegs mm datad wd' -> Z.of_nat (length wd') = wpld * h -> acc asegs mm datad (4 * (wpld * h)) ->
    rw_cells asegs mm (fr + 32) [C4 (Z_to_bv 64 w); CB 12 p0; C4 (Z_to_bv 64 h); CB 12 p1; C4 (Z_to_bv 64 2)] ->
    rw_cells asegs mm (sa + 32) [C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 datas); C8 c48; C8 (Z_to_bv 64 (fr + 48))] ->
    evt asegs (band_row_exit sp gp tp (Z_to_bv 64 (datas + 4 * (i * wpls))) s0 (Z_to_bv 64 sa) (Z_to_bv 64 wpld) (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpls))
               (Z_to_bv 64 4) a5 (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 8) s2 s3 s4 (Z_to_bv 64 (fr + 64)) s6 (Z_to_bv 64 (fr + 32)) s9 (Z_to_bv 64 wpls)
               F fc m sa fr datas datad wpls wpld w h 2 bs c48 p0 p1)
      (MS (mkR ra' sp gp tp (Z_to_bv 64 (datas + 4 * (i * wpls))) (Z_to_bv 64 (4 * j)) (Z_to_bv 64 (2 * j)) s0 (Z_to_bv 64 sa)
             (Z_to_bv 64 wpld) a1' (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpls)) (Z_to_bv 64 4) a5 (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 8)
             s2 s3 s4 (Z_to_bv 64 (fr + 64)) s6 (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 2147450880) s9 (Z_to_bv 64 wpls) s11'
             (Z_to_bv 64 j) (Z_to_bv 64 j) (Z_to_bv 64 (datas + 4 * (i * wpls))) (Z_to_bv 64 (datad + 4 * (i * wpld))))
          F (Z_to_bv 64 0x9dacc) fc None mm (seg_rom asegs))).
  { intros ra' a1' s11' mm wd' MU1 WM1 MI1 HB1 ACCS1 UA1 UAL1 ACCD1 FC1 SL1.
    clear MI HB ACCS UA UAL ACCD FC SL MU WM.
    lwalk [0x9dae4; 0x9da6c]. sx32_fix.
    replace (4 * j + 4) with (4 * (j + 1)) by lia. replace (2 * j + 2) with (2 * (j + 1)) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w) by lia. rewrite EJ in *.
      brT. apply evt_done. unfold band_row_exit, band_inv, SHB. do 9 eexists. exists mm, wd'. split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    - brF.
      eapply evt_cut.
      + eapply (IH (j + 1)) with (bs := bs) (wd := wd') (h := h) (w := w) (c48 := c48) (p0 := p0) (p1 := p1); try eassumption; try lia.
        unfold band_inv. repeat (split; [assumption|]). assumption.
      + intros ms' PO. apply evt_done. unfold band_row_exit in PO |- *.
        destruct PO as (ra'' & t1'' & t2'' & a1'' & s11'' & t3'' & t4'' & t5'' & t6'' & m' & wd'' & E & MU' & WM' & R).
        exists ra'', t1'', t2'', a1'', s11'', t3'', t4'', t5'', t6'', m', wd''.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }
  (* [comment removed for export] *)
  assert (JS : 0 <= j / 16 < wpls) by (clear - HJ HK WS HW; Z.div_mod_to_equations; lia).
  lwalk [0x9db50].
  rewrite !(srliw_idx j 16) by lia.
  replace (datas + 4 * (i * wpls) + j / 16 * 4) with (datas + 4 * (i * wpls + j / 16)) by lia.
  lwalk [0x9db60; 0x9dbd8].
  destruct (bytes_at_read4w m datas bs (4 * (i * wpls + j / 16)) HB ltac:(lia) ltac:(lia)) as (wv & R).
  lstep. clear R.
  lwalk [0x9db80].
  lwalk [0x9dacc; 0x9dabc; 0x9dc80].
  brfork B1; [solve [eapply CONT; eassumption]|].
  (* [comment removed for export] *)
  lwalk [0x9dabc; 0x9dc80].
  rewrite !(srliw_idx j 32) by lia.
  replace (datad + 4 * (i * wpld) + j / 32 * 4) with (datad + 4 * (i * wpld + j / 32)) by lia.
  rewrite (Z.mod_small (datad + 4 * (i * wpld + j / 32)) 18446744073709551616) by lia.
  lwalk [0x9dabc; 0x9dc80].
  destruct (u32arr_nth wd (i * wpld + j / 32) ltac:(lia)) as (dv & NTHD).
  pose proof (u32arr_read asegs m datad wd (i * wpld + j / 32) dv _ UA NTHD ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9dac8].
  arr_sw datad (i * wpld + j / 32) (datad + 4 * (i * wpld + j / 32)).
  eapply CONT; eassumption.
Qed.

(* [comment removed for export] *)
Definition band_exit (sp gp tp s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (sa fr datas datad wpls wpld w h d : Z) (bs : list byte) (c48 : word) (p0 p1 : list byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a1' a2' s11' t3' t4' t5' t6' : word) (m' : mem) (wd' : list word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 SHB) s9 s10 s11' t3' t4' t5' t6')
             F (Z_to_bv 64 0x9dbe0) fc None m' (seg_rom asegs)
    /\ munch (BD_W datad (4 * (wpld * h))) m m' /\ wmono asegs m m'
    /\ band_inv m' sa fr datas datad wpls wpld w h d bs wd' c48 p0 p1.

Lemma band_rows : forall (d : Z), In d [2; 4; 8] -> forall (k : nat) (i : Z)
    (ra sp gp tp t1 t2 s0 a1 a5 s2 s3 s4 s6 s9 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (sa fr datas datad wpls wpld w h : Z) (bs : list byte) (wd : list word) (c48 : word) (p0 p1 : list byte),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat -> band_geom sa fr datas datad wpls wpld w h d ->
  band_inv m sa fr datas datad wpls wpld w h d bs wd c48 p0 p1 ->
  evt asegs (band_exit sp gp tp s0 (Z_to_bv 64 sa) (Z_to_bv 64 wpld) (Z_to_bv 64 (4 * wpls))
               (Z_to_bv 64 4) a5 (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 8) s2 s3 s4 (Z_to_bv 64 (fr + 64)) s6 (Z_to_bv 64 (fr + 32)) s9 (Z_to_bv 64 wpls)
               F fc m sa fr datas datad wpls wpld w h d bs c48 p0 p1)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (datas + 4 * (i * wpls))) t1 t2 s0 (Z_to_bv 64 sa)
             (Z_to_bv 64 wpld) a1 (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpls)) (Z_to_bv 64 4) a5 (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 8)
             s2 s3 s4 (Z_to_bv 64 (fr + 64)) s6 (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 SHB) s9 (Z_to_bv 64 wpls) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9da80) fc None m (seg_rom asegs)).
Proof.
  intros d HD.
  assert (PX : band_px_stmt d) by (destruct HD as [<-|[<-|[<-|[]]]]; [exact band_px2| exact band_px4| exact band_px8]).
  clear HD. unfold band_px_stmt in PX.
  induction k as [|k IH]; intros i ra sp gp tp t1 t2 s0 a1 a5 s2 s3 s4 s6 s9 s11 t3 t4 t5 t6 F fc m sa fr datas datad wpls wpld w h bs wd c48 p0 p1
    HK HI HK1 GEO INV.
  { lia. }
  pose proof GEO as (HW & WS & WD & WPLS & WPLD & HH & SH & DH & S0 & S8 & SHI & SSH & SSEG & D0 & D8 & DHI & DSH & DSEG & SEP
                     & FR0 & FRHI & FRD & SA0 & SAHI & SAD).
  pose proof INV as (MI & HB & HBL & ACCS & UA & UAL & ACCD & FC & SL).
  assert (NS0 : 0 <= i * wpls <= 2^24) by (clear - HI HK HH WPLS SH; nia).
  assert (ND0 : 0 <= i * wpld <= 2^24) by (clear - HI HK HH WPLD DH; nia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (BD_W datad (4 * (wpld * h))) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0x9dae4; 0x9da6c].
  rewrite (sx32_small w) by lia.
  brF.
  lwalk [0x9dae4; 0x9da6c].
  (* [comment removed for export] *)
  replace (datad + i * wpld * 4) with (datad + 4 * (i * wpld)) by (clear; lia).
  replace (datas + i * wpls * 4) with (datas + 4 * (i * wpls)) by (clear; lia).
  assert (Q1 : Z.of_nat (Z.to_nat w) = w - 0) by (clear - HW; lia).
  assert (Q3 : (1 <= Z.to_nat w)%nat) by (clear - HW; lia).
  assert (Q4 : 0 <= i < h) by (clear - HI HK; lia).
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (PX (Z.to_nat w) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm sa fr datas datad wpls wpld w h i bs wd c48 p0 p1 Q1 ltac:(lia) Q3 Q4 GEO INV) as ZR end.
    unfold SHB in ZR. exact ZR. }
  intros ms' PO. unfold band_row_exit in PO.
  destruct PO as (ra' & t1' & t2' & a1' & s11' & t3' & t4' & t5' & t6' & m' & wd' & -> & MU' & WM' & INV').
  clear MI HB ACCS UA UAL ACCD FC SL INV.
  pose proof INV' as (MI & HB & HBL' & ACCS & UA & UAL & ACCD & FC & SL).
  pose proof (munch_trans _ _ _ _ MU MU') as MUc. pose proof (wmono_trans asegs _ _ _ WM WM') as WMc. clear MU WM MU' WM'.
  unfold SHB in *.
  lwalk [0x9da80; 0x9dbe0].
  rewrite (sx32_small h) by lia.
  replace (datas + 4 * (i * wpls) + 4 * wpls) with (datas + 4 * ((i + 1) * wpls)) by (clear; lia).
  destruct k as [|k].
  - assert (EI : i + 1 = h) by lia. rewrite EI in *.
    brT. apply evt_done. unfold band_exit, SHB. do 11 eexists. exists m', wd'. split; [reflexivity|].
    split; [exact MUc|]. split; [exact WMc| exact INV'].
  - brF.
    eapply evt_cut.
    + eapply (IH (i + 1)) with (bs := bs) (wd := wd') (w := w) (c48 := c48) (p0 := p0) (p1 := p1); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold band_exit in PO |- *.
      destruct PO as (ra'' & t0'' & t1'' & t2'' & a1'' & a2'' & s11'' & t3'' & t4'' & t5'' & t6'' & m'' & wd'' & E & MU'' & WM'' & R).
      exists ra'', t0'', t1'', t2'', a1'', a2'', s11'', t3'', t4'', t5'', t6'', m'', wd''.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MUc MU'')|]. split; [exact (wmono_trans asegs _ _ _ WMc WM'')| exact R].
Qed.
