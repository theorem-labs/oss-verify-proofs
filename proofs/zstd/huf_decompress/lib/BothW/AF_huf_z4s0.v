(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_fa_iface AF_huf_z4s3_iface AF_huf_z4d_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4skx.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Lemma z4_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma z4_landm : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small; lia. Qed.
Ltac z4chk K H1 H2 H3 H4 H5 := exfalso; clear - K H1 H2 H3 H4 H5;
  rewrite ?Z.shiftr_div_pow2 in K by lia; rewrite ?z4_landm in K by (Z.div_mod_to_equations; lia);
  rewrite ?zb_lxor_ones in K by (Z.div_mod_to_equations; lia); rewrite ?z4_land3 in K;
  Z.div_mod_to_equations; lia.
Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma z4s0_pro : forall (Q : machine_state -> Prop) (RNG : footprint) (m : amem) (F : bvmap 5 word) (fc : bv 32)
    (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (DST dcap SS n DT lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> mem_inv bsegs m -> rt_got m -> rt_shbase m -> lo <= bv_unsigned sp - 384 ->
  rng RNG (bv_unsigned sp - 384) 384 -> rng_aimg RNG -> 2^46 <= bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
  0 <= DST -> (0 < dcap -> 4096 <= DST) -> DST + dcap <= 2^47 -> 0 <= dcap < 2^32 -> 0 <= n < 2^26 ->
  (10 <= n -> 4096 <= SS /\ SS + n <= 2^47) -> 4096 <= DT <= 2^47 ->
  (forall mm (j1 j2 : list byte)
          (z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
     dcap < 6 \/ n < 10 ->
     stk bsegs mm lo (bv_unsigned sp + -384) ->
     rw_cells bsegs mm (bv_unsigned sp + -384) [CB 112 j1; C8 (Z_to_bv 64 dcap); CB 160 j2] ->
     rw_cells bsegs mm (bv_unsigned sp + -104)
       [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     mem_inv bsegs mm -> munch [(bv_unsigned sp - 384, bv_unsigned sp)] m mm -> wmono bsegs m mm ->
     evtF bsegs RNG Q (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16
                               z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31)
                          F (Z_to_bv 64 AZ4_DEPI) fc None mm (seg_rom bsegs))) ->
  (forall mm (j1 j2 : list byte) (z1 z5 z6 z7 z8 z9 z10 z11 z15 z17 z18 z19 z20 z22 z23 z24 z25 z26 z27 z28 z31 : word),
     6 <= dcap -> 10 <= n ->
     stk bsegs mm lo (bv_unsigned sp + -384) ->
     rw_cells bsegs mm (bv_unsigned sp + -384) [CB 112 j1; C8 (Z_to_bv 64 dcap); CB 160 j2] ->
     rw_cells bsegs mm (bv_unsigned sp + -104)
       [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     rt_got mm -> rt_shbase mm ->
     mem_inv bsegs mm -> munch [(bv_unsigned sp - 384, bv_unsigned sp)] m mm -> wmono bsegs m mm ->
     evtF bsegs RNG Q (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp z5 z6 z7 z8 z9 z10 z11 (Z_to_bv 64 SS)
                               (Z_to_bv 64 n) (Z_to_bv 64 DT) z15 (Z_to_bv 64 DST) z17 z18 z19 z20 (Z_to_bv 64 AZ4_SB)
                               z22 z23 z24 z25 z26 z27 z28 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) z31)
                          F (Z_to_bv 64 (AZ4_D + 172)) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SS) (Z_to_bv 64 n)
                            (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 AZ4_D) fc None m (seg_rom bsegs)).
Proof.
  intros Q RNG m F fc ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 DST dcap SS n DT lo
    ST MI GOT SHB LOS RS RI SPB SP16 HD0 HDP HD1 HDC HN HS HDT KX KC.
  unfold AZ4_D, AZ4_DEPI, AZ4_SB in *.
  pose proof (munch_refl [(bv_unsigned sp - 384, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep.
  carve_frame 104%nat ST. carve_frame 280%nat ST.
  do 17 zstep.
  zstep. if_cases K72; zify_cond K72;
    [| zstep; eapply KX; [lia | eassumption ..]].
  zstep.
  zstep. if_cases K84; zify_cond K84;
    [| zstep; eapply KX; [lia | eassumption ..]].
  destruct (HS ltac:(lia)) as (HS0 & HS1).
  zstep. if_cases K92; zify_cond K92; [|exfalso; lia].
  assert (DSTP : 4096 <= DST) by lia.
  do 2 zstep.
  zstep. if_cases K108; zify_cond K108; [|exfalso; lia].
  zstep. if_cases K116; zify_cond K116; [|exfalso; lia].
  zstep.
  zstep. if_cases K128; zify_cond K128; [|exfalso; lia].
  do 2 zstep.
  zstep. if_cases K144; zify_cond K144; [|exfalso; lia].
  zstep. if_cases K152; zify_cond K152; [|exfalso; lia].
  do 3 zstep.
  eapply KC; [lia | lia | eassumption ..].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma z4s0_hdr : forall (Q : machine_state -> Prop) (RNG : footprint) (m mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 x5 x6 x7 x8 x10 x12 x17 x22 x23 x24 x25 x26 x27 x28 x31 gp tp sp : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (DST dcap SS n DT lo l1 l2 l3 mtl tl : Z) (j1 j2 : list byte),
  stk bsegs mm lo (bv_unsigned sp + -384) ->
  rw_cells bsegs mm (bv_unsigned sp + -384) [CB 112 j1; C8 (Z_to_bv 64 dcap); CB 160 j2] ->
  rw_cells bsegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv bsegs mm -> munch [(bv_unsigned sp - 384, bv_unsigned sp)] m mm -> wmono bsegs m mm ->
  rng RNG (bv_unsigned sp - 384) 384 -> rng_aimg RNG -> 2^46 <= bv_unsigned sp <= 2^47 ->
  lo <= bv_unsigned sp - 384 -> bv_unsigned sp mod 16 = 0 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 10 <= n < 2^26 -> 4096 <= SS -> SS + n <= 2^47 ->
  4096 <= DT <= 2^47 -> DT mod 4 = 0 ->
  0 <= l1 < 65536 -> 0 <= l2 < 65536 -> 0 <= l3 < 65536 -> 1 <= mtl <= 12 -> 0 <= tl <= mtl ->
  bytes_at bsegs mm DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl] -> rng RNG DT 4 ->
  unpoisoned mm DT (DT + 8) -> DT mod 8 = 0 -> rng RNG (shad DT) 1 -> DT + 8 <= lo ->
  (forall mm' (je : list byte)
          (z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
     stk bsegs mm' lo (bv_unsigned sp + -384) ->
     rw_cells bsegs mm' (bv_unsigned sp + -384) [CB 280 je] ->
     rw_cells bsegs mm' (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     mem_inv bsegs mm' -> munch [(bv_unsigned sp - 384, bv_unsigned sp)] m mm' -> wmono bsegs m mm' ->
     evtF bsegs RNG Q (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16
                               z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31)
                          F (Z_to_bv 64 AZ4_DEPI) fc None mm' (seg_rom bsegs))) ->
  (forall mm' (ja jb jc : list byte) (z1 z5 z6 z7 z10 z12 z13 z14 z16 z17 z24 z27 z28 z29 z30 z31 : word),
     6 + l1 + l2 + l3 <= n ->
     stk bsegs mm' lo (bv_unsigned sp + -384) ->
     rw_cells bsegs mm' (bv_unsigned sp + -384)
       [CB 48 ja; C8 (Z_to_bv 64 (DST + dcap)); CB 16 jb; C8 (Z_to_bv 64 (DST + (dcap + 3) / 4));
        C8 (Z_to_bv 64 (DST + 2 * ((dcap + 3) / 4))); CB 16 jc; C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 dcap); CB 160 j2] ->
     rw_cells bsegs mm' (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     mem_inv bsegs mm' -> munch [(bv_unsigned sp - 384, bv_unsigned sp)] m mm' -> wmono bsegs m mm' ->
     evtF bsegs RNG Q (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp z5 z6 z7 (Z_to_bv 64 DST)
                               (Z_to_bv 64 (SS + 6 + l1 + l2)) z10 (Z_to_bv 64 (SS + 6)) z12 z13 z14 (Z_to_bv 64 l1) z16 z17
                               (Z_to_bv 64 l3) (Z_to_bv 64 l2) (Z_to_bv 64 (SS + 6 + l1)) (Z_to_bv 64 AZ4_SB)
                               (Z_to_bv 64 (6 + l1 + l2 + l3)) (Z_to_bv 64 n) z24 (Z_to_bv 64 (tl + 256 * mtl))
                               (Z_to_bv 64 (DST + 3 * ((dcap + 3) / 4))) z27 z28 z29 z30 z31)
                          F (Z_to_bv 64 AZ4_I1) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (SS + 6 + l1 + l2)) x10
                            (Z_to_bv 64 (SS + 6)) x12 (Z_to_bv 64 n) (Z_to_bv 64 DT) (Z_to_bv 64 l1) (Z_to_bv 64 DST) x17
                            (Z_to_bv 64 l3) (Z_to_bv 64 l2) (Z_to_bv 64 (SS + 6 + l1)) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25
                            x26 x27 x28 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) x31)
                       F (Z_to_bv 64 (AZ4_D + 448)) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG m mm F fc x1 x5 x6 x7 x8 x10 x12 x17 x22 x23 x24 x25 x26 x27 x28 x31 gp tp sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 DST dcap SS n DT lo l1 l2 l3
    mtl tl j1 j2 ST FRA FRB MI MU WM RS RI SPB LOS SP16 HD0 HD1 HDC HN HS0 HS1 HDT HDT4 HL1 HL2 HL3 HMT HTL DTB RDT UDT DT8 RSD DTL KE KC.
  unfold AZ4_D, AZ4_SB, AZ4_I1, AZ4_DEPI in *.
  pose proof (unpoisoned_full mm DT (DT + 8) (DT / 8) UDT ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as SB0.
  apply (rw_cells_C1_of_byte bsegs) in SB0; [| unfold ASHOFF in *; Z.div_mod_to_equations; lia | unfold ASHOFF in *; Z.div_mod_to_equations; lia].
  unfold shad in RSD. unfold ASHOFF in SB0, RSD.
  assert (DTG : DT = 8 * (DT / 8)) by (Z.div_mod_to_equations; lia).
  assert (DTGB : 512 <= DT / 8 <= 2^44) by (Z.div_mod_to_equations; lia).
  set (g := DT / 8) in *.
  rewrite ?Z.shiftr_div_pow2 in RSD by lia; change (2^3) with 8 in RSD; change (DT / 8) with g in RSD.
  do 4 zstep.
  zstep. if_cases K464; zify_cond K464; [|z4chk K464 HD0 HD1 HDC HN DT8].
  do 2 zstep.
  zstep. if_cases K480; zify_cond K480; [|z4chk K480 HD0 HD1 HDC HN DT8].
  do 3 zstep.
  zstep. if_cases K500; zify_cond K500; [|z4chk K500 HD0 HD1 HDC HN DT8].
  do 2 zstep.
  zstep. if_cases K516; zify_cond K516; [|z4chk K516 HD0 HD1 HDC HN DT8].
  zstep. zstep. rewrite (Z.shiftr_div_pow2 DT 3) by lia; change (2^3) with 8; change (DT / 8) with g.
  rewrite (Z.add_comm _ g) in SB0.
  zstep.
  zstep. if_cases K536; zify_cond K536; [|exfalso; apply K536; vm_compute; reflexivity].
  do 4 zstep.
  zstep. if_cases K560; zify_cond K560; [|zstep; lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -384) _ |- _ =>
      apply rw_cells_forget in H; destruct H as (je & H); cbn [cells_size csize Nat.add] in H end;
    eapply KE; eassumption].
  do 2 zstep.
  zstep. if_cases K576; zify_cond K576; [|z4chk K576 HD0 HD1 HDC HN DT8].
  zstep. zstep. zstep. zstep.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => assert (RODT : ro_cells bsegs mx DT [C1 (Z_to_bv 8 mtl); C1 (Z_to_bv 8 1); C2 (Z_to_bv 64 (tl + 256 * mtl))])
    by (unfold ro_cells, cells_at; split; [cbn [cells_wf cell_wf length]; repeat split | cbn [cells_bytes cbytes app]; rewrite le2_two_bytes by lia; eassumption]) end.
  zstep. rewrite ?zext_extract_le2.
  rewrite zx16_short by lia. rewrite (Z.mod_small (tl + 256 * mtl)) by lia.
  replace (l1 + l2 + l3 + 6) with (6 + l1 + l2 + l3) by lia.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -384) _ |- _ => rewrite ?Z.shiftr_div_pow2 in H by lia; rename H into FRC end.
  rewrite ?Z.shiftr_div_pow2 by lia. change (2^2) with 4 in *.
  replace (DST + (dcap + 3) / 4 + (dcap + 3) / 4) with (DST + 2 * ((dcap + 3) / 4)) in FRC by lia.
  replace (DST + (dcap + 3) / 4 + (dcap + 3) / 4 + (dcap + 3) / 4) with (DST + 3 * ((dcap + 3) / 4)) by lia.
  eapply KC; [lia | eassumption ..].
Qed.

Lemma z4d_epi : forall (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word)
    (fc : bv 32) (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte),
  lo <= bv_unsigned sp - 384 -> 2^46 <= bv_unsigned sp <= 2^47 -> rng RNG (bv_unsigned sp - 384) 384 -> rng_aimg RNG ->
  z4epi_hyp RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs
    (z4d_postA RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc DST dcap lo m0).
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs LOS SPB RS RI.
  unfold z4epi_hyp. intros mm spl bd4 bd3 bd2 bd1 z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22
    z23 z24 z25 z26 z27 z28 z29 z30 z31
    (_ & _ & _ & _ & ST & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRB & MI & MU & WM).
  pose proof (stk_release bsegs mm lo _ _ ST SPL ltac:(lia)) as L0. rewrite SPLS in L0.
  replace (bv_unsigned sp + -384 + Z.of_nat 120) with (bv_unsigned sp + -264) in L0 by lia.
  pose proof (stk_release bsegs mm lo _ _ L0 B4 ltac:(lia)) as L1. rewrite B4S in L1.
  replace (bv_unsigned sp + -264 + Z.of_nat 40) with (bv_unsigned sp + -224) in L1 by lia.
  pose proof (stk_release bsegs mm lo _ _ L1 B3 ltac:(lia)) as L2. rewrite B3S in L2.
  replace (bv_unsigned sp + -224 + Z.of_nat 40) with (bv_unsigned sp + -184) in L2 by lia.
  pose proof (stk_release bsegs mm lo _ _ L2 B2 ltac:(lia)) as L3. rewrite B2S in L3.
  replace (bv_unsigned sp + -184 + Z.of_nat 40) with (bv_unsigned sp + -144) in L3 by lia.
  pose proof (stk_release bsegs mm lo _ _ L3 B1 ltac:(lia)) as L4. rewrite B1S in L4.
  replace (bv_unsigned sp + -144 + Z.of_nat 40) with (bv_unsigned sp + -104) in L4 by lia.
  clear ST SPL SPLS B4 B4S B3 B3S B2 B2S B1 B1S L0 L1 L2 L3.
  unfold AZ4_DEPI.
  zstep. do 13 zstep. zstep. zstep.
  release_frame FRB L4 (bv_unsigned sp).
  apply evtF_done. unfold z4d_postA.
  try (lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned sp + ?k + ?k')] =>
         replace (bv_unsigned sp + k + k') with (bv_unsigned sp) by lia end).
  rewrite ?Z_to_bv_bv_unsigned.
  do 16 eexists. split; [reflexivity|].
  split; [exact MI|]. split; [eassumption|]. split; [exact MU | exact WM].
Qed.

Lemma z4s0_entry : forall (Q : machine_state -> Prop) (RNG : footprint) (m0 : amem) (F : bvmap 5 word) (fc : bv 32)
    (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (DST dcap SS DT lo mtl tl SBL SBH : Z) (src : list Z),
  stk bsegs m0 lo (bv_unsigned sp) -> mem_inv bsegs m0 -> rt_got m0 -> rt_shbase m0 -> lo <= bv_unsigned sp - 384 ->
  rng RNG (bv_unsigned sp - 384) 384 -> rng_aimg RNG -> 2^46 <= bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
  0 <= DST -> (0 < dcap -> 4096 <= DST) -> DST + dcap <= 2^47 -> 0 <= dcap < 2^32 -> zlen src < 2^26 ->
  4096 <= DT -> DT + 8 <= lo -> DT mod 8 = 0 -> 1 <= mtl <= 12 -> 0 <= tl <= mtl ->
  bytes_at bsegs m0 SS (map (Z_to_bv 8) src) ->
  bytes_at bsegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl] -> rng RNG DT 4 -> rng RNG (shad DT) 1 ->
  (forall mm, munch [(bv_unsigned sp - 384, bv_unsigned sp)] m0 mm -> unpoisoned mm DT (DT + 8)) ->
  (10 <= zlen src -> 4096 <= SBL /\ SBL mod 8 = 0 /\ SBL <= SS /\ SS + zlen src <= SBH /\ SBH <= 2^47 /\ SBH <= lo
     /\ rng RNG SS (zlen src) /\ rng RNG (shad SBL) (shlen (SBH - SBL + 7))
     /\ forall mm, munch [(bv_unsigned sp - 384, bv_unsigned sp)] m0 mm -> unpoisoned mm SBL SBH) ->
  (forall mm' (je : list byte)
          (z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
     stk bsegs mm' lo (bv_unsigned sp + -384) ->
     rw_cells bsegs mm' (bv_unsigned sp + -384) [CB 280 je] ->
     rw_cells bsegs mm' (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     mem_inv bsegs mm' -> munch [(bv_unsigned sp - 384, bv_unsigned sp)] m0 mm' -> wmono bsegs m0 mm' ->
     evtF bsegs RNG Q (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16
                               z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31)
                          F (Z_to_bv 64 AZ4_DEPI) fc None mm' (seg_rom bsegs))) ->
  (forall mm' (ja jb jc j2 : list byte) (l1 l2 l3 : Z) (z1 z5 z6 z7 z10 z12 z13 z14 z16 z17 z24 z27 z28 z29 z30 z31 : word),
     0 <= l1 < 65536 -> 0 <= l2 < 65536 -> 0 <= l3 < 65536 -> 6 + l1 + l2 + l3 <= zlen src -> 6 <= dcap -> 10 <= zlen src ->
     stk bsegs mm' lo (bv_unsigned sp + -384) ->
     rw_cells bsegs mm' (bv_unsigned sp + -384)
       [CB 48 ja; C8 (Z_to_bv 64 (DST + dcap)); CB 16 jb; C8 (Z_to_bv 64 (DST + (dcap + 3) / 4));
        C8 (Z_to_bv 64 (DST + 2 * ((dcap + 3) / 4))); CB 16 jc; C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 dcap); CB 160 j2] ->
     rw_cells bsegs mm' (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     mem_inv bsegs mm' -> munch [(bv_unsigned sp - 384, bv_unsigned sp)] m0 mm' -> wmono bsegs m0 mm' ->
     evtF bsegs RNG Q (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp z5 z6 z7 (Z_to_bv 64 DST)
                               (Z_to_bv 64 (SS + 6 + l1 + l2)) z10 (Z_to_bv 64 (SS + 6)) z12 z13 z14 (Z_to_bv 64 l1) z16 z17
                               (Z_to_bv 64 l3) (Z_to_bv 64 l2) (Z_to_bv 64 (SS + 6 + l1)) (Z_to_bv 64 AZ4_SB)
                               (Z_to_bv 64 (6 + l1 + l2 + l3)) (Z_to_bv 64 (zlen src)) z24 (Z_to_bv 64 (tl + 256 * mtl))
                               (Z_to_bv 64 (DST + 3 * ((dcap + 3) / 4))) z27 z28 z29 z30 z31)
                          F (Z_to_bv 64 AZ4_I1) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SS) (Z_to_bv 64 (zlen src))
                            (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 AZ4_D) fc None m0 (seg_rom bsegs)).
Proof.
  intros Q RNG m0 F fc ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    DST dcap SS DT lo mtl tl SBL SBH src
    ST MI RGT RSB LOS RS RI SPB SP16 D0 D1 D2 DC NS T0 T1 T8 HMT HTL BS BD RD4 RSD UD SB EX IC.
  assert (TR : forall mm A bs, bytes_at bsegs m0 A bs -> munch [(bv_unsigned sp - 384, bv_unsigned sp)] m0 mm ->
                 A + zlen bs <= lo -> bytes_at bsegs mm A bs).
  { intros mm A bs H MU HA. eapply bytes_at_transport; [exact H | exact MU |].
    cbn [disjoint_from]. split; [lia | exact I]. }
  pose proof (bytes_at_bound _ _ _ _ BS) as BSB. rewrite length_map in BSB.
  apply (z4s0_pro Q RNG m0 F fc ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           DST dcap SS (zlen src) DT lo); try assumption; try lia.
  - intros mm j1 j2 z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 _ ST1 FA FB MI1 MU1 WM1.
    apply (EX mm (cells_bytes [CB 112 j1; C8 (Z_to_bv 64 dcap); CB 160 j2]) z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31);
      try assumption.
    exact (rw_cells_merge bsegs mm _ [] [CB 112 j1; C8 (Z_to_bv 64 dcap); CB 160 j2] [] FA).
  - intros mm j1 j2 z1 z5 z6 z7 z8 z9 z10 z11 z15 z17 z18 z19 z20 z22 z23 z24 z25 z26 z27 z28 z31
      DC6 N10 ST1 FA FB _ _ MI1 MU1 WM1.
    destruct (SB N10) as (B0 & B8 & B1 & B2 & B3 & BL & R1 & R2 & U).
    pose proof z4s_J as J. unfold z4s_J_case in J.
    apply (J Q RNG mm F fc z1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp z5 z6 z7 z8 z9 z10 z11
             (Z_to_bv 64 (zlen src)) (Z_to_bv 64 DT) z15 (Z_to_bv 64 DST) z17 z18 z19 z20 z22 z23 z24 z25 z26 z27 z28
             (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) z31 SS (zlen src) SBL SBH (map (Z_to_bv 8) src));
      try assumption; try lia.
    + apply TR; [exact BS | exact MU1 | rewrite length_map; lia].
    + rewrite length_map. reflexivity.
    + exact (U mm MU1).
    + intros l1 l2 l3 a0 a2 a7' t0' t1' t2' t3' L1 L2 L3.
      apply (z4s0_hdr Q RNG m0 mm F fc z1 t0' t1' t2' z8 a0 a2 a7' z22 z23 z24 z25 z26 z27 t3' z31 gp tp sp
               ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 DST dcap SS (zlen src) DT lo l1 l2 l3 mtl tl j1 j2);
        try assumption; try lia;
        lazymatch goal with
        | |- _ mod 4 = 0 => Z.div_mod_to_equations; lia
        | |- bytes_at _ _ _ _ => apply TR; [exact BD | exact MU1 | cbn [length]; lia]
        | |- _ mm DT (DT + 8) => exact (UD mm MU1)
        | |- _ => intros; eapply IC; eassumption
        end.
Qed.

End CANSEC1.
