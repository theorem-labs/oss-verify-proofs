(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4m AF_huf_z4f_defs AF_huf_z4kx AF_huf_z4kx2 AF_huf_z4fin AF_huf_z4fin2 AF_huf_z4fin3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Startup_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Definition AZ4_TB : Z := 0x10374.

Section CANSEC1. Context {rc : runConstT}.
Section Z4FIN.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl lo : Z) (src : list Z) (cbs : list byte) (pdt pb : aptr) (SBL SBH : Z) (cells : list deltX2).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -528).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis HDB : In (HB pb DST dcap) LB.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TOK : x2_table_ok cells 11.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^11)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 8192.
  Hypothesis MTL : 11 <= mtl <= 12.
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis SG : 3 * seg < dcap.
  Hypothesis NSM : 10 <= n < 2^26.
  Hypothesis SBB : SBL <= SS /\ SS + n <= SBH.
  Hypothesis SBA : ablk SBL SBH /\ SBL mod 8 = 0.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DJ1 : KXGoM.apart DST dcap DT DTL.
  Hypothesis DJ2 : KXGoM.apart DST dcap SS n.
  Hypothesis UDT : unpoisoned m0 DT (DT + DTL).
  Hypothesis UDB : unpoisoned m0 DST (DST + dcap).
  Hypothesis USB : unpoisoned m0 SBL SBH.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WDT : rng RNG DT DTL.
  Hypothesis WDB : rng RNG DST dcap.
  Hypothesis WSB : rng RNG SBL (SBH - SBL).
  Hypothesis WDTS : rng RNG (shad DT) (shlen (DTL + 7)).
  Hypothesis WDBS : rng RNG (shad DST) (shlen (dcap + 7)).
  Hypothesis WSBS : rng RNG (shad SBL) (shlen (SBH - SBL + 7)).

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation Z4M := (AF_huf_z4m.Z4M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  
  Notation KH pc mm k prev x1 x5 x6 x9 x10 x11 x12 x13 x18 x19 x21 x22 x24 x25 x27 x30 :=
    (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 (Z_to_bv 64 65) (Z_to_bv 64 (DT + 4)) x9 x10 x11 x12 x13
             (Z_to_bv 64 k) (Z_to_bv 64 (SPF + 264)) (Z_to_bv 64 (2^64 - 1 - (DT + 4))) (Z_to_bv 64 9)
             x18 x19 (Z_to_bv 64 prev) x21 x22 (Z_to_bv 64 0x7fff8000) x24 x25 (Z_to_bv 64 0x20d53) x27
             (Z_to_bv 64 2) (Z_to_bv 64 seg) x30 (Z_to_bv 64 64))
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).


  Notation ZF l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl lo src cbs pdt pb
                      SBL SBH cells AH HDT HDB LOA LOS SPT SP16 TOK ECB LCB MTL DC SG NSM SBB SBA BYS DJ1 DJ2 UDT UDB USB
                      WSK WIM WDT WDB WSB WDTS WDBS WSBS).


  
  Lemma z4_u64arr_cell : forall m A ws (i : nat) v, u64arr bsegs m A ws -> nth_error ws i = Some v ->
    rw_cells bsegs m (A + 8 * Z.of_nat i) [C8 v].
Proof.
  intros m A ws i v (BA & WR) H.
  assert (L8 : forall w : word, length (le8 w) = 8%nat) by (intros; reflexivity).
  assert (NS : forall ws' (i' : nat) v' j, nth_error ws' i' = Some v' -> (j < 8)%nat ->
            nth_error (u64s ws') (8 * i' + j) = nth_error (le8 v') j).
  { induction ws' as [|w ws' IH]; intros i' v' j H' J; [destruct i'; discriminate|].
    destruct i' as [|i']; cbn [u64s].
    - injection H' as <-. rewrite nth_error_app1 by (rewrite L8; lia). f_equal; lia.
    - rewrite nth_error_app2 by (rewrite L8; lia).
      replace (8 * S i' + j - length (le8 w))%nat with (8 * i' + j)%nat by (rewrite L8; lia).
      apply IH; assumption. }
  assert (IL : (i < length ws)%nat) by (apply nth_error_Some; congruence).
  unfold bytes_at in BA. unfold wr_at in WR. rewrite u64s_length in BA.
  destruct BA as (BA0 & BA1 & BA2). destruct WR as (WR0 & WR1 & WR2).
  unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize]. rewrite app_nil_r.
  split; [split; [tauto |] |].
  - unfold bytes_at. rewrite L8. split; [lia | split; [lia |]].
    intros j J. replace (A + 8 * Z.of_nat i + Z.of_nat j) with (A + Z.of_nat (8 * i + j)) by lia.
    rewrite BA2 by lia. apply NS; assumption.
  - unfold wr_at. split; [lia | split; [lia |]].
    intros j J. replace (A + 8 * Z.of_nat i + j) with (A + (8 * Z.of_nat i + j)) by lia. apply WR2. lia.
Qed.

  Lemma z4_lxor_ones : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 2^64 - 1 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec.
  destruct (Z_lt_le_dec i 64) as [IL | IL].
  - rewrite Z.ones_spec_low by lia. rewrite Bool.xorb_true_r.
    replace (2^64 - 1 - x) with (Z.lnot x + 1 * 2^64) by (pose proof (Z.add_lnot_diag x); lia).
    rewrite <- (Z.mod_pow2_bits_low (Z.lnot x + 1 * 2^64) 64 i) by lia. rewrite Z.mod_add by lia.
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia.
    assert (T1 : Z.testbit x i = false)
      by (rewrite <- (Z.mod_small x (2^64)) by lia; apply Z.mod_pow2_bits_high; lia).
    assert (T2 : Z.testbit (2^64 - 1 - x) i = false)
      by (rewrite <- (Z.mod_small (2^64 - 1 - x) (2^64)) by lia; apply Z.mod_pow2_bits_high; lia).
    rewrite T1, T2. reflexivity.
Qed.

  
  Lemma z4_dbc_rd : forall m1, mem_inv bsegs m1 ->
    ov_read_bytes bsegs m1 (Z_to_bv 64 0x103b0) 8 = Some (le8 (Z_to_bv 64 AZ4_DBC)).
Proof.
  intros m1 MI.
  assert (RC : ro_cells bsegs m1 0x103b0 [CB (length (le8 (Z_to_bv 64 AZ4_DBC))) (le8 (Z_to_bv 64 AZ4_DBC))]).
  { apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | vm_compute; congruence]. }
  eapply (ro_cells_read_at bsegs m1 0x103b0 _ 0 (CB (length (le8 (Z_to_bv 64 AZ4_DBC))) (le8 (Z_to_bv 64 AZ4_DBC))) 8 _ RC);
    reflexivity.
Qed.

  
  Notation STAk k SE OPk pc mm x1 x5 x6 x9 a0 a1 a2 a3 x21 x22 x24 x25 x27 x30 :=
    (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 (Z_to_bv 64 65) (Z_to_bv 64 (DT + 4)) x9 a0 a1 a2 a3
             (Z_to_bv 64 k) (Z_to_bv 64 (SPF + 264)) (Z_to_bv 64 (2^64 - 1 - (DT + 4))) (Z_to_bv 64 9)
             (Z_to_bv 64 (SPF + 176 + 8 * k)) (Z_to_bv 64 OPk) (Z_to_bv 64 SE) x21 x22 (Z_to_bv 64 0x7fff8000) x24 x25
             (Z_to_bv 64 0x20d53) x27 (Z_to_bv 64 2) (Z_to_bv 64 seg) x30 (Z_to_bv 64 64))
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  
  Definition WSOK (ws : list word) (k : Z) : Prop :=
    forall i, k <= i < 4 -> exists ipi opi bi iei, nth_error ws (Z.to_nat i) = Some (Z_to_bv 64 ipi)
      /\ nth_error ws (Z.to_nat (4 + i)) = Some (Z_to_bv 64 opi) /\ nth_error ws (Z.to_nat (8 + i)) = Some (Z_to_bv 64 bi)
      /\ nth_error ws (Z.to_nat (15 + i)) = Some (Z_to_bv 64 iei)
      /\ SS <= ipi /\ ipi + 8 <= SS + n /\ DST <= opi <= DST + dcap /\ 1 <= bi < 2^64 /\ 9 <= iei < 2^64.

  Lemma wsok_upd : forall ws k v, 0 <= k < 4 -> WSOK ws k -> WSOK (upd ws (Z.to_nat (4 + k)) v) (k + 1).
Proof.
  intros ws k v K W i Hi. destruct (W i ltac:(lia)) as (ipi & opi & bi & iei & H1 & H2 & H3 & H4 & R).
  exists ipi, opi, bi, iei. rewrite !nth_error_upd_other by lia. tauto.
Qed.

  Lemma z4f_sx : forall k SE mm ws (x1 x5 x6 x9 x10 x11 x12 x13 x18 x19 x21 x22 x24 x27 x30 : word),
    0 <= k < 4 -> DST + k * seg < SE <= DST + dcap ->
    Z4M mm (Z_to_bv 64 AZ4_TB) ws -> nth_error ws 13 = Some (Z_to_bv 64 SS) -> WSOK ws k ->
    (forall mm' ws' (y1 y5 y6 y9 y10 y11 y12 y13 y18 y19 y21 y22 y24 y25 y27 y30 : word),
       k + 1 < 4 -> Z4M mm' (Z_to_bv 64 AZ4_TB) ws' -> nth_error ws' 13 = Some (Z_to_bv 64 SS) -> WSOK ws' (k + 1) ->
       evtF bsegs RNG POST (KH 0x86b50 mm' (k + 1) SE y1 y5 y6 y9 y10 y11 y12 y13 y18 y19 y21 y22 y24 y25 y27 y30)) ->
    evtF bsegs RNG POST (KH 0x86b74 mm k (DST + k * seg) x1 x5 x6 x9 x10 x11 x12 x13 x18 x19 x21 x22 x24 (Z_to_bv 64 SE) x27 x30).
Proof using All.
  intros k SE mm ws x1 x5 x6 x9 x10 x11 x12 x13 x18 x19 x21 x22 x24 x27 x30 K4 HSE HZ W13 WS IH.
  pose proof (ZF z4f_frame_facts) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  pose proof (ZF z4f_blocks) as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
  destruct (WS k ltac:(lia)) as (ip & op & bw & ie & WIP & WOP & WBW & WIE & IP1 & IP2 & OP1 & BW1 & IE1).
  pose proof HZ as HZ0. unfold AF_huf_z4m.Z4M in HZ0.
  destruct HZ0 as ((buf & BU & BL) & BS & BT & ST1 & RF0 & ST2 & R128 & U64 & WL & ST3 & RFS & MI & MU & WM).
  unfold AF_huf_z4m.Z4F0 in RF0.
  replace (SPF + 24) with (SP + -504) in RF0 by lia. replace (SPF + 128) with (SP + -400) in R128 by lia.
  assert (DP : 1 <= DST) by (unfold ablk, ABase.AIMG_HI, ABase.KLS in *; lia).
  assert (SS8 : 8 <= SS) by (destruct SBB; unfold ablk, ABase.AIMG_HI, ABase.KLS in *; lia).
  assert (KS : 0 <= k * seg <= 3 * seg) by (clear -K4 DC; nia).
  do 3 zstep.
  rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
  pose proof (u64arr_read bsegs mm (SPF + 144) ws (4 + k) (Z_to_bv 64 op) (wa (SP + -352 + k * 8)) U64
                ltac:(exact WOP) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDO.
  do 2 zstep.
  rewrite bv_ltu_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
  rewrite (Z.mod_small SE) by lia. rewrite (Z.mod_small op) by lia.
  destruct (Z_lt_le_dec SE op) as [OE | OK].
  - rewrite (proj2 (Z.ltb_lt _ _)) by exact OE.
    eapply (ZF z4f_err); exact HZ.
  - rewrite (proj2 (Z.ltb_ge _ _)) by exact OK.
    pose proof (u64arr_read bsegs mm (SPF + 144) ws (15 + k) (Z_to_bv 64 ie) (wa (SP + -264 + k * 8)) U64
                  ltac:(exact WIE) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDE.
    pose proof (u64arr_read bsegs mm (SPF + 144) ws k (Z_to_bv 64 ip) (wa (SP + -384 + k * 8)) U64
                  ltac:(exact WIP) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDI.
    pose proof (u64arr_read bsegs mm (SPF + 144) ws (8 + k) (Z_to_bv 64 bw) (wa (SP + -320 + k * 8)) U64
                  ltac:(exact WBW) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDB.
    do 3 zstep. z4f_br. do 5 zstep.
    rewrite bv_ltu_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
    rewrite (Z.mod_small ip) by lia. rewrite (Z.mod_small (ie + -8)) by lia.
    destruct (Z_lt_le_dec ip (ie + -8)) as [IE8 | IE8].
    + rewrite (proj2 (Z.ltb_lt _ _)) by exact IE8. eapply (ZF z4f_err); exact HZ.
    + rewrite (proj2 (Z.ltb_ge _ _)) by exact IE8.
      zstep. z4f_br.
      replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + k * 8) with (SPF + 176 + 8 * k) by lia.
      change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
      assert (RBW : rw_cells bsegs mm (SPF + 208 + k * 8) [C8 (Z_to_bv 64 bw)]).
      { pose proof (z4_u64arr_cell mm (SPF + 144) ws (Z.to_nat (8 + k)) (Z_to_bv 64 bw) U64 WBW) as C.
        replace (SPF + 144 + 8 * Z.of_nat (Z.to_nat (8 + k))) with (SPF + 208 + k * 8) in C by lia. exact C. }
      assert (RSS : rw_cells bsegs mm (SPF + 248) [C8 (Z_to_bv 64 SS)]).
      { pose proof (z4_u64arr_cell mm (SPF + 144) ws 13 (Z_to_bv 64 SS) U64 W13) as C.
        replace (SPF + 144 + 8 * Z.of_nat 13) with (SPF + 248) in C by lia. exact C. }
      assert (CONT : forall mm' (y1 y5 y6 y9 a0 a1 a2 a3 y21 y22 y24 y25 y27 y30 : word),
         Z4M mm' (Z_to_bv 64 AZ4_TB) (upd ws (Z.to_nat (4 + k)) (Z_to_bv 64 SE)) ->
         evtF bsegs RNG POST (STAk k SE op 0x875d0 mm' y1 y5 y6 y9 a0 a1 a2 a3 y21 y22 y24 y25 y27 y30)).
      { intros mm' y1 y5 y6 y9 a0 a1 a2 a3 y21 y22 y24 y25 y27 y30 HZ'.
        do 3 zstep.
        rewrite bv_eqb_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
        rewrite (Z.mod_small (k + 1)) by lia. rewrite (Z.mod_small 4) by lia.
        destruct (Z.eq_dec (k + 1) 4) as [K3 | K3].
        - rewrite (proj2 (Z.eqb_eq _ _)) by exact K3. cbn [negb].
          zstep. eapply (ZF z4f_done); exact HZ'.
        - rewrite (proj2 (Z.eqb_neq _ _)) by exact K3. cbn [negb].
          replace (SP + -264) with (SPF + 264) by lia.
          change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
          apply (IH mm' (upd ws (Z.to_nat (4 + k)) (Z_to_bv 64 SE))); [lia | exact HZ' | | apply wsok_upd; [lia | exact WS]].
          rewrite nth_error_upd_other by lia. exact W13. }
      eapply (AF_huf_z4kx2.z4_S POST RNG mm FR fc);
        [exact (ZF z4f_ctx mm (Z_to_bv 64 AZ4_TB) ws HZ) | lia | lia | lia | exact RBW | lia | exact RSS | lia | lia | lia | | ].
      * intros ra' s1' a3' t5' s11' HS11 H8.
        eapply (ZF z4f_e5 k SE op (Z_to_bv 64 AZ4_TB) ws K4 ltac:(lia) ltac:(lia) WOP CONT); [exact HZ | lia | lia | exact HS11].
      * intros ra' s1' a3' s8' t5' s11' HS11 H8.
        eapply (ZF z4f_be0 k SE op (Z_to_bv 64 AZ4_TB) ws K4 ltac:(lia) ltac:(lia) WOP CONT); [exact HZ | lia | lia | exact HS11].
Qed.

  
  Lemma z4f_step : forall k mm ws (x1 x5 x6 x9 x10 x11 x12 x13 x18 x19 x21 x22 x24 x25 x27 x30 : word),
    0 <= k < 4 -> Z4M mm (Z_to_bv 64 AZ4_TB) ws -> nth_error ws 13 = Some (Z_to_bv 64 SS) -> WSOK ws k ->
    (forall mm' ws' (y1 y5 y6 y9 y10 y11 y12 y13 y18 y19 y21 y22 y24 y25 y27 y30 : word),
       k + 1 < 4 -> Z4M mm' (Z_to_bv 64 AZ4_TB) ws' -> nth_error ws' 13 = Some (Z_to_bv 64 SS) -> WSOK ws' (k + 1) ->
       evtF bsegs RNG POST (KH 0x86b50 mm' (k + 1) (DST + (k + 1) * seg) y1 y5 y6 y9 y10 y11 y12 y13 y18 y19 y21 y22 y24 y25 y27 y30)) ->
    evtF bsegs RNG POST (KH 0x86b50 mm k (DST + k * seg) x1 x5 x6 x9 x10 x11 x12 x13 x18 x19 x21 x22 x24 x25 x27 x30).
Proof using All.
  intros k mm ws x1 x5 x6 x9 x10 x11 x12 x13 x18 x19 x21 x22 x24 x25 x27 x30 K4 HZ W13 WS IH.
  pose proof (ZF z4f_frame_facts) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  pose proof (ZF z4f_blocks) as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
  pose proof HZ as HZ0. unfold AF_huf_z4m.Z4M in HZ0.
  destruct HZ0 as ((buf & BU & BL) & BS & BT & ST1 & RF0 & ST2 & R128 & U64 & WL & ST3 & RFS & MI & MU & WM).
  unfold AF_huf_z4m.Z4F0 in RF0.
  replace (SPF + 24) with (SP + -504) in RF0 by lia.
  assert (DP : 1 <= DST) by (unfold ablk, ABase.AIMG_HI, ABase.KLS in *; lia).
  do 3 zstep.
  assert (KS : 0 <= k * seg <= 3 * seg) by (clear -K4 DC; nia).
  assert (LA : Z.land (DST + k * seg) 18446744073709551615 = DST + k * seg).
  { change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  rewrite LA.
  replace (DST + dcap - (DST + k * seg)) with (dcap - k * seg) by lia.
  destruct (Z_le_gt_dec seg (dcap - k * seg)) as [NC | CL].
  - z4f_br. zstep. zstep. z4f_br. do 4 zstep. z4f_br. rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent. z4f_br.
    replace (SP + -264) with (SPF + 264) by lia.
    change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
    eapply (z4f_sx k (seg + (DST + k * seg))); [lia | lia | exact HZ | exact W13 | exact WS | ].
    intros mm' ws' y1 y5 y6 y9 y10 y11 y12 y13 y18 y19 y21 y22 y24 y25 y27 y30 HK HZ' W13' WS'.
    replace (seg + (DST + k * seg)) with (DST + (k + 1) * seg) by ring.
    apply (IH mm' ws'); assumption.
  - z4f_br.
    replace (SP + -264) with (SPF + 264) by lia.
    change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
    eapply (z4f_sx k (DST + dcap)); [lia | lia | exact HZ | exact W13 | exact WS | ].
    intros mm' ws' y1 y5 y6 y9 y10 y11 y12 y13 y18 y19 y21 y22 y24 y25 y27 y30 HK.
    assert (k * seg <= 2 * seg) by (clear -K4 DC HK; nia). lia.
Qed.

  
  Lemma z4f_kloop : forall (j : nat) k mm ws (x1 x5 x6 x9 x10 x11 x12 x13 x18 x19 x21 x22 x24 x25 x27 x30 : word),
    Z.of_nat j = 4 - k -> 0 <= k < 4 ->
    Z4M mm (Z_to_bv 64 AZ4_TB) ws -> nth_error ws 13 = Some (Z_to_bv 64 SS) -> WSOK ws k ->
    evtF bsegs RNG POST (KH 0x86b50 mm k (DST + k * seg) x1 x5 x6 x9 x10 x11 x12 x13 x18 x19 x21 x22 x24 x25 x27 x30).
Proof using All.
  induction j as [|j IH]; intros k mm ws x1 x5 x6 x9 x10 x11 x12 x13 x18 x19 x21 x22 x24 x25 x27 x30 HJ K4 HZ W13 WS; [lia|].
  eapply z4f_step; [exact K4 | exact HZ | exact W13 | exact WS |].
  intros mm' ws' y1 y5 y6 y9 y10 y11 y12 y13 y18 y19 y21 y22 y24 y25 y27 y30 HK HZ' W13' WS'.
  eapply IH; [lia | lia | exact HZ' | exact W13' | exact WS'].
Qed.

  
  Notation HOA pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
             (Z_to_bv 64 0x7fff8000) x24 x25 (Z_to_bv 64 0x20d53) x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  
  
  Lemma z4f_fin : forall mm ws (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31 : word),
    Z4M mm (Z_to_bv 64 AZ4_TB) ws -> nth_error ws 13 = Some (Z_to_bv 64 SS) -> WSOK ws 0 ->
    evtF bsegs RNG POST (HOA 0x86b18 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31).
Proof using All.
  intros mm ws x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31 HZ W13 WS.
  pose proof (ZF z4f_frame_facts) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  pose proof (ZF z4f_blocks) as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
  pose proof (ZF z4f_dtl) as DTL8.
  pose proof HZ as HZ0. unfold AF_huf_z4m.Z4M in HZ0.
  destruct HZ0 as ((buf & BU & BL) & BS & BT & ST1 & RF0 & ST2 & R128 & U64 & WL & ST3 & RFS & MI & MU & WM).
  unfold AF_huf_z4m.Z4F0 in RF0.
  replace (SPF + 24) with (SP + -504) in RF0 by lia. replace (SPF + 128) with (SP + -400) in R128 by lia.
  unfold AZ4_TB in R128. pose proof (z4_dbc_rd mm MI) as RDB.
  do 14 zstep.
  rewrite z4_lxor_ones by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^2) with 4.
  replace (SP + -264) with (SPF + 264) by lia.
  replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0 * seg)) by (f_equal; lia).
  eapply (z4f_kloop 4 0); [reflexivity | lia | exact HZ | exact W13 | exact WS].
Qed.

End Z4FIN.
End CANSEC1.
