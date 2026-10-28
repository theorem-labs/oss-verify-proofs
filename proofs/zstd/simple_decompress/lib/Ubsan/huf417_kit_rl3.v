(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f huf417_kit_rlk huf417_kit_rl3lo huf417_kit_rl3hi.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41RL3.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation NB1 mm c b pad p st lm := (BDAT mm (SPV + -376) c b pad p st lm).
  Notation NB2 mm c b pad p st lm := (BDAT mm (SPV + -144) c b pad p st lm).
  Notation NB4 mm c b pad p st lm := (BDAT mm (SPV + -224) c b pad p st lm).
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation KBASE mm rest j e1 dl tl rsv S1 n1 b1 S2 n2 b2 S3 n3 b3 S4 n4 b4 :=
    (X41P mm rest /\ mem_inv usegs mm /\ stk usegs mm DST (DST + dcap) /\ bytes_at usegs mm DT dtb /\ huf_nb_ok false dtb tl /\
     SBUF mm S1 n1 b1 /\ SBUF mm S2 n2 b2 /\ SBUF mm S3 n3 b3 /\ SBUF mm S4 n4 b4 /\
     0 <= j /\ 0 <= e1 /\ j + 3 * e1 + 4 <= dcap /\ dl = tl + 256 * rsv /\ 1 <= tl <= 12 /\ 0 <= rsv <= 255).
  Notation WR3 := [(SPV - 184, SPV - 144)].
  Notation WDF := [(DST, DST + dcap); (SPV - 512, SPV - 336); (SPV - 224, SPV - 104)].
  Notation K4608 := (huf417_kit_rlk.K4608 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb).
  Notation K4796 := (huf417_kit_rlk.K4796 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb).
  Notation K5004 := (huf417_kit_rlk.K5004 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb).

  Lemma x41_rl3 : forall rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0,
    K4796 rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 ->
    K5004 rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 ->
    K4608 rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0.
  Proof using CTX DJ3.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 KA KB.
    unfold huf417_kit_rlk.K4608.
    intros mm K1 K2 c1 o1 Q1 c2 o2 Q2 k3 k4 p3 o3 p4 o4 x7 x8 x9 x12 x22 x23 x27 KB0 FA BD1 BD2 BD3 BD4 RS1 RS2 DI3 DI4.
    pose proof KB0 as (PV & MI & OUT & DTB & NBOK & SB1 & SB2 & SB3 & SB4 & HJ & HE & HROOM & HDL & HTL & HRSV).
    pose proof SB3 as (B3 & L3 & R30 & R31 & R32 & D31 & D32).
    pose proof SB4 as (B4 & L4 & R40 & R41 & R42 & D41 & D42).
    assert (N3 : 0 <= n3) by (rewrite <- L3; apply Nat2Z.is_nonneg).
    assert (N4 : 0 <= n4) by (rewrite <- L4; apply Nat2Z.is_nonneg).
    pose proof DI3 as (HP3 & HO3 & HX3).
    pose proof DI4 as (HP4 & HO4 & HX4).
    assert (S4O : S4 + o4 < 2^47) by (destruct HX4 as [HX4 | (HX4 & _)]; lia).
    assert (RLS4 : x41_rls 3 o4 n4 p4)
      by (unfold x41_rls, x41_hinv, RZ_huf_dx41.SINV; destruct HX4 as [HX4 | (HX4 & HX4')]; repeat split; lia).
    destruct (Z_lt_le_dec o3 8) as [LO3 | HI3].
    - assert (RLS3 : x41_rls 3 o3 n3 p3)
        by (unfold x41_rls, x41_hinv, RZ_huf_dx41.SINV; destruct HX3 as [HX3 | (HX3 & HX3')]; repeat split; lia).
      eapply (x41_rl3_lo_w ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm S3 o3 S4 o4);
        [lia | lia | lia | lia | lia | lia | exact MI | exact FA | intros O4 | intros O4].
      + eapply (KA mm K1 K2 k3 c1 o1 Q1 c2 o2 Q2 p3 o3 3 k4 p4 o4 x7 x8 (Z_to_bv 64 3) (Z_to_bv 64 (S4 + 8)) x27 k4).
        all: first [exact KB0 | exact FA | exact BD1 | exact BD2 | exact BD3 | exact BD4 | exact RS1 | exact RS2 | exact RLS3
                   | exact DI4 | exact O4].
      + eapply (KB mm K1 K2 k3 k4 c1 o1 Q1 c2 o2 Q2 p3 o3 3 p4 o4 3 x7 x8 (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (S4 + o4)) x27).
        all: first [exact KB0 | exact FA | exact BD1 | exact BD2 | exact BD3 | exact BD4 | exact RS1 | exact RS2 | exact RLS3
                   | exact RLS4].
    - destruct HX3 as [HX3 | (N3' & HP3')]; [lia|].
      assert (LE : Z.land p3 7 = p3 mod 8)
        by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
      assert (LB : 0 <= Z.land p3 7 <= 7)
        by (rewrite LE; pose proof (Z.mod_pos_bound p3 8 ltac:(lia)); lia).
      assert (DB : 0 <= p3 / 8 <= 7) by (Z.div_mod_to_equations; lia).
      assert (RLS3 : x41_rls 0 (o3 - p3 / 8) n3 (Z.land p3 7))
        by (unfold x41_rls, x41_hinv, RZ_huf_dx41.SINV; repeat split; lia).
      assert (TRB : forall mm', munch WR3 mm mm' -> wmono usegs mm mm' -> mem_inv usegs mm' ->
                 KBASE mm' rest j e1 dl tl rsv S1 n1 b1 S2 n2 b2 S3 n3 b3 S4 n4 b4 /\
                 NB1 mm' K1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) /\
                 NB2 mm' K2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) /\
                 NB4 mm' k4 (Z_to_bv 64 p4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8))).
      { intros mm' MU WM MI'.
        assert (MUF : munch WDF mm mm')
          by (eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia).
        split.
        { split.
          { eapply RZ_huf_dx41f.x41p_transport.
            all: first [exact CTX | exact DJ3 | exact PV | exact MUF | exact WM | exact gp | exact F | exact fc | exact m0]. }
          split; [exact MI'|].
          split; [eapply (stk_transport_disjoint usegs _ mm mm' _ _ OUT MU WM); cbn [disjoint_from]; lia|].
          split; [eapply (bytes_at_transport usegs _ mm mm' DT dtb DTB MU); cbn [disjoint_from]; lia|].
          split; [exact NBOK|].
          split. { eapply RZ_huf_dx41f.sbuf_transport.
            all: first [exact CTX | exact DJ3 | exact SB1 | exact MUF | exact gp | exact F | exact fc | exact m0]. }
          split. { eapply RZ_huf_dx41f.sbuf_transport.
            all: first [exact CTX | exact DJ3 | exact SB2 | exact MUF | exact gp | exact F | exact fc | exact m0]. }
          split. { eapply RZ_huf_dx41f.sbuf_transport.
            all: first [exact CTX | exact DJ3 | exact SB3 | exact MUF | exact gp | exact F | exact fc | exact m0]. }
          split. { eapply RZ_huf_dx41f.sbuf_transport.
            all: first [exact CTX | exact DJ3 | exact SB4 | exact MUF | exact gp | exact F | exact fc | exact m0]. }
          repeat split; lia. }
        split; [eapply (rw_cells_transport usegs _ mm mm' _ _ BD1 MU WM);
                cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
        split; [eapply (rw_cells_transport usegs _ mm mm' _ _ BD2 MU WM);
                cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
        eapply (rw_cells_transport usegs _ mm mm' _ _ BD4 MU WM);
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
      eapply (x41_rl3_hi_w ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX
                mm S3 n3 b3 o3 p3 S4 o4 k3 pad3);
        [lia | lia | lia | lia | lia | lia | exact MI | exact FA | exact BD3 | exact SB3 | | ].
      + intros mm' c y7 y8 y27 O4 MU WM MI' FA' BD3'.
        destruct (TRB mm' MU WM MI') as (KB' & BD1' & BD2' & BD4').
        eapply (KA mm' K1 K2 c c1 o1 Q1 c2 o2 Q2 (Z.land p3 7) (o3 - p3 / 8) 0 k4 p4 o4 y7 y8 (Z_to_bv 64 3) (Z_to_bv 64 (S4 + 8)) y27 k4).
        all: first [exact KB' | exact FA' | exact BD1' | exact BD2' | exact BD3' | exact BD4' | exact RS1 | exact RS2 | exact RLS3
                   | exact DI4 | exact O4].
      + intros mm' c y7 y8 y27 O4 MU WM MI' FA' BD3'.
        destruct (TRB mm' MU WM MI') as (KB' & BD1' & BD2' & BD4').
        eapply (KB mm' K1 K2 c k4 c1 o1 Q1 c2 o2 Q2 (Z.land p3 7) (o3 - p3 / 8) 0 p4 o4 3 y7 y8 (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (S4 + o4)) y27).
        all: first [exact KB' | exact FA' | exact BD1' | exact BD2' | exact BD3' | exact BD4' | exact RS1 | exact RS2 | exact RLS3
                   | exact RLS4].
  Qed.
End DX41RL3.
