(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.cks Require Import CkTables CkModel CkMathCrc CkWalk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.CkA Require Import CrcAGlue CrcAMirror.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.CkB Require Import CkBImg CkBTables CkBShadow CkBIface CkBKit CrcBGlue CrcBMirror CrcB_zkit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= crcz_acc_hint.

Section P.
  Variables (RNG : footprint)
            (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo A : Z) (bs : list Z).
  Hypothesis LOS : lo <= bv_unsigned sp - 144.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis CKSH : ck_sh m.
  Hypothesis BUF : ck_buf RNG m A bs.
  Hypothesis A1 : 1 <= A.
  Hypothesis ALO : A + Z.of_nat (length bs) <= lo.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).

  Notation SP := (bv_unsigned sp).
  Notation LEN := (Z.of_nat (length bs)).

  Section B.
    Variables (v0 wa2 ws6 : word) (ib cnt x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 : Z).
    Hypothesis Hib : 0 <= ib.
    Hypothesis Hl : ib + 20 <= LEN.
    Hypothesis Hal : (A + ib) mod 4 = 0.
    Hypothesis Rc : 1 <= cnt < 2^64.
    Hypothesis R0 : 0 <= x0 < 2^64.
    Hypothesis R1 : 0 <= x1 < 2^64.
    Hypothesis R2 : 0 <= x2 < 2^64.
    Hypothesis R3 : 0 <= x3 < 2^64.
    Hypothesis R4 : 0 <= x4 < 2^64.
    Hypothesis RY0 : 0 <= y0 < 2^64.
    Hypothesis RY1 : 0 <= y1 < 2^64.
    Hypothesis RY2 : 0 <= y2 < 2^64.
    Hypothesis RY3 : 0 <= y3 < 2^64.
    Hypothesis RY4 : 0 <= y4 < 2^64.

    Notation INVB mm v24 v32 := (crcz_invb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs v0 (Z_to_bv 64 135136) (Z_to_bv 64 0) v24 v32 m mm).

    Lemma b_wk : forall off, off = 0 \/ off = 4 \/ off = 8 \/ off = 12 \/ off = 16 ->
      A <= A + ib + off /\ A + ib + off + 4 <= A + LEN /\ 1 <= 4 /\ (A + ib + off) mod 8 + 4 <= 8.
    Proof. intros off H. repeat split; try lia; Z.div_mod_to_equations; lia. Qed.

    Lemma b_rw : forall mm v24 v32 off, INVB mm v24 v32 -> 0 <= off <= 16 ->
      ov_read_bytes asegs mm (Z_to_bv 64 (A + ib + off)) 4 = Some (le4 (Z_to_bv 64 (wdp bs (ib + off)))).
    Proof.
      intros mm v24 v32 off HINV H. destruct HINV as (_ & _ & _ & _ & _ & BY). destruct BUF as (_ & BF & _).
      apply (ck_buf_read4 mm A bs (ib + off) _ BY BF); [lia | lia | unfold wa; f_equal; lia].
    Qed.

    Lemma b_ar : forall off, 0 <= off <= 20 -> 0 <= A + ib + off < 2 ^ 64.
    Proof. intros off H. pose proof KLO as K. unfold KHIGH in K. pose_sp_range sp. lia. Qed.

    Lemma b_guard : forall k, 0 < k <= 64 -> bv_ltu (Z_to_bv 64 (- k)) (Z_to_bv 64 (A + ib)) = false.
    Proof.
      intros k Hk. apply guard_bltu_neg; [lia| lia|].
      pose proof KLO as K. unfold KHIGH in K. pose_sp_range sp. lia.
    Qed.

    Ltac bw_ck a WK UNP MU WA :=
      let b := fresh "b" in let RD := fresh "RD" in let CK := fresh "CK" in let SR := fresh "SR" in
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        destruct (unpoisoned_check_mu _ lo m mm A (A + LEN) a 4 UNP MU WA ALO KLO
                    (proj1 WK) (proj1 (proj2 WK)) (proj1 (proj2 (proj2 WK))) (proj2 (proj2 (proj2 WK)))) as (b & RD & CK & SR)
      end.
    Ltac z3 := zstep; zstep; zstep; rewrite sxb_sval.
    Ltac z4 := zstep; zstep; zstep; zstep; rewrite sxb_sval.

    Ltac b_join U OK :=
      zstep; lazymatch goal with CK : sval _ = 0 \/ _ |- _ => ck_fast U OK CK; clear CK end.

    Ltac b_dead G := zstep; zstep; apply (evtF_if_false _ _ _ _ _ _ _ _ _ _ _ G).

    Ltac b_word BF :=
      lazymatch goal with |- context [sx32 (Z_to_bv 64 (wdp bs ?j))] => rewrite (sx32_sxz (wdp bs j) (wdp_range64 bs j BF)) end.

    Ltac b_tabv :=
      lazymatch goal with |- context [sx32 (Z_to_bv 64 (btab ?k ?j))] => rewrite (sx32_sxz (btab k j) (btab_range64 k j)) end.

    Ltac btab_site r k idx ALEM KR IR MU WA MI TLB :=
      setreg r (Z_to_bv 64 (136416 + 4 * (256 * k + idx))) ltac:(f_equal; symmetry; apply ALEM);
      let SX := fresh "SX" in let TR := fresh "TR" in let HI := fresh "HI" in
      pose proof (sxz_range (btab k idx)) as SX; pose proof (braid_addr_range k idx KR IR) as TR; pose proof IR as HI;
      let b2 := fresh "b" in let RD2 := fresh "RD" in let CK2 := fresh "CK" in let SR2 := fresh "SR" in let RDT := fresh "RDT" in
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        destruct (tab_check_mu _ lo m mm 136416 1024 (256 * k + idx) (btab_unpoisoned m CKSH) MU WA TLB KLO eq_refl
                    (braid_idx_range k idx KR IR)) as (b2 & RD2 & CK2 & SR2);
        pose proof (btab_read mm k idx (Z_to_bv 64 (136416 + 4 * (256 * k + idx))) MI KR IR (braid_wa k idx)) as RDT
      end.

    Ltac b_done := apply evtF_done; repeat eexists.

    Lemma braid_addrB3' : forall y, 139488 + ((y mod 4294967296) ≫ 24) ≪ 2 = 136416 + 4 * (256 * 3 + bI3 y).
    Proof. intros y. unfold bI3. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. lia. Qed.

    Definition bseg1_post (mm : amem) : machine_state -> Prop := fun ms' => exists (q_ra q_t0 q_s0 q_s1 q_a0 q_a4 q_s2 q_s7 q_s8 q_s9 q_s10 q_s11 : word),
      ms' = (MS (mkR q_ra (Z_to_bv 64 (SP + -144)) gp tp q_t0 (Z_to_bv 64 (sxz (wdp bs ib))) (Z_to_bv 64 (cnt)) q_s0 q_s1 q_a0 (Z_to_bv 64 (A + ib)) wa2 (Z_to_bv 64 (A + ib)) q_a4 (Z_to_bv 64 (x0)) (Z_to_bv 64 (x4)) (Z_to_bv 64 2147450880) q_s2 (Z_to_bv 64 136416) (Z_to_bv 64 (x2)) (Z_to_bv 64 (x1)) ws6 q_s7 q_s8 q_s9 q_s10 q_s11 (Z_to_bv 64 (sxz (wdp bs (ib + 4)))) (Z_to_bv 64 (x3)) (Z_to_bv 64 (sxz (wdp bs (ib + 8)))) (Z_to_bv 64 (sxz (wdp bs (ib + 12))))) F (Z_to_bv 64 0x80a98) fc None mm (seg_rom asegs)).
    Lemma bseg1 : forall (mm : amem) (v24 v32 : word) (p_ra p_t0 p_t1 p_s0 p_s1 p_a0 p_a4 p_s2 p_s7 p_s8 p_s9 p_s10 p_s11 p_t3 p_t5 p_t6 : word), INVB mm v24 v32 ->
      evtF asegs RNG (bseg1_post mm)
        (MS (mkR p_ra (Z_to_bv 64 (SP + -144)) gp tp p_t0 p_t1 (Z_to_bv 64 (cnt)) p_s0 p_s1 p_a0 (Z_to_bv 64 (A + ib)) wa2 (Z_to_bv 64 (A + ib)) p_a4 (Z_to_bv 64 (x0)) (Z_to_bv 64 (x4)) (Z_to_bv 64 2147450880) p_s2 (Z_to_bv 64 136416) (Z_to_bv 64 (x2)) (Z_to_bv 64 (x1)) ws6 p_s7 p_s8 p_s9 p_s10 p_s11 p_t3 (Z_to_bv 64 (x3)) p_t5 p_t6) F (Z_to_bv 64 0x809f8) fc None mm (seg_rom asegs)).
    Proof.
      intros mm v24 v32 p_ra p_t0 p_t1 p_s0 p_s1 p_a0 p_a4 p_s2 p_s7 p_s8 p_s9 p_s10 p_s11 p_t3 p_t5 p_t6 HINV.
      pose proof HINV as (FR & ST & MU & WM & MI & BY). unfold crcz_frameb in FR.
      pose proof BUF as (BY0 & BF & UNP & RB & RSH).
      pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
      assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      assert (WA : wabove [(SP - 144, SP)] lo) by (cbn; lia).
      pose proof (btab_shrng RNG RISH) as RSHT. unfold ABRAID in RSHT.
      assert (TLB : 136416 + 4 * 1024 <= lo) by lia.
      pose_zr_lits. pose proof (zb_length bs) as ZBL.
      pose proof (b_wk 0 ltac:(lia)) as WK0. rewrite !Z.add_0_r in WK0.
      pose proof (b_wk 4 ltac:(lia)) as WK1. pose proof (b_wk 8 ltac:(lia)) as WK2.
      pose proof (b_wk 12 ltac:(lia)) as WK3. pose proof (b_wk 16 ltac:(lia)) as WK4.
      pose proof (b_rw mm v24 v32 0 HINV ltac:(lia)) as RW0. rewrite !Z.add_0_r in RW0.
      pose proof (b_rw mm v24 v32 4 HINV ltac:(lia)) as RW1. pose proof (b_rw mm v24 v32 8 HINV ltac:(lia)) as RW2.
      pose proof (b_rw mm v24 v32 12 HINV ltac:(lia)) as RW3.
      pose proof (b_ar 0 ltac:(lia)) as AR0. rewrite Z.add_0_r in AR0.
      pose proof (b_ar 4 ltac:(lia)) as AR1. pose proof (b_ar 8 ltac:(lia)) as AR2.
      pose proof (b_ar 12 ltac:(lia)) as AR3. pose proof (b_ar 16 ltac:(lia)) as AR4.
      pose proof (sxz_range (wdp bs ib)) as SW0. pose proof (sxz_range (wdp bs (ib + 4))) as SW1.
      pose proof (sxz_range (wdp bs (ib + 8))) as SW2. pose proof (sxz_range (wdp bs (ib + 12))) as SW3.
      pose proof (b_guard 5 ltac:(lia)) as G5. pose proof (b_guard 9 ltac:(lia)) as G9. pose proof (b_guard 13 ltac:(lia)) as G13.
      pose proof (b_guard 17 ltac:(lia)) as G17. pose proof (b_guard 21 ltac:(lia)) as G21.
      zstep. zstep. apply evtF_if_false; [reflexivity|].
      bw_ck (A + ib) WK0 UNP MU WA. z3. b_join 14 0x80a10.
      b_dead G5.
      bw_ck (A + ib + 4) WK1 UNP MU WA. z4. zstep. b_word BF. b_join 28 0x80a30.
      b_dead G9.
      bw_ck (A + ib + 8) WK2 UNP MU WA. z4. zstep. b_word BF. b_join 30 0x80a50.
      b_dead G13.
      bw_ck (A + ib + 12) WK3 UNP MU WA. z4. zstep. b_word BF. b_join 31 0x80a70.
      b_dead G17. b_dead G21.
      bw_ck (A + ib + 16) WK4 UNP MU WA. z4. zstep. b_word BF. b_join 8 0x80a98.
      b_done.
    Qed.

    Definition bseg2_post (mm : amem) : machine_state -> Prop := fun ms' => exists (q_ra q_t0 q_s0 q_s1 q_a0 q_a5 q_a6 q_s2 q_s5 q_t5 q_t6 : word),
      ms' = (MS (mkR q_ra (Z_to_bv 64 (SP + -144)) gp tp q_t0 (Z_to_bv 64 (sxz (btab 0 (bI0 (dY0 (wdp bs (ib + 12)) x3))))) (Z_to_bv 64 (cnt)) q_s0 q_s1 q_a0 (Z_to_bv 64 (A + ib)) wa2 (Z_to_bv 64 (A + ib)) (Z_to_bv 64 (136416 + 4 * (256 * 0 + bI0 (dY0 (wdp bs (ib + 16)) x4)))) q_a5 q_a6 (Z_to_bv 64 2147450880) q_s2 (Z_to_bv 64 136416) (Z_to_bv 64 (sxz (btab 0 (bI0 (dY0 (wdp bs (ib + 4)) x1))))) q_s5 ws6 (Z_to_bv 64 ((dY0 (wdp bs (ib + 16)) x4))) (Z_to_bv 64 ((dY0 (wdp bs (ib + 12)) x3))) (Z_to_bv 64 ((dY0 (wdp bs (ib + 8)) x2))) (Z_to_bv 64 ((dY0 (wdp bs (ib + 4)) x1))) (Z_to_bv 64 ((dY0 (wdp bs ib) x0))) (Z_to_bv 64 (sxz (btab 0 (bI0 (dY0 (wdp bs ib) x0))))) (Z_to_bv 64 (sxz (btab 0 (bI0 (dY0 (wdp bs (ib + 8)) x2))))) q_t5 q_t6) F (Z_to_bv 64 0x80b4c) fc None mm (seg_rom asegs)).
    Lemma bseg2 : forall (mm : amem) (v24 v32 : word) (p_ra p_t0 p_s0 p_s1 p_a0 p_a4 p_s2 p_s7 p_s8 p_s9 p_s10 p_s11 : word), INVB mm v24 v32 ->
      evtF asegs RNG (bseg2_post mm)
        (MS (mkR p_ra (Z_to_bv 64 (SP + -144)) gp tp p_t0 (Z_to_bv 64 (sxz (wdp bs ib))) (Z_to_bv 64 (cnt)) p_s0 p_s1 p_a0 (Z_to_bv 64 (A + ib)) wa2 (Z_to_bv 64 (A + ib)) p_a4 (Z_to_bv 64 (x0)) (Z_to_bv 64 (x4)) (Z_to_bv 64 2147450880) p_s2 (Z_to_bv 64 136416) (Z_to_bv 64 (x2)) (Z_to_bv 64 (x1)) ws6 p_s7 p_s8 p_s9 p_s10 p_s11 (Z_to_bv 64 (sxz (wdp bs (ib + 4)))) (Z_to_bv 64 (x3)) (Z_to_bv 64 (sxz (wdp bs (ib + 8)))) (Z_to_bv 64 (sxz (wdp bs (ib + 12))))) F (Z_to_bv 64 0x80a98) fc None mm (seg_rom asegs)).
    Proof.
      intros mm v24 v32 p_ra p_t0 p_s0 p_s1 p_a0 p_a4 p_s2 p_s7 p_s8 p_s9 p_s10 p_s11 HINV.
      pose proof HINV as (FR & ST & MU & WM & MI & BY). unfold crcz_frameb in FR.
      pose proof BUF as (BY0 & BF & UNP & RB & RSH).
      pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
      assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      assert (WA : wabove [(SP - 144, SP)] lo) by (cbn; lia).
      pose proof (btab_shrng RNG RISH) as RSHT. unfold ABRAID in RSHT.
      assert (TLB : 136416 + 4 * 1024 <= lo) by lia.
      pose_zr_lits. pose proof (zb_length bs) as ZBL.
      pose proof (b_rw mm v24 v32 16 HINV ltac:(lia)) as RW4.
      pose proof (sxz_range (wdp bs (ib + 16))) as SW4.
      pose proof (sxz_range (wdp bs ib)) as SW0. pose proof (sxz_range (wdp bs (ib + 4))) as SW1.
      pose proof (sxz_range (wdp bs (ib + 8))) as SW2. pose proof (sxz_range (wdp bs (ib + 12))) as SW3.
      pose proof (dY0_range (wdp bs ib) x0 R0) as DY0. pose proof (dY0_range (wdp bs (ib + 4)) x1 R1) as DY1.
      pose proof (dY0_range (wdp bs (ib + 8)) x2 R2) as DY2. pose proof (dY0_range (wdp bs (ib + 12)) x3 R3) as DY3.
      pose proof (dY0_range (wdp bs (ib + 16)) x4 R4) as DY4.
      zstep. rewrite <- (dY0_unfold (wdp bs ib) x0). zstep. zstep. zstep.
      btab_site 14 0 (bI0 (dY0 (wdp bs ib) x0)) (braid_addrB0 (dY0 (wdp bs ib) x0)) k0_range (bI0_range (dY0 (wdp bs ib) x0)) MU WA MI TLB.
      z3. zstep. b_word BF. b_join 15 0x80abc.
      zstep. rewrite <- (dY0_unfold (wdp bs (ib + 4)) x1). zstep. zstep. zstep.
      btab_site 15 0 (bI0 (dY0 (wdp bs (ib + 4)) x1)) (braid_addrB0 (dY0 (wdp bs (ib + 4)) x1)) k0_range (bI0_range (dY0 (wdp bs (ib + 4)) x1)) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 14 0x80ae0.
      zstep. rewrite <- (dY0_unfold (wdp bs (ib + 8)) x2). zstep. zstep. zstep.
      btab_site 14 0 (bI0 (dY0 (wdp bs (ib + 8)) x2)) (braid_addrB0 (dY0 (wdp bs (ib + 8)) x2)) k0_range (bI0_range (dY0 (wdp bs (ib + 8)) x2)) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 15 0x80b04.
      zstep. rewrite <- (dY0_unfold (wdp bs (ib + 12)) x3). zstep. zstep. zstep.
      btab_site 15 0 (bI0 (dY0 (wdp bs (ib + 12)) x3)) (braid_addrB0 (dY0 (wdp bs (ib + 12)) x3)) k0_range (bI0_range (dY0 (wdp bs (ib + 12)) x3)) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 14 0x80b28.
      zstep. rewrite <- (dY0_unfold (wdp bs (ib + 16)) x4). zstep. zstep. zstep.
      btab_site 14 0 (bI0 (dY0 (wdp bs (ib + 16)) x4)) (braid_addrB0 (dY0 (wdp bs (ib + 16)) x4)) k0_range (bI0_range (dY0 (wdp bs (ib + 16)) x4)) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 15 0x80b4c.
      b_done.
    Qed.

    Definition bseg3_post (mm : amem) : machine_state -> Prop := fun ms' => exists (q_ra q_a0 q_a5 q_a6 q_s2 q_s5 : word),
      ms' = (MS (mkR q_ra (Z_to_bv 64 (SP + -144)) gp tp (Z_to_bv 64 (sxz (btab 1 (bI1 y3)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y3)))) (Z_to_bv 64 (cnt)) (Z_to_bv 64 (sxz (btab 1 (bI1 y1)))) (Z_to_bv 64 (sxz (btab 1 (bI1 y2)))) q_a0 (Z_to_bv 64 (A + ib)) wa2 (Z_to_bv 64 (A + ib)) (Z_to_bv 64 (136416 + 4 * (256 * 1 + bI1 y4))) q_a5 q_a6 (Z_to_bv 64 2147450880) q_s2 (Z_to_bv 64 136416) (Z_to_bv 64 (sxz (btab 0 (bI0 y1)))) q_s5 ws6 (Z_to_bv 64 (y4)) (Z_to_bv 64 (y3)) (Z_to_bv 64 (y2)) (Z_to_bv 64 (y1)) (Z_to_bv 64 (y0)) (Z_to_bv 64 (sxz (btab 0 (bI0 y0)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y2)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y4)))) (Z_to_bv 64 (sxz (btab 1 (bI1 y0))))) F (Z_to_bv 64 0x80c00) fc None mm (seg_rom asegs)).
    Lemma bseg3 : forall (mm : amem) (v24 v32 : word) (p_ra p_t0 p_s0 p_s1 p_a0 p_a5 p_a6 p_s2 p_s5 p_t5 p_t6 : word), INVB mm v24 v32 ->
      evtF asegs RNG (bseg3_post mm)
        (MS (mkR p_ra (Z_to_bv 64 (SP + -144)) gp tp p_t0 (Z_to_bv 64 (sxz (btab 0 (bI0 y3)))) (Z_to_bv 64 (cnt)) p_s0 p_s1 p_a0 (Z_to_bv 64 (A + ib)) wa2 (Z_to_bv 64 (A + ib)) (Z_to_bv 64 (136416 + 4 * (256 * 0 + bI0 y4))) p_a5 p_a6 (Z_to_bv 64 2147450880) p_s2 (Z_to_bv 64 136416) (Z_to_bv 64 (sxz (btab 0 (bI0 y1)))) p_s5 ws6 (Z_to_bv 64 (y4)) (Z_to_bv 64 (y3)) (Z_to_bv 64 (y2)) (Z_to_bv 64 (y1)) (Z_to_bv 64 (y0)) (Z_to_bv 64 (sxz (btab 0 (bI0 y0)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y2)))) p_t5 p_t6) F (Z_to_bv 64 0x80b4c) fc None mm (seg_rom asegs)).
    Proof.
      intros mm v24 v32 p_ra p_t0 p_s0 p_s1 p_a0 p_a5 p_a6 p_s2 p_s5 p_t5 p_t6 HINV.
      pose proof HINV as (FR & ST & MU & WM & MI & BY). unfold crcz_frameb in FR.
      pose proof BUF as (BY0 & BF & UNP & RB & RSH).
      pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
      assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      assert (WA : wabove [(SP - 144, SP)] lo) by (cbn; lia).
      pose proof (btab_shrng RNG RISH) as RSHT. unfold ABRAID in RSHT.
      assert (TLB : 136416 + 4 * 1024 <= lo) by lia.
      pose_zr_lits. pose proof (zb_length bs) as ZBL.
      pose proof (btab_read mm 0 (bI0 y4) _ MI k0_range (bI0_range y4) (braid_wa 0 (bI0 y4))) as RDP. pose proof (bI0_range y4) as HRDP.
      zstep. zstep. zstep. zstep.
      btab_site 15 1 (bI1 y0) (braid_addrB1 y0) k1_range (bI1_range y0) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 14 0x80b70.
      zstep. zstep. zstep. zstep.
      btab_site 14 1 (bI1 y1) (braid_addrB1 y1) k1_range (bI1_range y1) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 15 0x80b94.
      zstep. zstep. zstep. zstep.
      btab_site 15 1 (bI1 y2) (braid_addrB1 y2) k1_range (bI1_range y2) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 14 0x80bb8.
      zstep. zstep. zstep. zstep.
      btab_site 16 1 (bI1 y3) (braid_addrB1 y3) k1_range (bI1_range y3) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 14 0x80bdc.
      zstep. zstep. zstep. zstep.
      btab_site 14 1 (bI1 y4) (braid_addrB1 y4) k1_range (bI1_range y4) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 15 0x80c00.
      b_done.
    Qed.

    Definition bseg4_post : machine_state -> Prop := fun ms' => exists (mm3 : amem) (q_a0 q_a4 : word),
      ms' = (MS (mkR (Z_to_bv 64 (sxz (btab 2 (bI2 y2)))) (Z_to_bv 64 (SP + -144)) gp tp (Z_to_bv 64 (sxz (btab 1 (bI1 y3)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y3)))) (Z_to_bv 64 (cnt)) (Z_to_bv 64 (sxz (btab 1 (bI1 y1)))) (Z_to_bv 64 (sxz (btab 1 (bI1 y2)))) q_a0 (Z_to_bv 64 (A + ib)) wa2 (Z_to_bv 64 (A + ib)) q_a4 (Z_to_bv 64 (136416 + 4 * (256 * 2 + bI2 y4))) (Z_to_bv 64 (sxz (btab 1 (bI1 y0)))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (sxz (btab 1 (bI1 y4)))) (Z_to_bv 64 136416) (Z_to_bv 64 (sxz (btab 0 (bI0 y1)))) (Z_to_bv 64 (sxz (btab 2 (bI2 y3)))) ws6 (Z_to_bv 64 (y4)) (Z_to_bv 64 (y3)) (Z_to_bv 64 (y2)) (Z_to_bv 64 (y1)) (Z_to_bv 64 (y0)) (Z_to_bv 64 (sxz (btab 0 (bI0 y0)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y2)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y4)))) (Z_to_bv 64 (sxz (btab 1 (bI1 y0))))) F (Z_to_bv 64 0x80cd8) fc None mm3 (seg_rom asegs))
      /\ INVB mm3 (Z_to_bv 64 (sxz (btab 2 (bI2 y1)))) (Z_to_bv 64 (sxz (btab 2 (bI2 y0)))).
    Lemma bseg4 : forall (mm : amem) (v24 v32 : word) (p_ra p_a0 p_a5 p_a6 p_s2 p_s5 : word), INVB mm v24 v32 ->
      evtF asegs RNG bseg4_post
        (MS (mkR p_ra (Z_to_bv 64 (SP + -144)) gp tp (Z_to_bv 64 (sxz (btab 1 (bI1 y3)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y3)))) (Z_to_bv 64 (cnt)) (Z_to_bv 64 (sxz (btab 1 (bI1 y1)))) (Z_to_bv 64 (sxz (btab 1 (bI1 y2)))) p_a0 (Z_to_bv 64 (A + ib)) wa2 (Z_to_bv 64 (A + ib)) (Z_to_bv 64 (136416 + 4 * (256 * 1 + bI1 y4))) p_a5 p_a6 (Z_to_bv 64 2147450880) p_s2 (Z_to_bv 64 136416) (Z_to_bv 64 (sxz (btab 0 (bI0 y1)))) p_s5 ws6 (Z_to_bv 64 (y4)) (Z_to_bv 64 (y3)) (Z_to_bv 64 (y2)) (Z_to_bv 64 (y1)) (Z_to_bv 64 (y0)) (Z_to_bv 64 (sxz (btab 0 (bI0 y0)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y2)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y4)))) (Z_to_bv 64 (sxz (btab 1 (bI1 y0))))) F (Z_to_bv 64 0x80c00) fc None mm (seg_rom asegs)).
    Proof.
      intros mm v24 v32 p_ra p_a0 p_a5 p_a6 p_s2 p_s5 HINV.
      pose proof HINV as (FR & ST & MU & WM & MI & BY). unfold crcz_frameb in FR.
      pose proof BUF as (BY0 & BF & UNP & RB & RSH).
      pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
      assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      assert (WA : wabove [(SP - 144, SP)] lo) by (cbn; lia).
      pose proof (btab_shrng RNG RISH) as RSHT. unfold ABRAID in RSHT.
      assert (TLB : 136416 + 4 * 1024 <= lo) by lia.
      pose_zr_lits. pose proof (zb_length bs) as ZBL.
      pose proof (btab_read mm 1 (bI1 y4) _ MI k1_range (bI1_range y4) (braid_wa 1 (bI1 y4))) as RDP. pose proof (bI1_range y4) as HRDP.
      zstep. zstep. zstep. zstep. zstep.
      btab_site 15 2 (bI2 y0) (braid_addrB2 y0) k2_range (bI2_range y0) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 14 0x80c28.
      zstep. zstep. zstep. zstep. zstep.
      btab_site 14 2 (bI2 y1) (braid_addrB2 y1) k2_range (bI2_range y1) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 15 0x80c50.
      zstep. zstep. zstep. zstep. zstep.
      btab_site 15 2 (bI2 y2) (braid_addrB2 y2) k2_range (bI2_range y2) MU WA MI TLB.
      z3. zstep. b_tabv. zstep. b_join 14 0x80c7c.
      zstep. zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mn _) =>
        pose proof (btab_read mn 2 (bI2 y2) _ MI k2_range (bI2_range y2) (braid_wa 2 (bI2 y2))) as RDN end.
      zstep. zstep. zstep. zstep. zstep.
      btab_site 14 2 (bI2 y3) (braid_addrB2 y3) k2_range (bI2_range y3) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 15 0x80cac.
      zstep. zstep. zstep. zstep. zstep. zstep.
      btab_site 15 2 (bI2 y4) (braid_addrB2 y4) k2_range (bI2_range y4) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 14 0x80cd8.
      apply evtF_done. unfold bseg4_post. eexists. do 2 eexists. split; [reflexivity|]. split; [exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact BY].
    Qed.

    Definition bseg5_post (mm : amem) : machine_state -> Prop := fun ms' => exists (q_a0 q_a5 q_t4 : word),
      ms' = (MS (mkR (Z_to_bv 64 (sxz (btab 2 (bI2 y2)))) (Z_to_bv 64 (SP + -144)) gp tp (Z_to_bv 64 (sxz (btab 1 (bI1 y3)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y2)))) (Z_to_bv 64 (cnt)) (Z_to_bv 64 (sxz (btab 1 (bI1 y1)))) (Z_to_bv 64 (sxz (btab 1 (bI1 y2)))) q_a0 (Z_to_bv 64 (A + ib)) wa2 (Z_to_bv 64 (A + ib)) (Z_to_bv 64 (136416 + 4 * (256 * 3 + bI3 y4))) q_a5 (Z_to_bv 64 (sxz (btab 1 (bI1 y0)))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (sxz (btab 1 (bI1 y4)))) (Z_to_bv 64 136416) (Z_to_bv 64 (sxz (btab 0 (bI0 y1)))) (Z_to_bv 64 (sxz (btab 2 (bI2 y3)))) ws6 (Z_to_bv 64 (sxz (btab 3 (bI3 y3)))) (Z_to_bv 64 (sxz (btab 3 (bI3 y2)))) (Z_to_bv 64 (sxz (btab 3 (bI3 y1)))) (Z_to_bv 64 (sxz (btab 3 (bI3 y0)))) (Z_to_bv 64 (sxz (btab 2 (bI2 y4)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y0)))) q_t4 (Z_to_bv 64 (sxz (btab 0 (bI0 y3)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y4))))) F (Z_to_bv 64 0x80da4) fc None mm (seg_rom asegs)).
    Lemma bseg5 : forall (mm : amem) (p_a0 p_a4 : word), INVB mm (Z_to_bv 64 (sxz (btab 2 (bI2 y1)))) (Z_to_bv 64 (sxz (btab 2 (bI2 y0)))) ->
      evtF asegs RNG (bseg5_post mm)
        (MS (mkR (Z_to_bv 64 (sxz (btab 2 (bI2 y2)))) (Z_to_bv 64 (SP + -144)) gp tp (Z_to_bv 64 (sxz (btab 1 (bI1 y3)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y3)))) (Z_to_bv 64 (cnt)) (Z_to_bv 64 (sxz (btab 1 (bI1 y1)))) (Z_to_bv 64 (sxz (btab 1 (bI1 y2)))) p_a0 (Z_to_bv 64 (A + ib)) wa2 (Z_to_bv 64 (A + ib)) p_a4 (Z_to_bv 64 (136416 + 4 * (256 * 2 + bI2 y4))) (Z_to_bv 64 (sxz (btab 1 (bI1 y0)))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (sxz (btab 1 (bI1 y4)))) (Z_to_bv 64 136416) (Z_to_bv 64 (sxz (btab 0 (bI0 y1)))) (Z_to_bv 64 (sxz (btab 2 (bI2 y3)))) ws6 (Z_to_bv 64 (y4)) (Z_to_bv 64 (y3)) (Z_to_bv 64 (y2)) (Z_to_bv 64 (y1)) (Z_to_bv 64 (y0)) (Z_to_bv 64 (sxz (btab 0 (bI0 y0)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y2)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y4)))) (Z_to_bv 64 (sxz (btab 1 (bI1 y0))))) F (Z_to_bv 64 0x80cd8) fc None mm (seg_rom asegs)).
    Proof.
      intros mm p_a0 p_a4 HINV.
      pose proof HINV as (FR & ST & MU & WM & MI & BY). unfold crcz_frameb in FR.
      pose proof BUF as (BY0 & BF & UNP & RB & RSH).
      pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
      assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      assert (WA : wabove [(SP - 144, SP)] lo) by (cbn; lia).
      pose proof (btab_shrng RNG RISH) as RSHT. unfold ABRAID in RSHT.
      assert (TLB : 136416 + 4 * 1024 <= lo) by lia.
      pose_zr_lits. pose proof (zb_length bs) as ZBL.
      pose proof (btab_read mm 2 (bI2 y4) _ MI k2_range (bI2_range y4) (braid_wa 2 (bI2 y4))) as RDP. pose proof (bI2_range y4) as HRDP.
      zstep. zstep. rewrite srliw24_form. zstep. zstep. zstep. zstep.
      btab_site 14 3 (bI3 y0) (braid_addrB3 y0) k3_range (bI3_range y0) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 15 0x80d04.
      zstep. zstep. rewrite srliw24_form. zstep. zstep. zstep. zstep.
      btab_site 15 3 (bI3 y1) (braid_addrB3 y1) k3_range (bI3_range y1) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 14 0x80d30.
      zstep. zstep. rewrite srliw24_form. zstep. zstep. zstep. zstep.
      btab_site 10 3 (bI3 y2) (braid_addrB3 y2) k3_range (bI3_range y2) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 15 0x80d5c.
      zstep. rewrite srliw24_form. zstep. zstep. zstep. zstep.
      btab_site 15 3 (bI3 y3) (braid_addrB3' y3) k3_range (bI3_range y3) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 10 0x80d84.
      zstep. rewrite srliw24_form. zstep. zstep.
      btab_site 14 3 (bI3 y4) (braid_addrB3' y4) k3_range (bI3_range y4) MU WA MI TLB.
      z3. zstep. b_tabv. b_join 15 0x80da4.
      b_done.
    Qed.

    Definition bseg6_post (mm : amem) : machine_state -> Prop := fun ms' => exists (q_ra q_t0 q_t1 q_s0 q_s1 q_a0 q_a4 q_s7 q_s8 q_s9 q_s10 q_s11 q_t3 q_t5 q_t6 : word),
      ms' = (MS (mkR q_ra (Z_to_bv 64 (SP + -144)) gp tp q_t0 q_t1 (Z_to_bv 64 (cnt + -1)) q_s0 q_s1 q_a0 (Z_to_bv 64 (A + ib + 20)) wa2 (Z_to_bv 64 (A + ib + 20)) q_a4 (Z_to_bv 64 (dLaneM y0)) (Z_to_bv 64 (dLaneM y4)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (135136)) (Z_to_bv 64 136416) (Z_to_bv 64 (dLaneM y2)) (Z_to_bv 64 (dLaneM y1)) ws6 q_s7 q_s8 q_s9 q_s10 q_s11 q_t3 (Z_to_bv 64 (dLaneM y3)) q_t5 q_t6) F (Z_to_bv 64 0x80dfc) fc None mm (seg_rom asegs)).
    Lemma bseg6 : forall (mm : amem) (p_a0 p_a5 p_t4 : word), INVB mm (Z_to_bv 64 (sxz (btab 2 (bI2 y1)))) (Z_to_bv 64 (sxz (btab 2 (bI2 y0)))) ->
      evtF asegs RNG (bseg6_post mm)
        (MS (mkR (Z_to_bv 64 (sxz (btab 2 (bI2 y2)))) (Z_to_bv 64 (SP + -144)) gp tp (Z_to_bv 64 (sxz (btab 1 (bI1 y3)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y2)))) (Z_to_bv 64 (cnt)) (Z_to_bv 64 (sxz (btab 1 (bI1 y1)))) (Z_to_bv 64 (sxz (btab 1 (bI1 y2)))) p_a0 (Z_to_bv 64 (A + ib)) wa2 (Z_to_bv 64 (A + ib)) (Z_to_bv 64 (136416 + 4 * (256 * 3 + bI3 y4))) p_a5 (Z_to_bv 64 (sxz (btab 1 (bI1 y0)))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (sxz (btab 1 (bI1 y4)))) (Z_to_bv 64 136416) (Z_to_bv 64 (sxz (btab 0 (bI0 y1)))) (Z_to_bv 64 (sxz (btab 2 (bI2 y3)))) ws6 (Z_to_bv 64 (sxz (btab 3 (bI3 y3)))) (Z_to_bv 64 (sxz (btab 3 (bI3 y2)))) (Z_to_bv 64 (sxz (btab 3 (bI3 y1)))) (Z_to_bv 64 (sxz (btab 3 (bI3 y0)))) (Z_to_bv 64 (sxz (btab 2 (bI2 y4)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y0)))) p_t4 (Z_to_bv 64 (sxz (btab 0 (bI0 y3)))) (Z_to_bv 64 (sxz (btab 0 (bI0 y4))))) F (Z_to_bv 64 0x80da4) fc None mm (seg_rom asegs)).
    Proof.
      intros mm p_a0 p_a5 p_t4 HINV.
      pose proof HINV as (FR & ST & MU & WM & MI & BY). unfold crcz_frameb in FR.
      pose proof BUF as (BY0 & BF & UNP & RB & RSH).
      pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
      assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      assert (WA : wabove [(SP - 144, SP)] lo) by (cbn; lia).
      pose proof (btab_shrng RNG RISH) as RSHT. unfold ABRAID in RSHT.
      assert (TLB : 136416 + 4 * 1024 <= lo) by lia.
      pose_zr_lits. pose proof (zb_length bs) as ZBL.
      pose proof (btab_read mm 3 (bI3 y4) _ MI k3_range (bI3_range y4) (braid_wa 3 (bI3 y4))) as RDP. pose proof (bI3_range y4) as HRDP.
      pose proof (sxz_range (btab 0 (bI0 y0))) as SX00.
      pose proof (sxz_range (btab 0 (bI0 y1))) as SX01.
      pose proof (sxz_range (btab 0 (bI0 y2))) as SX02.
      pose proof (sxz_range (btab 0 (bI0 y3))) as SX03.
      pose proof (sxz_range (btab 0 (bI0 y4))) as SX04.
      pose proof (sxz_range (btab 1 (bI1 y0))) as SX10.
      pose proof (sxz_range (btab 1 (bI1 y1))) as SX11.
      pose proof (sxz_range (btab 1 (bI1 y2))) as SX12.
      pose proof (sxz_range (btab 1 (bI1 y3))) as SX13.
      pose proof (sxz_range (btab 1 (bI1 y4))) as SX14.
      pose proof (sxz_range (btab 2 (bI2 y0))) as SX20.
      pose proof (sxz_range (btab 2 (bI2 y1))) as SX21.
      pose proof (sxz_range (btab 2 (bI2 y2))) as SX22.
      pose proof (sxz_range (btab 2 (bI2 y3))) as SX23.
      pose proof (sxz_range (btab 2 (bI2 y4))) as SX24.
      pose proof (sxz_range (btab 3 (bI3 y0))) as SX30.
      pose proof (sxz_range (btab 3 (bI3 y1))) as SX31.
      pose proof (sxz_range (btab 3 (bI3 y2))) as SX32.
      pose proof (sxz_range (btab 3 (bI3 y3))) as SX33.
      pose proof (sxz_range (btab 3 (bI3 y4))) as SX34.
      zstep. zstep. zstep. zstep. zstep.
      zstep. b_tabv.
      zstep. zstep.
      zstep. zstep. zstep. zstep.
      zstep. zstep. zstep.
      zstep. zstep. zstep. zstep. zstep.
      zstep. zstep.
      rewrite <- (dLaneM_unfold y0).
      rewrite <- (dLaneM_unfold y1).
      rewrite <- (dLaneM_unfold y2).
      rewrite <- (dLaneM_unfold y3).
      rewrite <- (dLaneM_unfold y4).
      b_done.
    Qed.

  End B.
End P.
