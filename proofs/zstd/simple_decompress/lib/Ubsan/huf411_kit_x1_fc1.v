(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require FseNCountRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_kit RZ_hft_bdt_defs RZ_hft_x1_kit huf411_kit_x1_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section X1.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV n DT WK wksz lo : Z).
  Hypothesis LO0 : 4096 <= lo.  Hypothesis LOS : lo <= SPV - HUF_TBL_STACK.  Hypothesis SPR : SPV < 2^47.  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis NR : n < 2^32.
  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + HUF_DTABLE_BYTES < 2^47.  Hypothesis DTAL : DT mod 4 = 0.
  Hypothesis WKL : 4096 <= WK.  Hypothesis WKSZ : 0 <= wksz < 2^32.  Hypothesis WKH : WK + wksz < 2^47.  Hypothesis WKAL : WK mod 4 = 0.
  Hypothesis OFFDT : DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT.  Hypothesis OFFWK : WK + wksz <= lo \/ SPV <= WK.
  Hypothesis DTWK : DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT.
  Hypothesis WK1492 : 1492 <= wksz.

  Notation POST := (huf_rd_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo false m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -240)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Variables (flags : word) (f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f104 f112 f120 : list byte).
  Variables (hw rank : list Z) (nbs tl r0 : Z).
  Hypothesis TLR : 1 <= tl <= 12.  Hypothesis R0R : 1 <= r0 <= n.  Hypothesis HWLEN : Z.of_nat (length hw) = 256.  Hypothesis RKLEN : Z.of_nat (length rank) = 13.
  Notation X1S fl wn wt dt rst syb m1 := (x1s DT WK wksz SPV lo m SAVED hw rank fl wn wt dt rst syb m1).
  Notation FLF cur sym c104 c112 :=
    [C8 (Z_to_bv 64 876); C8 flags; CB 8 f16; C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 ux1_K32); C8 (Z_to_bv 64 (DT + 20));
     C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (tl + 1)); C8 (Z_to_bv 64 (- (WK + 1))); C8 (Z_to_bv 64 (tl + 1));
     C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 sym); C8 (Z_to_bv 64 WK); c104; c112; C8 (Z_to_bv 64 ux1_K120)].

  Section FILLW.
  Variables (rst : list Z) (wn wt : word) (w cur sym count len nb : Z).
  Hypothesis NBT : 1 <= nb <= tl.  Hypothesis WR : 1 <= w <= 12.
  Hypothesis SLOTS : forall s, 0 <= s < count -> 0 <= sym + s < 256 /\ 0 <= cur + s * len /\ cur + s * len + len <= 4096.
  Hypothesis CUR0 : 0 <= cur.  Hypothesis CURH : cur <= 4096.  Hypothesis CNT : 0 <= count <= 256.  Hypothesis SYM0 : 0 <= sym <= 256.

  Notation FLW := (FLF cur sym (C8 (Z_to_bv 64 w)) (C8 (Z_to_bv 64 count))).
  Notation KLATCH := (forall m2 dt' syb' y5 y6 y7 y8 y10 y11 y12 y14 y15 y17 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31,
      X1S FLW wn wt dt' rst syb' m2 -> x1pref tl (cur + count * len) dt' ->
      evt usegs POST (STF 0x1f29c m2 (Z_to_bv 64 len) y5 y6 y7 y8 (Z_to_bv 64 (-9)) y10 y11 y12 (Z_to_bv 64 (WK + 980)) y14 y15
                           (Z_to_bv 64 (- (WK + 981))) y17 (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25))
                           y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)).
  Notation CASE pc mm x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF pc mm (Z_to_bv 64 len) x5 x6 x7 x8 (Z_to_bv 64 (-9)) x10 x11 (Z_to_bv 64 nb) (Z_to_bv 64 (WK + 980)) x14 x15
         (Z_to_bv 64 (- (WK + 981))) x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).

  Ltac open_x1s I := unfold x1s in I; destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM);
                     unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
  Ltac close_x1s := unfold x1s, HUF_TBL_STACK, HUF_DTABLE_BYTES; repeat (split; [eassumption|]); eassumption.
  Ltac zl := first [ lia | Z.div_mod_to_equations; lia ].
  Ltac chk K :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_cases K; zify_cond K; [exfalso; zl |]
    | |- _ => idtac
    end.
  Ltac getbyte r sv SVR :=
    lazymatch goal with |- _ => let v := reg_val r in lazymatch v with Z_to_bv 64 ?e =>
      let ESV := fresh "ESV" in remember e as sv eqn:ESV;
      assert (SVR : 0 <= sv < 256) by (subst sv; match goal with |- 0 <= bv_unsigned ?b < 256 => let X := fresh "X" in pose proof (bv_unsigned_in_range 8 b) as X; unfold bv_modulus in X; cbn in X; lia end);
      clear ESV end end.

  Lemma ux1_lxor_low_ones : forall c q, 0 < q -> 0 <= c < 2^q -> Z.lxor c (Z.ones q) = Z.ones q - c.
  Proof.
    intros c q Hq Hc.
    assert (ON : Z.ones q = 2^q - 1) by (rewrite Z.ones_equiv; lia).
    assert (LG : Z.log2 c < q) by (destruct (Z.eq_dec c 0) as [->|NZ]; [cbn; lia|]; apply Z.log2_lt_pow2; lia).
    rewrite <- Z.ldiff_ones_l_low by lia.
    symmetry. apply Z.sub_nocarry_ldiff. apply Z.ldiff_ones_r_low; lia.
  Qed.

  Lemma ux1_land_lxor : forall a b k, Z.land (Z.lxor a b) k = Z.lxor (Z.land a k) (Z.land b k).
  Proof.
    intros a b k. apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec.
    destruct (Z.testbit a i), (Z.testbit b i), (Z.testbit k i); reflexivity.
  Qed.

  Lemma ux1_shl_shr : forall x, Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 31 = 2 * (x mod 4294967296).
  Proof.
    intros x. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
    change (2^32) with 4294967296. change (2^31) with 2147483648.
    change 18446744073709551616 with (4294967296 * 4294967296).
    rewrite Z.mul_mod_distr_r by lia.
    replace (x mod 4294967296 * 4294967296) with (2 * (x mod 4294967296) * 2147483648) by lia.
    rewrite Z.div_mul by lia. reflexivity.
  Qed.

  Lemma ux1_lxor_k32 : forall c, 0 <= c < 2147483648 ->
    Z.lxor c (ux1_K32 mod 18446744073709551616) mod 4294967296 = 2147483647 - c.
  Proof.
    intros c Hc. change 4294967296 with (2^32).
    rewrite <- Z.land_ones by lia. rewrite ux1_land_lxor.
    rewrite (Z.land_ones c 32) by lia. rewrite (Z.mod_small c) by (change (2^32) with 4294967296; lia).
    replace (Z.land (ux1_K32 mod 18446744073709551616) (Z.ones 32)) with (Z.ones 31) by (vm_compute; reflexivity).
    rewrite ux1_lxor_low_ones by first [lia | change (2^31) with 2147483648; lia].
    change (Z.ones 31) with 2147483647. reflexivity.
  Qed.

  Lemma ux1_land_m1 : forall x, 0 <= x < 18446744073709551616 -> Z.land 18446744073709551615 x = x.
  Proof.
    intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64).
    rewrite Z.land_ones by lia. apply Z.mod_small. change (2^64) with 18446744073709551616. lia.
  Qed.

  Lemma ux1_land255 : forall x, 0 <= x < 256 -> Z.land x 255 = x.
  Proof.
    intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2^8) with 256. lia.
  Qed.

  Lemma x1_fill1_loop : forall j m1 dt syb s e5 e6 e10 e11 e12 e14 e15 e17 y7 x8 x21 x22 x23 x24 x25 x26 x27 y28 y29 x30 x31,
    KLATCH -> len = 1 -> Z.to_nat (count - s) = j -> X1S FLW wn wt dt rst syb m1 -> x1pref tl (cur + s) dt -> 0 <= s < count ->
    e5 = 2 * (256 - sym) -> e6 = 2 * count -> e10 = 2 * s -> e11 = nb -> e12 = sym + s -> e14 = cur + s ->
    e15 = DT + 4 + 2 * cur -> e17 = 2 * (2147483647 - cur) ->
    evt usegs POST (STF 0x1f174 m1 (Z_to_bv 64 len) (Z_to_bv 64 e5) (Z_to_bv 64 e6) y7 x8 (Z_to_bv 64 (-9))
                        (Z_to_bv 64 e10) (Z_to_bv 64 e11) (Z_to_bv 64 e12) (Z_to_bv 64 (WK + 980)) (Z_to_bv 64 e14)
                        (Z_to_bv 64 e15) (Z_to_bv 64 (- (WK + 981))) (Z_to_bv 64 e17)
                        (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 y28 y29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KL L1 EJ I PR SR E5 E6 E10 E11 E12 E14 E15 E17; [exfalso; lia|].
    subst e5 e6 e10 e11 e12 e14 e15 e17.
    assert (DTB : DT + HUF_DTABLE_BYTES < 140737488355328) by exact DTH.
    assert (WKB : WK + wksz < 140737488355328) by exact WKH.
    open_x1s I.
    destruct (SLOTS s SR) as (SY & C0 & C1). rewrite L1 in C0, C1.
    zstep. chk K1.
    zstep. chk K2.
    zstep. zstep. chk K3.
    zstep. decide_tests. change (Z.b2z false) with 0.
    zstep. rewrite (lxor_sign_small (cur + s)) by lia. decide_tests. change (Z.b2z false) with 0.
    zstep. zstep. zstep. chk K4.
    zstep.
    pose proof (proj1 SYC) as SYB. lbyte SYB. clear SYB.
    getbyte 28 sv SVR.
    u8_sok DTC (4 + 2 * (cur + s)). zstep. u8_store DTC (4 + 2 * (cur + s)) nb; [reflexivity|].
    u8_sok DTC (4 + 2 * (cur + s) + 1). zstep. u8_store DTC (4 + 2 * (cur + s) + 1) sv; [reflexivity|].
    pose proof (prf_open tl (cur + s) dt PR) as P0.
    pose proof (prf_st_nb tl (cur + s) [] dt 0 (4 + 2 * (cur + s)) nb P0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as P1.
    pose proof (prf_st_sy tl (cur + s) [0] _ 0 (4 + 2 * (cur + s) + 1) sv P1 ltac:(lia) ltac:(lia) ltac:(lia)) as P2.
    pose proof (prf_close_c tl (cur + s) [0] _ 1%nat P2 ltac:(lia) ltac:(vm_compute; reflexivity)) as P3.
    assert (DTLEN' : Z.of_nat (length (Zupd (4 + 2 * (cur + s) + 1) sv (Zupd (4 + 2 * (cur + s)) nb dt))) = Z.of_nat (length dt))
      by (rewrite !Zupd_length; reflexivity).
    rewrite DTLEN in DTLEN'.
    assert (DTBY' : Forall isbyte (Zupd (4 + 2 * (cur + s) + 1) sv (Zupd (4 + 2 * (cur + s)) nb dt)))
      by (apply Forall_Zupd; [apply Forall_Zupd; [exact DTBY | cbv beta; lia] | cbv beta; lia]).
    clear DTLEN DTBY P0 P1 P2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (I' : X1S FLW wn wt (Zupd (4 + 2 * (cur + s) + 1) sv (Zupd (4 + 2 * (cur + s)) nb dt)) rst syb mm) by close_x1s end.
    zstep. chk K5.
    zstep. zstep. zstep.
    zstep. if_cases KB; zify_cond KB.
    - eapply (IH _ _ _ (s + 1)); [exact KL | exact L1 | lia | exact I' | | lia | zl | zl | zl | zl | zl | zl | zl | zl].
      replace (cur + (s + 1)) with (cur + s + Z.of_nat 1) by lia. exact P3.
    - zstep. eapply KL; [exact I' |]. rewrite L1.
      replace (cur + count * 1) with (cur + s + Z.of_nat 1) by lia. exact P3.
  Qed.


  Lemma x1_fill1 : forall m1 dt syb x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KLATCH -> len = 1 -> X1S FLW wn wt dt rst syb m1 -> x1pref tl cur dt ->
    evt usegs POST (CASE 0x1f118 m1 x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros KL L1 I PR.
    pose proof I as I0.
    open_x1s I.
    zstep. zstep.
    if_cases K0; zify_cond K0.
    - apply andb_false_iff in K0. destruct K0 as [K0|K0]; apply Z.ltb_ge in K0; [|lia].
      eapply KL; [exact I0|]. replace (cur + count * len) with cur by (replace count with 0 by lia; lia). exact PR.
    - do 21 zstep.
      eapply (x1_fill1_loop (Z.to_nat count) m1 dt syb 0).
      + exact KL.
      + exact L1.
      + rewrite Z.sub_0_r. reflexivity.
      + exact I0.
      + rewrite Z.add_0_r. exact PR.
      + lia.
      + rewrite (swrap32_small (256 - sym)) by lia. rewrite (Z.mod_small (256 - sym)) by lia.
        rewrite (proj2 (Z.ltb_lt (256 - sym) 257)) by lia.
        replace (bv_swrap 32 (0 - Z.b2z true) mod 18446744073709551616) with 18446744073709551615 by reflexivity.
        rewrite ux1_land_m1 by lia. rewrite ux1_shl_shr. rewrite Z.mod_small by lia. reflexivity.
      + rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2. lia.
      + lia.
      + apply ux1_land255. lia.
      + rewrite (swrap32_small (sym + 0)) by lia. reflexivity.
      + rewrite (swrap32_small (cur + 0)) by lia. reflexivity.
      + rewrite Z.add_0_r. rewrite (swrap32_small cur) by lia. rewrite (Z.mod_small cur) by lia.
        rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2. lia.
      + rewrite ux1_shl_shr. rewrite ux1_lxor_k32 by lia. reflexivity.
  Qed.
  End FILLW.
End X1.
