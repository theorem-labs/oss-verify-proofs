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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_kit RZ_hft_bdt_defs RZ_hft_x1_kit huf411_kit_x1_defs huf411_kit_x1_fcd_in.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma fcd_rd4 : forall mm A pre (w : word) post k a,
  rw_cells usegs mm A (pre ++ C8 w :: post) -> Z.of_nat (cells_size pre) = k -> a = wa (A + k) ->
  ov_read_bytes usegs mm a 4 = Some (le4 w).
Proof.
  intros mm A pre w post k a H <- ->.
  apply (proj1 (rw_cells_app usegs mm A pre (C8 w :: post))) in H. destruct H as [_ [[_ Hb] _]]. cbn [cells_bytes cbytes] in Hb.
  pose proof (bytes_at_ov_read usegs mm _ _ 0 4 Hb) as R. rewrite Z.add_0_r in R.
  rewrite R. 2:{ cbn [skipn]. rewrite length_app, length_le8. lia. }
  change (skipn 0 (le8 w ++ cells_bytes post)) with (le8 w ++ cells_bytes post).
  rewrite firstn_app, length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma fcd_lxor_ones : forall c, 0 <= c < 2^64 -> Z.lxor c 18446744073709551615 = 18446744073709551615 - c.
Proof.
  intros c Hc. change 18446744073709551615 with (Z.ones 64).
  assert (ON : Z.ones 64 = 2^64 - 1) by (rewrite Z.ones_equiv; lia).
  assert (LG : Z.log2 c < 64) by (destruct (Z.eq_dec c 0) as [->|NZ]; [cbn; lia|]; apply Z.log2_lt_pow2; lia).
  rewrite <- Z.ldiff_ones_l_low by lia.
  symmetry. apply Z.sub_nocarry_ldiff. apply Z.ldiff_ones_r_low; lia.
Qed.

Lemma fcd_d4 : forall sv nb M, M = 2^64 -> Z.lor (Z.shiftl sv 8 mod M) nb * (ux1_K120 mod M) = d4 sv nb.
Proof. intros sv nb M ->. unfold d4, ux1_K120. reflexivity. Qed.

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
  Notation OST pc mm x6 x7 x8 x10 x11 x12 x14 x15 x17 x22 x23 x25 x26 x27 x28 x30 x31 :=
    (STF pc mm (Z_to_bv 64 len) (Z_to_bv 64 sym) x6 x7 x8 (Z_to_bv 64 (-9)) x10 x11 x12 (Z_to_bv 64 (WK + 980)) x14 x15
         (Z_to_bv 64 (- (WK + 981))) x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) (Z_to_bv 64 count) x22 x23
         (Z_to_bv 64 nb) x25 x26 x27 x28 (Z_to_bv 64 (256 - sym)) x30 x31).

  Ltac getbyte r sv SVR :=
    lazymatch goal with |- _ => let v := reg_val r in lazymatch v with Z_to_bv 64 ?e =>
      let ESV := fresh "ESV" in remember e as sv eqn:ESV;
      assert (SVR : 0 <= sv < 256) by (subst sv; match goal with |- 0 <= bv_unsigned ?b < 256 => let X := fresh "X" in pose proof (bv_unsigned_in_range 8 b) as X; unfold bv_modulus in X; cbn in X; lia end);
      clear ESV end end.
  Ltac fcd_ltb :=
    repeat match goal with |- context [Z.ltb ?a ?b] =>
      first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; lia)
            | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; lia) ] end;
    cbn [Z.b2z].
  Ltac fcd_landm1 :=
    repeat match goal with |- context [Z.land ?c ?x] =>
      let c' := eval vm_compute in c in
      lazymatch c' with 18446744073709551615 =>
        replace (Z.land c x) with x by (change c with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small; lia) end end.
  Ltac fcd_chk := exfalso; first [lia | congruence | Z.div_mod_to_equations; lia].
  Ltac setr r e := let v := reg_val r in replace v with (Z_to_bv 64 e) by (f_equal; lia).
  Ltac fcd_alia := lazymatch goal with |- _ = _ => lia | |- _ <= _ => lia | |- _ < _ => lia | |- _ <= _ < _ => lia end.

  Lemma x1_fcd_sym : forall j Q m1 dt syb s x6 x7 x8 x11 x12 x22 x23 x25 x26 x27 x28 x30 x31,
    KLATCH -> len = 16 * Q -> 1 <= Q <= 128 -> Z.to_nat (count - s) = j -> X1S FLW wn wt dt rst syb m1 ->
    x1pref tl (cur + s * len) dt -> 0 <= s < count ->
    evt usegs POST (OST 0x1efe0 m1 x6 x7 x8 (Z_to_bv 64 (DT + 20 + 2 * (cur + s * len))) x11 x12 (Z_to_bv 64 (2 * len))
                        (Z_to_bv 64 (cur + s * len)) (Z_to_bv 64 s) x22 x23 x25 x26 x27 x28 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KL L16 QR EJ I PR SR; [exfalso; lia|].
    pose proof I as I0.
    destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM).
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    destruct (SLOTS s SR) as (SY & C0 & C1).
    zstep. if_cases KB; zify_cond KB; [fcd_chk|].
    zstep. zstep. if_cases KC; zify_cond KC; [fcd_chk|].
    zstep. rewrite ?Z.shiftl_mul_pow2 by lia. try change (2^1) with 2.
    zstep. zstep. if_cases KD; zify_cond KD; [fcd_chk|].
    zstep. zstep.
    rewrite ?lxor_sign_small by lia. fcd_ltb.
    zstep. zstep.
    zstep. if_cases KE; zify_cond KE; [fcd_chk|].
    zstep. zstep. zstep.
    pose proof (proj1 SYC) as SYB. lbyte SYB. clear SYB. getbyte 11 sv SVR.
    zstep. zstep. zstep. zstep.
    zstep. zstep.
    rewrite fcd_d4 by reflexivity.
    rewrite fcd_lxor_ones by lia.
    pose proof (d4_bytes sv nb SVR ltac:(lia)) as (DR & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
    remember (d4 sv nb) as D eqn:ED. clear ED.
    clear DTC HWC RK RST STS SYC WKR F0 NSC FSAV STK MI MU WM.
    eapply x1_fcd_in with (flags := flags) (f16 := f16) (hw := hw) (rank := rank) (tl := tl) (r0 := r0) (rst := rst) (wn := wn) (wt := wt) (w := w)
      (j := Z.to_nat (Q - 0)) (Q := Q) (m1 := m1) (dt := dt) (syb := syb) (s := s) (off := s * len) (q := 0) (D := D) (sv := sv).
    all: try eassumption.
    all: try clear OFFDT OFFWK DTWK.
    all: try (apply Z.mul_nonneg_nonneg; lia).
    all: try (replace (cur + s * len + 16 * 0) with (cur + s * len) by lia; exact PR).
    all: try fcd_alia.
    unfold KIN. intros m2 dt2 syb2 y6 y7 y8 y11 y12 y22 y23 y25 y26 y27 y28 y30 y31 I2 PR2.
    clear B0 B1 B2 B3 B4 B5 B6 B7 DR.
    zstep. rewrite ?swrap32_small by lia.
    zstep.
    zstep. rewrite ?swrap32_small by lia.
    zstep. if_cases KF; zify_cond KF; [fcd_chk|].
    zstep. zstep. zstep.
    zstep. if_cases KG; zify_cond KG.
    - setr 10 (DT + 20 + 2 * (cur + (s + 1) * len)). setr 15 (cur + (s + 1) * len). setr 17 (s + 1).
      eapply (IH Q m2 dt2 syb2 (s + 1)).
      all: try eassumption.
      all: try (replace (cur + (s + 1) * len) with (cur + s * len + len) by lia; exact PR2).
      all: fcd_alia.
    - zstep. eapply KL; [exact I2|]. replace (cur + count * len) with (cur + s * len + len); [exact PR2|].
      replace count with (s + 1) by lia. lia.
  Qed.

  Lemma x1_fillD : forall Q m1 dt syb x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KLATCH -> len = 16 * Q -> 1 <= Q <= 128 -> X1S FLW wn wt dt rst syb m1 -> x1pref tl cur dt ->
    evt usegs POST (CASE 0x1ef90 m1 x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros KL LQ QR I PR.
    pose proof I as I0.
    destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM).
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    zstep. zstep.
    if_cases KA; zify_cond KA.
    { assert (C0 : count = 0) by (apply andb_false_iff in KA; destruct KA as [KA|KA]; apply Z.ltb_ge in KA; lia).
      eapply KL; [exact I0|]. rewrite C0, Z.mul_0_l, Z.add_0_r. exact PR. }
    zstep. zstep.
    replace (Z.land nb 255) with nb by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia).
    zstep. zstep.
    rewrite (swrap32_small (sym + 0)) by lia. replace (sym + 0) with sym by lia.
    zstep. zstep.
    rewrite (lxor_sign_small count) by lia. fcd_ltb.
    zstep. zstep.
    rewrite (swrap32_small (256 - sym)) by lia.
    let a := cur_mem_addr in
    pose proof (fcd_rd4 m1 (SPV + -240) [C8 (Z_to_bv 64 876); C8 flags; CB 8 f16; C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 ux1_K32); C8 (Z_to_bv 64 (DT + 20));
      C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (tl + 1)); C8 (Z_to_bv 64 (- (WK + 1))); C8 (Z_to_bv 64 (tl + 1))] (Z_to_bv 64 cur)
      [C8 (Z_to_bv 64 sym); C8 (Z_to_bv 64 WK); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 count); C8 (Z_to_bv 64 ux1_K120)] 80 a F0 eq_refl
      ltac:(unfold wa; f_equal; lia)) as RD4.
    zstep. clear RD4.
    rewrite (sx32w_small cur) by lia.
    zstep. zstep. fcd_ltb.
    do 7 zstep.
    fcd_landm1.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
    replace (Z_to_bv 64 (len * 2)) with (Z_to_bv 64 (2 * len)) by (f_equal; lia).
    replace (Z_to_bv 64 (DT + 20 + cur * 2)) with (Z_to_bv 64 (DT + 20 + 2 * (cur + 0 * len))) by (f_equal; lia).
    replace (Z_to_bv 64 cur) with (Z_to_bv 64 (cur + 0 * len)) by (f_equal; lia).
    eapply (x1_fcd_sym (Z.to_nat (count - 0)) Q m1 dt syb 0).
    all: try eassumption.
    all: try (replace (cur + 0 * len) with cur by lia; exact PR).
    all: fcd_alia.
  Qed.
  End FILLW.
End X1.
