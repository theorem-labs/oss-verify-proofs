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

  Notation LH mm s x7 x8 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF 0x1edd4 mm (Z_to_bv 64 len) (Z_to_bv 64 (4 * count)) (Z_to_bv 64 (cur + 2 * s)) x7 x8 (Z_to_bv 64 (-9))
         (Z_to_bv 64 (4 * s)) (Z_to_bv 64 nb) (Z_to_bv 64 (sym + s)) (Z_to_bv 64 (WK + 980)) (Z_to_bv 64 (cur + 2 * s))
         (Z_to_bv 64 (DT + 4 + 2 * cur)) (Z_to_bv 64 (- (WK + 981))) (Z_to_bv 64 (4 * (256 - sym))) (Z_to_bv 64 (-17))
         (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).

  Lemma f2_lo : forall a b, (a * 256 + b) mod 256 = b mod 256.
  Proof. intros a b. rewrite Z.add_comm. apply Z_mod_plus_full. Qed.

  Lemma f2_lor_v : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z.lor (Z.shiftl a 8 mod 2^64) b = a * 256 + b.
  Proof.
    intros a b Ha Hb. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. change (2^64) with 18446744073709551616.
    rewrite Z.mod_small by lia.
    apply (lor_add (a * 256) b 8); [lia | change (2^8) with 256; lia | change (2^8) with 256; apply Z_mod_mult].
  Qed.

  Lemma f2_hi : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z.shiftr (a * 256 + b) 8 = a.
  Proof.
    intros a b Ha Hb. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  Qed.

  Lemma f2_land255 : forall x, 0 <= x < 256 -> Z.land x 255 = x.
  Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2^8) with 256. lia. Qed.

  Lemma f2_a7 : forall x, 0 <= x <= 256 -> Z.shiftr ((Z.land (2^64 - 1) (x mod 2^64) * 2^32) mod 2^64) 30 = 4 * x.
  Proof.
    intros x Hx. change (2^64 - 1) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    change (2^64) with 18446744073709551616. change (2^32) with 4294967296.
    repeat rewrite (Z.mod_small x) by lia. rewrite Z.mod_small by lia.
    rewrite Z.shiftr_div_pow2 by lia. change (2^30) with 1073741824.
    replace (x * 4294967296) with (4 * x * 1073741824) by lia. apply Z.div_mul. lia.
  Qed.

  Ltac f2_open I := destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM);
                    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
  Ltac f2_close := unfold x1s, HUF_TBL_STACK, HUF_DTABLE_BYTES; repeat (split; [eassumption|]); eassumption.
  Ltac f2_dec := repeat match goal with
    | |- context [Z.lxor ?a ?c] => rewrite (lxor_sign_small a) by lia
    | |- context [Z.ltb ?a ?b] => first [rewrite (proj2 (Z.ltb_ge a b)) by lia | rewrite (proj2 (Z.ltb_lt a b)) by lia]
    | |- context [bv_swrap 32 ?z] => rewrite (swrap32_small z) by lia
    | |- context [Z.shiftl ?a ?k] => rewrite (Z.shiftl_mul_pow2 a k) by lia
    | |- context [Z.b2z false] => change (Z.b2z false) with 0
    | |- context [Z.b2z true] => change (Z.b2z true) with 1 end; zsimp.
  Ltac f2_chk := let K := fresh "K" in if_cases K;
    [exfalso; try (unfold bv_lts in K; rewrite !signed_lit in K by lia); zify_cond K; lia | clear K].
  Ltac f2_getbyte r sv SVR :=
    lazymatch goal with |- _ => let v := reg_val r in lazymatch v with Z_to_bv 64 ?e =>
      let ESV := fresh "ESV" in remember e as sv eqn:ESV;
      assert (SVR : 0 <= sv < 256) by (subst sv; match goal with |- 0 <= bv_unsigned ?b < 256 => let X := fresh "X" in pose proof (bv_unsigned_in_range 8 b) as X; unfold bv_modulus in X; cbn in X; lia end);
      clear ESV end end.
  Ltac f2_dtst DTC i v := u8_sok DTC i; zstep; u8_store DTC i v;
    [first [reflexivity | rewrite Z.mod_mod by lia; reflexivity | apply f2_lo | lia]|].
  Ltac f2_set r e := let v := reg_val r in replace v with (Z_to_bv 64 e) by (f_equal; lia).

  Lemma f2_loop : forall j m1 dt syb s x7 x8 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KLATCH -> len = 2 -> Z.to_nat (count - s) = j -> X1S FLW wn wt dt rst syb m1 -> x1pref tl (cur + 2 * s) dt -> 0 <= s < count ->
    evt usegs POST (LH m1 s x7 x8 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KL L2 EJ I PR SR; [exfalso; lia|].
    f2_open I.
    destruct (SLOTS s SR) as (SY & C0 & C1). rewrite L2 in C0, C1.
    destruct (SLOTS (count - 1) ltac:(lia)) as (SYE & _ & CE). rewrite L2 in CE.
    zstep. f2_chk.
    zstep. f2_chk.
    zstep.
    zstep. f2_chk.
    zstep. zstep. zstep. zstep. f2_dec.
    zstep. try f2_chk.
    zstep.
    pose proof (proj1 SYC) as SYB. lbyte SYB. clear SYB.
    f2_getbyte 7 sv SVR.
    zstep. zstep. f2_dec.
    f2_dtst DTC (4 + 2 * (cur + 2 * s)) nb.
    f2_dtst DTC (4 + 2 * (cur + 2 * s) + 1) sv.
    zstep. f2_chk.
    zstep. zstep. f2_dec.
    zstep. f2_chk.
    zstep. zstep. zstep. zstep. f2_dec.
    zstep. try f2_chk.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 7 in replace v with (Z_to_bv 64 (sv * 256 + nb)) by (f_equal; symmetry; apply f2_lor_v; lia) end.
    zstep.
    lazymatch goal with |- _ => let v := reg_val 30 in replace v with (Z_to_bv 64 sv) by (f_equal; symmetry; apply f2_hi; lia) end.
    f2_dtst DTC (4 + 2 * (cur + 2 * s + 1)) nb.
    f2_dtst DTC (4 + 2 * (cur + 2 * s + 1) + 1) sv.
    zstep. f2_chk.
    zstep. zstep. zstep. zstep.
    lazymatch type of DTC with u8arr _ _ _ (map _ ?d) => remember d as dt' eqn:EDT' end.
    assert (DTLEN' : Z.of_nat (length dt') = Z.of_nat (length dt)) by (subst dt'; rewrite !Zupd_length; reflexivity).
    rewrite DTLEN in DTLEN'.
    assert (DTBY' : Forall isbyte dt') by (subst dt'; repeat (apply Forall_Zupd; [|lia]); exact DTBY).
    assert (PR' : x1pref tl (cur + 2 * (s + 1)) dt').
    { subst dt'. replace (cur + 2 * (s + 1)) with (cur + 2 * s + Z.of_nat 2) by lia.
      apply (prf_close_c tl (cur + 2 * s) [1; 0]); [| lia | reflexivity].
      apply (prf_st_sy _ _ _ _ 1); [| lia | lia | lia].
      apply (prf_st_nb _ _ _ _ 1); [| lia | lia | lia | rewrite !Zupd_length; lia | lia].
      apply (prf_st_sy _ _ _ _ 0); [| lia | lia | lia].
      apply (prf_st_nb _ _ _ _ 0); [apply prf_open; exact PR | lia | lia | lia | lia | lia]. }
    clear EDT' DTLEN DTBY.
    assert (I' : X1S FLW wn wt dt' rst syb m1) by f2_close.
    zstep. if_cases KB; zify_cond KB.
    - f2_set 14 (cur + 2 * (s + 1)). f2_set 6 (cur + 2 * (s + 1)).
      f2_set 10 (4 * (s + 1)). f2_set 12 (sym + (s + 1)).
      eapply (IH m1 dt' syb (s + 1)); [exact KL | exact L2 | lia | exact I' | exact PR' | lia].
    - zstep. eapply KL; [exact I'|]. replace (cur + count * len) with (cur + 2 * (s + 1)) by (rewrite L2; lia). exact PR'.
  Qed.

  Lemma x1_fill2 : forall m1 dt syb x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KLATCH -> len = 2 -> X1S FLW wn wt dt rst syb m1 -> x1pref tl cur dt ->
    evt usegs POST (CASE 0x1ed84 m1 x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros KL L2 I PR.
    pose proof I as I0. f2_open I.
    zstep. zstep. if_cases K0; zify_cond K0.
    - eapply KL; [exact I0|]. replace (cur + count * len) with cur by nia. exact PR.
    - do 18 zstep. f2_dec.
      f2_set 5 (4 * count). f2_set 14 (cur + 2 * 0). f2_set 6 (cur + 2 * 0).
      lazymatch goal with |- _ => let v := reg_val 11 in replace v with (Z_to_bv 64 nb) by (f_equal; symmetry; apply f2_land255; lia) end.
      lazymatch goal with |- _ => let v := reg_val 15 in replace v with (Z_to_bv 64 (DT + 4 + 2 * cur)) by (f_equal; rewrite ?Z.mod_small by lia; lia) end.
      lazymatch goal with |- _ => let v := reg_val 17 in replace v with (Z_to_bv 64 (4 * (256 - sym))) by (f_equal; symmetry; apply f2_a7; lia) end.
      eapply (f2_loop (Z.to_nat (count - 0)) m1 dt syb 0); [exact KL | exact L2 | reflexivity | exact I0 | | lia].
      replace (cur + 2 * 0) with cur by lia. exact PR.
  Qed.
  End FILLW.
End X1.
