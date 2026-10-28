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
  Notation OST pc mm x6 x7 x8 x10 x11 x12 x14 x15 x17 x22 x23 x25 x26 x27 x28 x30 x31 :=
    (STF pc mm (Z_to_bv 64 len) (Z_to_bv 64 sym) x6 x7 x8 (Z_to_bv 64 (-9)) x10 x11 x12 (Z_to_bv 64 (WK + 980)) x14 x15
         (Z_to_bv 64 (- (WK + 981))) x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) (Z_to_bv 64 count) x22 x23
         (Z_to_bv 64 nb) x25 x26 x27 x28 (Z_to_bv 64 (256 - sym)) x30 x31).

  Local Ltac fci_chk := exfalso; first [lia | congruence | Z.div_mod_to_equations; lia].
  Local Ltac fci_setr r e := let v := reg_val r in replace v with (Z_to_bv 64 e) by (f_equal; lia).
  Local Ltac dtstB DTC i v BH := u8_sok DTC i; zstep; u8_store DTC i v; [unfold hidden in BH; rewrite BH; symmetry; apply Z.mod_small; lia|].
  Local Ltac pnb P c k i v := let P' := fresh "P" in
    pose proof (prf_st_nb tl c _ _ k i v P ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite ?Zupd_length; lia) ltac:(lia)) as P'; clear P; rename P' into P.
  Local Ltac psy P c k i v := let P' := fresh "P" in
    pose proof (prf_st_sy tl c _ _ k i v P ltac:(lia) ltac:(lia) ltac:(lia)) as P'; clear P; rename P' into P.

  Definition KIN (s off : Z) : Prop :=
    forall m2 dt' syb' y6 y7 y8 y11 y12 y22 y23 y25 y26 y27 y28 y30 y31,
      X1S FLW wn wt dt' rst syb' m2 -> x1pref tl (cur + off + len) dt' ->
      evt usegs POST (OST 0x1f0f4 m2 y6 y7 y8 (Z_to_bv 64 (DT + 20 + 2 * (cur + off))) y11 y12 (Z_to_bv 64 (2 * len))
                          (Z_to_bv 64 (cur + off)) (Z_to_bv 64 s) y22 y23 y25 y26 y27 y28 y30 y31).

  Lemma x1_fcd_in : forall j Q m1 dt syb s off q D sv a6 a7 a11 a28 x8 x22 x23 x25 x26 x27 x30 x31,
    KIN s off -> len = 16 * Q -> Z.to_nat (Q - q) = j -> X1S FLW wn wt dt rst syb m1 -> x1pref tl (cur + off + 16 * q) dt ->
    0 <= off -> cur + off + len <= 4096 -> 0 <= q < Q -> 0 <= sv < 256 ->
    a6 = 18446744073709551615 - (DT + 4 + 2 * (cur + off)) -> a7 = 32 * q -> a11 = DT + 20 + 2 * (cur + off) + 32 * q -> a28 = 16 * q ->
    0 <= D < 2^64 -> D mod 256 = nb -> Z.shiftr D 8 mod 256 = sv -> Z.shiftr D 16 mod 256 = nb -> Z.shiftr D 24 mod 256 = sv ->
    Z.shiftr D 32 mod 256 = nb -> Z.shiftr D 40 mod 256 = sv -> Z.shiftr D 48 mod 256 = nb -> Z.shiftr D 56 mod 256 = sv ->
    evt usegs POST (OST 0x1f034 m1 (Z_to_bv 64 a6) (Z_to_bv 64 a7) x8 (Z_to_bv 64 (DT + 20 + 2 * (cur + off))) (Z_to_bv 64 a11) (Z_to_bv 64 D)
                        (Z_to_bv 64 (2 * len)) (Z_to_bv 64 (cur + off)) (Z_to_bv 64 s) x22 x23 x25 x26 x27 (Z_to_bv 64 a28) x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KS L16 EJ I PR OFF0 OFFH QR SVR E6 E7 E11 E28 DR B0 B1 B2 B3 B4 B5 B6 B7; [exfalso; lia|].
    destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM).
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    hide B0. hide B1. hide B2. hide B3. hide B4. hide B5. hide B6. hide B7.
    remember (cur + off + 16 * q) as c eqn:EC.
    remember (4 + 2 * c) as bs eqn:EBS.
    pose proof (prf_open tl c dt PR) as P. clear PR.
    replace (Z_to_bv 64 a11) with (Z_to_bv 64 (DT + bs + 16)) by (f_equal; lia).
    zstep. if_cases KH; zify_cond KH; [fci_chk|].
    do 8 zstep.
    fci_setr 27 (DT + bs).
    dtstB DTC (bs + 4) nb B4. pnb P c 2 (bs + 4) nb.
    dtstB DTC (bs + 5) sv B5. psy P c 2 (bs + 5) sv.
    dtstB DTC (bs + 6) nb B6. pnb P c 3 (bs + 6) nb.
    dtstB DTC (bs + 7) sv B7. psy P c 3 (bs + 7) sv.
    dtstB DTC (bs + 0) nb B0. pnb P c 0 (bs + 0) nb.
    dtstB DTC (bs + 1) sv B1. psy P c 0 (bs + 1) sv.
    dtstB DTC (bs + 2) nb B2. pnb P c 1 (bs + 2) nb.
    dtstB DTC (bs + 3) sv B3. psy P c 1 (bs + 3) sv.
    zstep. if_cases KH1; zify_cond KH1; [fci_chk|].
    dtstB DTC (bs + 12) nb B4. pnb P c 6 (bs + 12) nb.
    dtstB DTC (bs + 13) sv B5. psy P c 6 (bs + 13) sv.
    dtstB DTC (bs + 14) nb B6. pnb P c 7 (bs + 14) nb.
    dtstB DTC (bs + 15) sv B7. psy P c 7 (bs + 15) sv.
    dtstB DTC (bs + 8) nb B0. pnb P c 4 (bs + 8) nb.
    dtstB DTC (bs + 9) sv B1. psy P c 4 (bs + 9) sv.
    dtstB DTC (bs + 10) nb B2. pnb P c 5 (bs + 10) nb.
    dtstB DTC (bs + 11) sv B3. psy P c 5 (bs + 11) sv.
    zstep. if_cases KH2; zify_cond KH2; [fci_chk|].
    dtstB DTC (bs + 20) nb B4. pnb P c 10 (bs + 20) nb.
    dtstB DTC (bs + 21) sv B5. psy P c 10 (bs + 21) sv.
    dtstB DTC (bs + 22) nb B6. pnb P c 11 (bs + 22) nb.
    dtstB DTC (bs + 23) sv B7. psy P c 11 (bs + 23) sv.
    dtstB DTC (bs + 16) nb B0. pnb P c 8 (bs + 16) nb.
    dtstB DTC (bs + 17) sv B1. psy P c 8 (bs + 17) sv.
    dtstB DTC (bs + 18) nb B2. pnb P c 9 (bs + 18) nb.
    dtstB DTC (bs + 19) sv B3. psy P c 9 (bs + 19) sv.
    zstep. if_cases KH3; zify_cond KH3; [fci_chk|].
    dtstB DTC (bs + 28) nb B4. pnb P c 14 (bs + 28) nb.
    dtstB DTC (bs + 29) sv B5. psy P c 14 (bs + 29) sv.
    dtstB DTC (bs + 30) nb B6. pnb P c 15 (bs + 30) nb.
    dtstB DTC (bs + 31) sv B7. psy P c 15 (bs + 31) sv.
    dtstB DTC (bs + 24) nb B0. pnb P c 12 (bs + 24) nb.
    dtstB DTC (bs + 25) sv B1. psy P c 12 (bs + 25) sv.
    dtstB DTC (bs + 26) nb B2. pnb P c 13 (bs + 26) nb.
    dtstB DTC (bs + 27) sv B3. psy P c 13 (bs + 27) sv.
    lazymatch type of DTC with u8arr _ _ _ (map _ ?d) => remember d as dt' eqn:EDT' end.
    assert (DTLEN' : Z.of_nat (length dt') = Z.of_nat (length dt)) by (subst dt'; rewrite !Zupd_length; reflexivity).
    rewrite DTLEN in DTLEN'.
    assert (DTBY' : Forall isbyte dt') by (subst dt'; repeat (apply Forall_Zupd; [|lia]); exact DTBY).
    pose proof (prf_close_c tl c _ dt' 16 P ltac:(lia) eq_refl) as PC. change (Z.of_nat 16) with 16 in PC.
    clear EDT' DTLEN DTBY P.
    assert (I' : X1S FLW wn wt dt' rst syb m1) by (unfold x1s, HUF_TBL_STACK, HUF_DTABLE_BYTES; repeat (split; [eassumption|]); eassumption).
    zstep. rewrite ?swrap32_small by lia.
    zstep. zstep.
    zstep. if_cases KL2; zify_cond KL2.
    - unfold hidden in B0, B1, B2, B3, B4, B5, B6, B7.
      eapply (IH Q m1 dt' syb s off (q + 1) D sv).
      all: try eassumption.
      all: try (replace (cur + off + 16 * (q + 1)) with (c + 16) by lia; exact PC).
      all: lazymatch goal with |- _ = _ => lia | |- _ <= _ => lia | |- _ < _ => lia | |- _ <= _ < _ => lia end.
    - eapply KS; [exact I'|]. replace (cur + off + len) with (c + 16) by lia. exact PC.
  Qed.
  End FILLW.
End X1.
