(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memmove RZ_seq_iface seqD_kit_sc_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma sc_wadd : forall x y M, M = 2^64 -> Z_to_bv 64 (x mod M + y) = Z_to_bv 64 (x + y).
Proof.
  intros x y M ->. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Section Hi.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo OP OENDW IP LEN OV B0 B1 R0 R1 : Z).
  Hypothesis B0L : 4096 <= B0.
  Hypothesis B1H : B1 < 2^47.
  Hypothesis OPB : B0 <= OP.
  Hypothesis LEN0 : 0 <= LEN.
  Hypothesis OPL : OP + LEN <= B1.
  Hypothesis OW0 : 0 <= OENDW.
  Hypothesis OWH : OENDW + 32 <= B1.
  Hypothesis RDM : rdbl usegs m R0 R1.
  Hypothesis R0L : 4096 <= R0.
  Hypothesis R1H : R1 < 2^47.
  Hypothesis IPR : R0 <= IP.
  Hypothesis OVC : sc_ovc OV IP OP LEN B0 B1 R0 R1.
  Hypothesis LOS : lo <= SPV - 80.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SPR : 0 <= SPV < 2^47.
  Hypothesis OFFB : B0 + (B1 - B0) <= lo \/ SPV <= B0.
  Hypothesis OFFR : R0 + (R1 - R0) <= lo \/ SPV <= R0.

  Notation POST := (zd_safecopy_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP LEN OENDW B0 B1 R0 R1 lo m).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -80)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation SCI m1 := (sc_inv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 m SPV lo OP OENDW LEN B0 B1 m1).

  Lemma sc_ovf : (OV = 1 /\ R0 = B0 /\ R1 = B1) \/ (OV = 0 /\ IP + LEN + 32 <= R1).
  Proof. destruct OVC as [(H1 & H2 & H3 & H4)|(H1 & H2 & H3)]; [left|right]; lia. Qed.

  Ltac rdp :=
    lazymatch goal with MU : munch _ m ?m1, REG : stk usegs ?m1 B0 B1 |- _ =>
      pose proof (sc_rd _ _ _ _ _ _ _ _ _ _ _ RDM OPB OPL OWH LOS OFFR MU REG) as RD end.
  Ltac ubf := let KC := fresh "KC" in ub KC.
  Ltac mv d sr :=
    lazymatch goal with MU : munch _ m ?m1, REG : stk usegs ?m1 B0 B1 |- _ =>
      let R := fresh "RD" in
      pose proof (sc_rd _ _ _ _ _ _ _ _ _ _ _ RDM OPB OPL OWH LOS OFFR MU REG) as R;
      mmv R B0 B1 d sr; clear R end.
  Ltac ld8 a :=
    lazymatch goal with MU : munch _ m ?m1, REG : stk usegs ?m1 B0 B1 |- _ =>
      let R := fresh "RD" in
      pose proof (sc_rd _ _ _ _ _ _ _ _ _ _ _ RDM OPB OPL OWH LOS OFFR MU REG) as R;
      ldRd R a 1%nat; ldRd R (a + 1) 1%nat; ldRd R (a + 2) 1%nat; ldRd R (a + 3) 1%nat;
      ldRd R (a + 4) 1%nat; ldRd R (a + 5) 1%nat; ldRd R (a + 6) 1%nat; ldRd R (a + 7) 1%nat; clear R end.
  Ltac st1 A := lazymatch goal with R : stk usegs _ B0 B1 |- _ => str R A 1%nat end.
  Ltac it8 a c :=
    ld8 a; zstep; st1 (c + 4); st1 (c + 5); st1 (c + 6); st1 (c + 7); st1 c; st1 (c + 1); st1 (c + 2); st1 (c + 3);
    zstep; ubf; zstep; zstep; ubf; zstep; zstep; zstep.
  Ltac itm dd sr :=
    zstep; zstep; zstep; zstep; zstep; mv dd sr; zstep; ubf; zstep; ubf;
    zstep; zstep; zstep; zstep; zstep; mv (dd + 16) (sr + 16); zstep; ubf; zstep; ubf; zstep; zstep; zstep.

  Lemma sc_tl : forall (k : nat) m1 (c d : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> OP <= c -> c + Z.of_nat k + 1 = OP + LEN -> R0 <= c + d -> OP + LEN + d <= R1 ->
    xs7 = Z_to_bv 64 c -> xs1 = Z_to_bv 64 d -> xs6 = Z_to_bv 64 (OP + LEN) -> xa0 = Z_to_bv 64 2 ->
    evt usegs POST (ST 124280 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I HC HK HR0 HR1 -> -> -> ->; open_sci I; rdp;
      zstep; rewrite ?sc_wadd by reflexivity; zstep; zstep; ub K; zstep; zstep; ub K1;
      ldRd RD (d + c) 1%nat; clear RD; str REG c 1%nat; zstep; zstep; br K2;
      [exfalso; lia | use sc_epi | use (IH _ (c + 1) d) | exfalso; lia].
  Qed.

  Lemma sc_1048 : forall m1 (c op ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> OP <= op <= c -> c <= B1 -> R0 <= ip -> OP + LEN + (ip - op) <= R1 ->
    xs7 = Z_to_bv 64 c -> xs6 = Z_to_bv 64 (OP + LEN) -> xs0 = Z_to_bv 64 op -> xs1 = Z_to_bv 64 ip ->
    evt usegs POST (ST 124268 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I H1 H2 H3 H4 -> -> -> ->.
    zstep. br K.
    - use sc_epi.
    - zstep. zstep. use (sc_tl (Z.to_nat (OP + LEN - c - 1)) _ c (ip - op)).
  Qed.

  Lemma sc_1016 : forall m1 (op ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> OP <= op <= OENDW -> R0 <= ip -> OP + LEN + (ip - op) <= R1 ->
    xs7 = Z_to_bv 64 (OENDW - op) -> xs1 = Z_to_bv 64 ip -> xs0 = Z_to_bv 64 op -> xs6 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 124236 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I H1 H2 H3 -> -> -> ->.
    zstep. zstep. zstep. zstep. ub K. zstep. zstep. ub K1. zstep. ub K2. zstep.
    use (sc_1048 _ OENDW op ip).
  Qed.

  Lemma sc_w8a : forall (q : nat) m1 (c op ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> OP <= op <= c -> c <= OENDW -> OENDW - c <= 8 * (Z.of_nat q + 1) -> R0 <= ip ->
    OENDW + 8 + (ip - op) <= R1 -> OP + LEN + (ip - op) <= R1 ->
    xa0 = Z_to_bv 64 9 -> xa1 = Z_to_bv 64 (c + (ip - op)) -> xa2 = Z_to_bv 64 c -> xa3 = Z_to_bv 64 c ->
    xa4 = Z_to_bv 64 (c + (ip - op)) -> xs2 = Z_to_bv 64 OENDW -> xs7 = Z_to_bv 64 (OENDW - op) ->
    xs0 = Z_to_bv 64 op -> xs1 = Z_to_bv 64 ip -> xs6 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 123744 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    induction q as [|q IH]; intros until x31; intros I H1 H2 HQ H3 H4 H5 -> -> -> -> -> -> -> -> -> ->; open_sci I;
      it8 (c + (ip - op)) c; br K2;
      [exfalso; lia | zstep; use (sc_1016 _ op ip) | use (IH _ (c + 8) op ip) | zstep; use (sc_1016 _ op ip)].
  Qed.

  Lemma sc_w8b : forall (q : nat) m1 (c d : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> OP <= c <= OP + LEN -> OP + LEN <= OENDW -> OP + LEN - c <= 8 * (Z.of_nat q + 1) ->
    R0 <= c + d -> OP + LEN + 8 + d <= R1 ->
    xs0 = Z_to_bv 64 c -> xs1 = Z_to_bv 64 (c + d) -> xa0 = Z_to_bv 64 9 -> xa1 = Z_to_bv 64 (c + d) ->
    xa2 = Z_to_bv 64 c -> xs3 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 123892 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    induction q as [|q IH]; intros until x31; intros I H1 H2 HQ H3 H4 -> -> -> -> -> ->; open_sci I;
      it8 (c + d) c; br K2;
      [exfalso; lia | zstep; use sc_epi | use (IH _ (c + 8) d) | zstep; use sc_epi].
  Qed.

  Lemma sc_wl2 : forall (q : nat) m1 (dd op ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> OP <= op <= OENDW -> op < dd < OENDW -> OENDW - dd <= 32 * (Z.of_nat q + 1) -> R0 <= ip ->
    OENDW + 32 + (ip - op) <= R1 -> OP + LEN + (ip - op) <= R1 ->
    xs4 = Z_to_bv 64 dd -> xs3 = Z_to_bv 64 (dd + (ip - op) + 16) -> xs8 = Z_to_bv 64 (-17) -> xs2 = Z_to_bv 64 OENDW ->
    xs0 = Z_to_bv 64 op -> xs1 = Z_to_bv 64 ip -> xs7 = Z_to_bv 64 (OENDW - op) -> xs6 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 124168 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    induction q as [|q IH]; intros until x31; intros I H1 H2 HQ H3 H4 H5 -> -> -> -> -> -> -> ->; open_sci I;
      itm dd (dd + (ip - op)); br K4;
      [exfalso; lia | use (sc_1016 _ op ip) | use (IH _ (dd + 32) op ip) | use (sc_1016 _ op ip)].
  Qed.

  Lemma sc_wl1 : forall (q : nat) m1 (dd d : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> OP < dd < OP + LEN -> OP + LEN <= OENDW -> OP + LEN - dd <= 32 * (Z.of_nat q + 1) ->
    R0 <= dd + d -> OP + LEN + 32 + d <= R1 ->
    xs2 = Z_to_bv 64 dd -> xs0 = Z_to_bv 64 (dd + d + 16) -> xs4 = Z_to_bv 64 (-17) -> xs3 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 124044 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    induction q as [|q IH]; intros until x31; intros I H1 H2 HQ H3 H4 -> -> -> ->; open_sci I;
      itm dd (dd + d); br K4;
      [exfalso; lia | zstep; use sc_epi | use (IH _ (dd + 32) d) | zstep; use sc_epi].
  Qed.

  Lemma sc_896 : forall m1 (op ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> OP <= op <= OENDW -> R0 <= ip -> OENDW + 32 + (ip - op) <= R1 -> OP + LEN + (ip - op) <= R1 ->
    xs0 = Z_to_bv 64 op -> xs1 = Z_to_bv 64 ip -> xs7 = Z_to_bv 64 (OENDW - op) -> xs2 = Z_to_bv 64 OENDW ->
    xs6 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 124116 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I H1 H2 H3 H4 -> -> -> -> ->; open_sci I.
    zstep. zstep. zstep. zstep. mv op ip. zstep. zstep. br K.
    - use (sc_1016 _ op ip).
    - zstep. ub K1. zstep. zstep. ub K2. zstep. ub K3. zstep. zstep. zstep.
      use (sc_wl2 (Z.to_nat (OENDW - op)) _ (op + 16) op ip).
  Qed.

  Lemma sc_768 : forall m1 (op ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> OP <= op <= OP + LEN -> OP + LEN <= OENDW -> R0 <= ip -> OP + LEN + 32 + (ip - op) <= R1 ->
    xs0 = Z_to_bv 64 op -> xs1 = Z_to_bv 64 ip -> xa3 = Z_to_bv 64 (OP + LEN - op) -> xs3 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 123988 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I H1 H2 H3 H4 -> -> -> ->; open_sci I.
    zstep. zstep. zstep. zstep. zstep. mv op ip. zstep. zstep. br K.
    - use sc_epi.
    - zstep. ub K1. zstep. zstep. ub K2. zstep. ub K3. zstep. zstep. zstep.
      use (sc_wl1 (Z.to_nat (OP + LEN - op)) _ (op + 16) (ip - op)).
  Qed.

  Lemma sc_620 : forall m1 (op ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> OP <= op <= OP + LEN -> OP + LEN <= OENDW -> R0 <= ip -> OP + LEN + 32 + (ip - op) <= R1 -> 0 <= OV <= 1 ->
    xs0 = Z_to_bv 64 op -> xs1 = Z_to_bv 64 ip -> xa3 = Z_to_bv 64 (OP + LEN - op) -> xa4 = Z_to_bv 64 OV ->
    evt usegs POST (ST 123840 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I H1 H2 H3 H4 H5 -> -> -> ->.
    zstep. zstep. ub K. zstep. zstep. zstep. zstep. ub K1.
    zstep. br K2; [use (sc_768 _ op ip)|].
    zstep. zstep. zstep. br K3; [use (sc_768 _ op ip)|].
    zstep. zstep. zstep. use (sc_w8b (Z.to_nat (OP + LEN - op)) _ op (ip - op)).
  Qed.

  Lemma sc_460 : forall m1 (op ip : Z) xra x5 x6 x7 xa0 xa1 xa2 xa5 xa6 xa7 xs3 xs4 xs5 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> OP <= op <= OP + LEN -> R0 <= ip ->
    ((OV = 1 /\ ip + 8 <= op) \/ (OV = 0 /\ ip - op = IP - OP)) ->
    evt usegs POST (ST 123680 m1 xra x5 x6 x7 (Z_to_bv 64 op) (Z_to_bv 64 ip) xa0 xa1 xa2 (Z_to_bv 64 (OP + LEN - op)) (Z_to_bv 64 OV) xa5 xa6 xa7
                       (Z_to_bv 64 OENDW) xs3 xs4 xs5 (Z_to_bv 64 (OP + LEN)) xs7 xs8 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I H1 H2 HV.
    pose proof sc_ovf as OF.
    assert (F3 : OP + LEN + (ip - op) <= R1)
      by (destruct HV as [(? & ?)|(? & ?)]; destruct OF as [(? & ? & ?)|(? & ?)]; lia).
    assert (F1 : OENDW < OP + LEN -> OENDW + 32 + (ip - op) <= R1)
      by (intro; destruct HV as [(? & ?)|(? & ?)]; destruct OF as [(? & ? & ?)|(? & ?)]; lia).
    assert (F2 : OP + LEN <= OENDW -> OP + LEN + 32 + (ip - op) <= R1)
      by (intro; destruct HV as [(? & ?)|(? & ?)]; destruct OF as [(? & ? & ?)|(? & ?)]; lia).
    assert (F4 : 0 <= OV <= 1) by (destruct HV as [(? & ?)|(? & ?)]; lia).
    clear HV OF.
    zstep. br K.
    - pose proof (F2 ltac:(lia)) as F5. use (sc_620 _ op ip).
    - pose proof (F1 ltac:(lia)) as F5. zstep. zstep. br K1.
      + use (sc_1048 _ op op ip).
      + zstep. zstep. zstep. ub K2. zstep. zstep. br K3.
        * use (sc_896 _ op ip).
        * zstep. zstep. zstep. br K4.
          -- use (sc_896 _ op ip).
          -- zstep. zstep. zstep. zstep. zstep. use (sc_w8a (Z.to_nat (OENDW - op)) _ op op ip).
  Qed.
End Hi.
