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

Section Lo.
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

  Hypothesis H460 : forall m1 (op ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> OP <= op <= OP + LEN -> R0 <= ip ->
    ((OV = 1 /\ ip + 8 <= op) \/ (OV = 0 /\ ip - op = IP - OP)) ->
    xs0 = Z_to_bv 64 op -> xs1 = Z_to_bv 64 ip -> xa3 = Z_to_bv 64 (OP + LEN - op) -> xa4 = Z_to_bv 64 OV ->
    xs2 = Z_to_bv 64 OENDW -> xs6 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 0x1e320 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).

  Lemma scl_ipl : IP + LEN <= R1.
  Proof. pose proof OVC as C. unfold sc_ovc in C. destruct C as [(_ & _ & E & H)|(_ & H & _)]; lia. Qed.
  Lemma scl_ovr : OV = 0 \/ OV = 1.
  Proof. pose proof OVC as C. unfold sc_ovc in C. destruct C as [(E & _)|(E & _)]; lia. Qed.
  Lemma scl_ov1 : OV <> 0 -> OV = 1 /\ R0 = B0 /\ R1 = B1 /\ IP <= OP.
  Proof. intros N. pose proof OVC as C. unfold sc_ovc in C. destruct C as [H|(E & _)]; [exact H| lia]. Qed.

  Ltac ldR A k :=
    lazymatch goal with REG : stk usegs ?m1 B0 B1, MU : munch _ m ?m1 |- _ =>
      let RD := fresh "RD" in let IPL := fresh "IPL" in
      pose proof (sc_rd m m1 SPV lo OP OENDW LEN B0 B1 R0 R1 RDM OPB OPL OWH LOS OFFR MU REG) as RD;
      pose proof scl_ipl as IPL;
      ldRd RD A k; try clear RD IPL
    end.
  Ltac ldra k := let a := cur_mem_addr in lazymatch a with Z_to_bv 64 ?E => ldR E k end.
  Ltac stra k := let a := cur_mem_addr in lazymatch a with Z_to_bv 64 ?E => lazymatch goal with REG : stk usegs _ B0 B1 |- _ => str REG E k end end.
  Ltac ubq H := first [ ub H | idtac ].

  Lemma sc_short_loop : forall (k : nat) m1 (op ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> OP <= op -> ip - op = IP - OP -> op + Z.of_nat k + 1 = OP + LEN ->
    xs0 = Z_to_bv 64 op -> xs1 = Z_to_bv 64 ip -> xa0 = Z_to_bv 64 2 -> xa1 = Z_to_bv 64 ip -> xa2 = Z_to_bv 64 op ->
    xa3 = Z_to_bv 64 (Z.of_nat k + 1) ->
    evt usegs POST (ST 0x1e1bc m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I HOP HIP HK -> -> -> -> -> ->; open_sci I; pose proof scl_ipl as IPL0.
    - zstep. zstep. ub K. zstep. zstep. ub K1. ldR ip 1%nat. str REG op 1%nat. zstep. zstep. zstep. zstep.
      br K2; [exfalso; lia|]. zstep. use sc_epi.
    - zstep. zstep. ub K. zstep. zstep. ub K1. ldR ip 1%nat. str REG op 1%nat. zstep. zstep. zstep. zstep.
      br K2; [|exfalso; lia]. use (IH _ (op + 1) (ip + 1)).
  Qed.

  Lemma sc_432 : forall m1 (ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> 8 <= LEN -> OV = 1 -> R0 <= ip + 8 -> ip + 8 <= OP ->
    xs0 = Z_to_bv 64 OP -> xs1 = Z_to_bv 64 ip -> xa3 = Z_to_bv 64 LEN -> xa4 = Z_to_bv 64 OV ->
    xs2 = Z_to_bv 64 OENDW -> xs6 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 0x1e304 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HL HO1 HR HD -> -> -> -> -> ->.
    zstep. zstep. zstep. ub K. zstep. zstep. ub K1. zstep. zstep.
    use (H460 _ (OP + 8) (ip + 8)).
  Qed.

  Lemma sc_copy8 : forall m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> 8 <= LEN -> OV <> 0 -> IP + 8 <= OP ->
    xs0 = Z_to_bv 64 OP -> xs1 = Z_to_bv 64 IP -> xa3 = Z_to_bv 64 LEN -> xa4 = Z_to_bv 64 OV ->
    xs2 = Z_to_bv 64 OENDW -> xs6 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 0x1e2c4 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HL HOV HD -> -> -> -> -> ->.
    pose proof (scl_ov1 HOV) as (HO1 & HR0 & HR1 & HIO). open_sci I.
    ldR IP 1%nat. ldR (IP + 1) 1%nat. ldR (IP + 2) 1%nat. ldR (IP + 3) 1%nat.
    ldR (IP + 4) 1%nat. ldR (IP + 5) 1%nat. ldR (IP + 6) 1%nat. ldR (IP + 7) 1%nat.
    str REG (OP + 4) 1%nat. str REG (OP + 5) 1%nat. str REG (OP + 6) 1%nat. str REG (OP + 7) 1%nat.
    str REG OP 1%nat. str REG (OP + 1) 1%nat. str REG (OP + 2) 1%nat. str REG (OP + 3) 1%nat.
    use (sc_432 _ IP).
  Qed.

  Lemma sc_tbl : forall (dz : Z) m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31,
    SCI m1 -> 8 <= LEN -> OV <> 0 -> 0 <= dz <= 7 -> OP = IP + dz ->
    xs0 = Z_to_bv 64 OP -> xs1 = Z_to_bv 64 IP -> xa1 = Z_to_bv 64 dz -> xa3 = Z_to_bv 64 LEN -> xa4 = Z_to_bv 64 OV ->
    xs2 = Z_to_bv 64 OENDW -> xs6 = Z_to_bv 64 (OP + LEN) ->
    evt usegs POST (ST 0x1e1f8 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HL HOV HD HOP -> -> HA1 -> -> -> ->.
    pose proof (scl_ov1 HOV) as (HO1 & HR0 & HR1 & HIO). open_sci I.
    assert (C : dz = 0 \/ dz = 1 \/ dz = 2 \/ dz = 3 \/ dz = 4 \/ dz = 5 \/ dz = 6 \/ dz = 7) by lia.
    destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; subst xa1.
    all: zstep; zstep; zstep; zstep; zstep; ubq K; zstep; ub K1; zstep; ub K2; zstep;
         ldra 1%nat; zstep; zstep; zstep; stra 1%nat; zstep; ub K3; zstep; zstep; ub K4;
         ldra 1%nat; zstep; stra 1%nat; zstep; ub K5; zstep; ub K6;
         ldra 1%nat; zstep; stra 1%nat; zstep; ub K7; zstep; ub K8;
         ldra 1%nat; zstep; zstep; zstep; stra 1%nat; zstep; ubq K9; zstep; zstep; zstep; zstep; rewrite ?zb_lxor_ones by lia; ub K10; zstep; zstep; ub K11;
         zstep; ldra 1%nat; ldra 1%nat; ldra 1%nat; ldra 1%nat; stra 1%nat; stra 1%nat; stra 1%nat; stra 1%nat;
         zstep; ub K12; zstep; zstep; br K13; [| exfalso; lia].
    all: eapply sc_432; first [ reflexivity | eassumption | close_sci | idtac ].
    all: try (f_equal; lia); try lia.
  Qed.

  Lemma sc_main : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    stk usegs m B0 B1 -> stk usegs m lo SPV -> mem_inv usegs m ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OP) (Z_to_bv 64 OENDW) (Z_to_bv 64 IP) (Z_to_bv 64 LEN) (Z_to_bv 64 OV)
               a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e154) fc None m (seg_rom usegs)).
  Proof.
    intros until t6. intros REG STK MI.
    assert (MU : munch [(OP, Z.max (OP + LEN) (OENDW + 32)); (SPV - 80, SPV)] m m) by apply munch_refl.
    assert (WM : wmono usegs m m) by apply wmono_refl.
    pose proof scl_ipl as IPL. pose proof scl_ovr as OVR.
    zstep. carve_frame 80%nat STK.
    do 10 zstep. zstep. zstep. ub K.
    zstep. zstep. zstep. zstep. zstep. zstep. ub K1.
    zstep. zstep. zstep. br K2.
    - zstep. br K3.
      + use (H460 _ OP IP).
      + pose proof (scl_ov1 ltac:(lia)) as (HO1 & HR0 & HR1 & HIO).
        zstep. zstep. zstep. br K4.
        * use sc_copy8.
        * use (sc_tbl (OP - IP)).
    - zstep. br K5.
      + use sc_epi.
      + zstep. zstep. zstep. use (sc_short_loop (Z.to_nat (LEN - 1)) _ OP IP).
  Qed.
End Lo.
