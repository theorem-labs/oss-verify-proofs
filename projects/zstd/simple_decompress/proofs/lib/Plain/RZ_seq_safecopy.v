(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac MemRange.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memmove RZ_seq_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Proofs.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo OP OENDW IP LEN B0 B1 : Z).
  Hypothesis B0L : 4096 <= B0.
  Hypothesis B1H : B1 < 2^47.
  Hypothesis IPOP : B0 <= IP <= OP.
  Hypothesis LEN0 : 0 <= LEN.
  Hypothesis OPL : OP + LEN <= B1.
  Hypothesis OW0 : 0 <= OENDW.
  Hypothesis OWH : OENDW + 32 <= B1.
  Hypothesis LOS : lo <= SPV - 64.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SPR : 0 <= SPV < 2^47.
  Hypothesis OFFS : B0 + (B1 - B0) <= lo \/ SPV <= B0.

  Notation POST := (zd_safecopy_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP B0 B1 lo m).
  (* [comment removed for export] *)
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -64)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  (* [comment removed for export] *)
  Definition SCI (m1 : fmem) : Prop :=
    stk psegs m1 B0 B1 /\ stk psegs m1 lo (SPV + -64)
    /\ (exists j0, rw_cells psegs m1 (SPV + -64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ mem_inv psegs m1 /\ munch [(OP, B1); (SPV - 64, SPV)] m m1 /\ wmono psegs m m1.
  Ltac open_sci I := destruct I as (REG & STK & [j0 FR] & MI & MU & WM).
  Ltac close_sci := split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|]; split; eassumption.

  (* [comment removed for export] *)
  Lemma sc_epi : forall m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31,
    SCI m1 -> evt psegs POST (ST 0x1c6d4 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I. open_sci I.
    do 7 zstep. zstep.
    release_frame FR STK SPV.
    zstep. finish2.
  Qed.

  (* [comment removed for export] *)
  Ltac ldr REG A k :=
    lazymatch type of REG with stk ?segs ?m1 ?b0 ?b1 =>
      let a := cur_mem_addr in
      let bs := fresh "bs" in let RD := fresh "RD" in let L := fresh "L" bs in
      destruct (stk_read_at segs m1 b0 b1 A k a REG ltac:(lia) ltac:(lia) ltac:(addr_tac)) as [bs [L RD]];
      zstep; try clear RD
    end.
  Ltac str REG A k :=
    lazymatch type of REG with stk ?segs ?m1 ?b0 ?b1 =>
      let a := cur_mem_addr in
      let SOK := fresh "SOK" in
      pose proof (stk_store_ok_at segs m1 b0 b1 A k a REG ltac:(lia) ltac:(lia) ltac:(addr_tac)) as SOK;
      zstep; store_done
    end.
  Tactic Notation "use" uconstr(L) :=
    eapply L; first [ eassumption | close_sci | idtac ]; try (f_equal; lia); try lia.

  (* [comment removed for export] *)
  Lemma sc_tail_loop : forall (k : nat) m1 (op ip oend : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31,
    SCI m1 -> OP <= op -> B0 <= ip <= op -> oend <= B1 -> op + Z.of_nat k + 1 = oend ->
    xa0 = Z_to_bv 64 op -> xs0 = Z_to_bv 64 ip -> xs4 = Z_to_bv 64 oend ->
    evt psegs POST (ST 0x1c6bc m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I HOP HIP HEND HK -> -> ->; open_sci I.
    - ldr REG ip 1%nat. zstep. zstep. str REG op 1%nat. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      use sc_epi.
    - ldr REG ip 1%nat. zstep. zstep. str REG op 1%nat. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      use (IH _ (op + 1) (ip + 1) oend).
  Qed.

  (* [comment removed for export] *)
  Lemma sc_tail : forall m1 (op ip oend : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31,
    SCI m1 -> OP <= op <= B1 -> B0 <= ip <= op -> OP <= oend <= B1 ->
    xa0 = Z_to_bv 64 op -> xs0 = Z_to_bv 64 ip -> xs4 = Z_to_bv 64 oend ->
    evt psegs POST (ST 0x1c6b8 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HOP HIP HEND -> -> ->.
    zstep. if_cases K; zify_cond K.
    - use sc_epi.
    - use (sc_tail_loop (Z.to_nat (oend - op - 1)) _ op ip oend).
  Qed.

  (* [comment removed for export] *)
  Ltac cp8 REG ip op :=
    ldr REG ip 1%nat; ldr REG (ip + 1) 1%nat; ldr REG (ip + 2) 1%nat; ldr REG (ip + 3) 1%nat;
    ldr REG (ip + 4) 1%nat; ldr REG (ip + 5) 1%nat; ldr REG (ip + 6) 1%nat; ldr REG (ip + 7) 1%nat;
    str REG (op + 4) 1%nat; str REG (op + 5) 1%nat; str REG (op + 6) 1%nat; str REG (op + 7) 1%nat;
    str REG op 1%nat; str REG (op + 1) 1%nat; str REG (op + 2) 1%nat; str REG (op + 3) 1%nat.

  (* [comment removed for export] *)
  Lemma sc_w1a : forall (q : nat) m1 (op ip oend : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31,
    SCI m1 -> OP <= op <= oend -> B0 <= ip <= op -> oend + 32 <= B1 -> oend - op <= 8 * (Z.of_nat q + 1) ->
    xa0 = Z_to_bv 64 op -> xs0 = Z_to_bv 64 ip -> xs2 = Z_to_bv 64 oend ->
    evt psegs POST (ST 0x1c5c0 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31).
  Proof.
    induction q as [|q IH]; intros until x31; intros I HOP HIP HEND HQ -> -> ->; open_sci I.
    - cp8 REG ip op. zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|]. zstep. use sc_epi.
    - cp8 REG ip op. zstep. zstep. zstep. if_cases K; zify_cond K.
      + use (IH _ (op + 8) (ip + 8) oend).
      + zstep. use sc_epi.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_w2_exit : forall m1 (op0 ip0 : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31,
    SCI m1 -> OP <= op0 <= OENDW -> B0 <= ip0 <= op0 ->
    xs0 = Z_to_bv 64 ip0 -> xs5 = Z_to_bv 64 (OENDW - op0) -> xs1 = Z_to_bv 64 OENDW -> xs4 = Z_to_bv 64 (OP + LEN) ->
    evt psegs POST (ST 0x1c6b0 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HOP HIP -> -> -> ->.
    zstep. zstep. use (sc_tail _ OENDW (ip0 + (OENDW - op0)) (OP + LEN)).
  Qed.

  (* [comment removed for export] *)
  Lemma sc_w2a : forall (q : nat) m1 (op ip op0 ip0 : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31,
    SCI m1 -> OP <= op <= OENDW -> B0 <= ip <= op -> OP <= op0 <= OENDW -> B0 <= ip0 <= op0 -> OENDW - op <= 8 * (Z.of_nat q + 1) ->
    xa0 = Z_to_bv 64 op -> xa1 = Z_to_bv 64 ip ->
    xs0 = Z_to_bv 64 ip0 -> xs5 = Z_to_bv 64 (OENDW - op0) -> xs1 = Z_to_bv 64 OENDW -> xs4 = Z_to_bv 64 (OP + LEN) ->
    evt psegs POST (ST 0x1c55c m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31).
  Proof.
    induction q as [|q IH]; intros until x31; intros I HOP HIP HOP0 HIP0 HQ -> -> -> -> -> ->; open_sci I.
    - cp8 REG ip op. zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|]. zstep. use (sc_w2_exit _ op0 ip0).
    - cp8 REG ip op. zstep. zstep. zstep. if_cases K; zify_cond K.
      + use (IH _ (op + 8) (ip + 8) op0 ip0).
      + zstep. use (sc_w2_exit _ op0 ip0).
  Qed.

  (* [comment removed for export] *)
  Ltac mmv d sr :=
    lazymatch goal with REG : stk psegs ?m1 B0 B1 |- _ =>
      eapply evt_cut;
      [ eapply memmove_reg_spec with (D := d) (S := sr) (n := 16) (B0 := B0) (B1 := B1) (R0 := B0) (R1 := B1);
        [ exact REG | apply rdbl_of_stk; exact REG | lia | eassumption | try reflexivity; f_equal; lia | try reflexivity; f_equal; lia | reflexivity ]
      | post_call psegs m1 ]
    end;
    lazymatch goal with H : stk psegs _ B0 B1, H2 : rdbl psegs _ B0 B1 |- _ => clear H2; rename H into REG end.

  (* [comment removed for export] *)
  Lemma sc_w1b_loop : forall (q : nat) m1 (d sr oend : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31,
    SCI m1 -> OP <= d < oend -> B0 <= sr <= d -> oend + 32 <= B1 -> oend - d <= 32 * (Z.of_nat q + 1) ->
    xs1 = Z_to_bv 64 d -> xs0 = Z_to_bv 64 (sr + 16) -> xs2 = Z_to_bv 64 oend ->
    evt psegs POST (ST 0x1c634 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31).
  Proof.
    induction q as [|q IH]; intros until x31; intros I HD HS HEND HQ -> -> ->; open_sci I.
    - zstep. zstep. zstep. zstep. mmv d sr. zstep. zstep. zstep. zstep. mmv (d + 16) (sr + 16).
      zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|]. zstep. use sc_epi.
    - zstep. zstep. zstep. zstep. mmv d sr. zstep. zstep. zstep. zstep. mmv (d + 16) (sr + 16).
      zstep. zstep. zstep. if_cases K; zify_cond K.
      + use (IH _ (d + 32) (sr + 32) oend).
      + zstep. use sc_epi.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_w1b : forall m1 (op ip len' : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31,
    SCI m1 -> OP <= op -> B0 <= ip <= op -> 0 <= len' -> op + len' + 32 <= B1 ->
    xa0 = Z_to_bv 64 op -> xs0 = Z_to_bv 64 ip -> xa3 = Z_to_bv 64 len' -> xs2 = Z_to_bv 64 (op + len') ->
    evt psegs POST (ST 0x1c610 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HOP HIP HL HEND -> -> -> ->; open_sci I.
    zstep. zstep. zstep. zstep. zstep. mmv op ip.
    zstep. zstep. if_cases K; zify_cond K.
    - use sc_epi.
    - zstep. zstep. use (sc_w1b_loop (Z.to_nat len') _ (op + 16) (ip + 16) (op + len')).
  Qed.

  (* [comment removed for export] *)
  Lemma sc_w2b_loop : forall (q : nat) m1 (d sr op0 ip0 : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31,
    SCI m1 -> OP <= d < OENDW -> B0 <= sr <= d -> OP <= op0 <= OENDW -> B0 <= ip0 <= op0 -> OENDW - d <= 32 * (Z.of_nat q + 1) ->
    xs2 = Z_to_bv 64 d -> xs3 = Z_to_bv 64 (sr + 16) ->
    xs0 = Z_to_bv 64 ip0 -> xs5 = Z_to_bv 64 (OENDW - op0) -> xs1 = Z_to_bv 64 OENDW -> xs4 = Z_to_bv 64 (OP + LEN) ->
    evt psegs POST (ST 0x1c684 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31).
  Proof.
    induction q as [|q IH]; intros until x31; intros I HD HS HOP0 HIP0 HQ -> -> -> -> -> ->; open_sci I.
    - zstep. zstep. zstep. zstep. mmv d sr. zstep. zstep. zstep. zstep. mmv (d + 16) (sr + 16).
      zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|]. use (sc_w2_exit _ op0 ip0).
    - zstep. zstep. zstep. zstep. mmv d sr. zstep. zstep. zstep. zstep. mmv (d + 16) (sr + 16).
      zstep. zstep. zstep. if_cases K; zify_cond K.
      + use (IH _ (d + 32) (sr + 32) op0 ip0).
      + use (sc_w2_exit _ op0 ip0).
  Qed.

  (* [comment removed for export] *)
  Lemma sc_w2b : forall m1 (op ip : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31,
    SCI m1 -> OP <= op <= OENDW -> B0 <= ip <= op ->
    xa0 = Z_to_bv 64 op -> xs0 = Z_to_bv 64 ip -> xs5 = Z_to_bv 64 (OENDW - op) -> xs1 = Z_to_bv 64 OENDW -> xs4 = Z_to_bv 64 (OP + LEN) ->
    evt psegs POST (ST 0x1c664 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HOP HIP -> -> -> -> ->; open_sci I.
    zstep. zstep. zstep. zstep. mmv op ip.
    zstep. zstep. if_cases K; zify_cond K.
    - use (sc_w2_exit _ op ip).
    - zstep. zstep. use (sc_w2b_loop (Z.to_nat (OENDW - op)) _ (op + 16) (ip + 16) op ip).
  Qed.

  (* [comment removed for export] *)
  Lemma sc_j1 : forall m1 (op ip len' : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31,
    SCI m1 -> OP <= op -> B0 <= ip <= op -> 0 <= len' -> op + len' = OP + LEN ->
    xa0 = Z_to_bv 64 op -> xs0 = Z_to_bv 64 ip -> xa3 = Z_to_bv 64 len' -> xa4 = Z_to_bv 64 1 ->
    xs1 = Z_to_bv 64 OENDW -> xs4 = Z_to_bv 64 (OP + LEN) ->
    evt psegs POST (ST 0x1c53c m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HOP HIP HL HE -> -> -> -> -> ->.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + use (sc_w1b _ op ip len').
      + use (sc_w1a (Z.to_nat len') _ op ip (op + len')).
    - zstep. if_cases K1; zify_cond K1.
      + use (sc_tail _ op ip (OP + LEN)).
      + zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
        zstep. zstep. zstep. if_cases K3; zify_cond K3.
        * use (sc_w2b _ op ip).
        * zstep. use (sc_w2a (Z.to_nat (OENDW - op)) _ op ip op ip).
  Qed.

  Tactic Notation "useE" uconstr(L) :=
    eapply L; [ first [ eassumption | close_sci ] | .. ];
    try (lazymatch goal with |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity end); try lia.

  (* [comment removed for export] *)
  Lemma sc_first8 : forall m1 xra x5 x6 x7 xa1 xa2 xa5 xa6 xa7 xs2 xs3 xs5 x28 x29 x30 x31,
    SCI m1 -> 8 <= LEN ->
    evt psegs POST (ST 0x1c4f0 m1 xra x5 x6 x7 (Z_to_bv 64 IP) (Z_to_bv 64 OENDW) (Z_to_bv 64 OP) xa1 xa2 (Z_to_bv 64 LEN) (Z_to_bv 64 1) xa5 xa6 xa7
                       xs2 xs3 (Z_to_bv 64 (OP + LEN)) xs5 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HL; open_sci I.
    cp8 REG IP OP. zstep. zstep. zstep.
    use (sc_j1 _ (OP + 8) (IP + 8) (LEN - 8)).
  Qed.

  (* [comment removed for export] *)
  Ltac ldra REG k := let a := cur_mem_addr in lazymatch a with Z_to_bv 64 ?E => ldr REG E k end.
  Ltac stra REG k := let a := cur_mem_addr in lazymatch a with Z_to_bv 64 ?E => str REG E k end.

  (* [comment removed for export] *)
  Lemma sc_ovl8 : forall (dz : Z) m1 xra x5 x6 x7 xa2 xa5 xa6 xa7 xs2 xs3 xs5 x28 x29 x30 x31,
    SCI m1 -> 8 <= LEN -> 0 <= dz <= 7 -> OP = IP + dz ->
    evt psegs POST (ST 0x1c480 m1 xra x5 x6 x7 (Z_to_bv 64 IP) (Z_to_bv 64 OENDW) (Z_to_bv 64 OP) (Z_to_bv 64 dz) xa2 (Z_to_bv 64 LEN) (Z_to_bv 64 1) xa5 xa6 xa7
                       xs2 xs3 (Z_to_bv 64 (OP + LEN)) xs5 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HL HD HOP; open_sci I.
    assert (C : dz = 0 \/ dz = 1 \/ dz = 2 \/ dz = 3 \/ dz = 4 \/ dz = 5 \/ dz = 6 \/ dz = 7) by lia.
    destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
    all: zstep; zstep; ldra REG 1%nat; zstep; zstep; zstep; stra REG 1%nat; ldra REG 1%nat; stra REG 1%nat; ldra REG 1%nat; stra REG 1%nat;
         ldra REG 1%nat; zstep; zstep; zstep; stra REG 1%nat; zstep; zstep;
         ldra REG 1%nat; ldra REG 1%nat; ldra REG 1%nat; ldra REG 1%nat; stra REG 1%nat; stra REG 1%nat; stra REG 1%nat; stra REG 1%nat;
         zstep; zstep; zstep; zstep; zstep.
    all: useE (sc_j1 _).
  Qed.

  (* [comment removed for export] *)
  Lemma sc_short_loop : forall (k : nat) m1 (op ip oend : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31,
    SCI m1 -> OP <= op -> B0 <= ip <= op -> oend <= B1 -> op + Z.of_nat k + 1 = oend ->
    xa0 = Z_to_bv 64 op -> xs0 = Z_to_bv 64 ip -> xs4 = Z_to_bv 64 oend ->
    evt psegs POST (ST 0x1c454 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I HOP HIP HEND HK -> -> ->; open_sci I.
    - ldr REG ip 1%nat. zstep. zstep. str REG op 1%nat. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. use sc_epi.
    - ldr REG ip 1%nat. zstep. zstep. str REG op 1%nat. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      use (IH _ (op + 1) (ip + 1) oend).
  Qed.

  (* [comment removed for export] *)
  Lemma sc_main : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    stk psegs m B0 B1 -> stk psegs m lo SPV -> mem_inv psegs m ->
    evt psegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OP) (Z_to_bv 64 OENDW) (Z_to_bv 64 IP) (Z_to_bv 64 LEN) (Z_to_bv 64 1) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1c41c) fc None m (seg_rom psegs)).
  Proof.
    intros until t6. intros REG STK MI.
    assert (MU : munch [(OP, B1); (SPV - 64, SPV)] m m) by apply munch_refl.
    assert (WM : wmono psegs m m) by apply wmono_refl.
    zstep. carve_frame 64%nat STK.
    do 7 zstep. zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + use sc_first8.
      + use (sc_ovl8 (OP - IP)).
    - zstep. if_cases K1; zify_cond K1.
      + use sc_epi.
      + use (sc_short_loop (Z.to_nat (LEN - 1)) _ OP IP (OP + LEN)).
  Qed.
End Proofs.

Theorem zd_safecopy_proof : zd_safecopy_stmt.
Proof.
  unfold zd_safecopy_stmt, PZD_SAFECOPY. intros until B1. intros REG B0L B1H IPOP LEN0 OPL OW0 OWH STK LOS SPR OFFS MI -> -> -> -> ->.
  unfold off_stack in OFFS. pose proof STK as (LO0 & _ & _).
  eapply sc_main; eassumption.
Qed.
