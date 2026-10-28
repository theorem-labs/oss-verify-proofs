(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_frame_iface AZ_libc_iface AZ_kx AZ_globals AZ_globalsR AZ_findfsi_a AZ_findfsi_b AZ_finddsize_a.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).
Notation FB1 F := (mkABlock (ABFake 1) F 128).
Notation SHB := 2147450880.
Notation KM8 := 18446744073709551608.
Notation K9 := 4294967287.
Notation KSK := (Z_to_bv 64 25481893).

Section CANSEC1. Context {rc : runConstT}.

Section FD.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 : amem) (SPV SPA SRC : Z) (src : list Z) (size0 lo FF SHF FLG : Z).
  (* [comment removed for export] *)
  Hypothesis OK : all_bytes src.
  Hypothesis N0 : 0 <= size0.
  Hypothesis N40 : size0 < 1099511627776.
  Hypothesis NLEN : size0 <= zlen src.
  Hypothesis SRCE : SRC + zlen src < 2^64.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPA - 4672 /\ SPV - 208 <= SPA <= SPV - 192 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis G_src : ablk SRC (SRC + zlen src) /\ (SRC + zlen src <= lo \/ SPV <= SRC).
  Hypothesis G_ff : ablk FF (FF + 128) /\ FF mod 128 = 0 /\ FF + 128 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 128 <= al_fake L + FAKESZ
                    /\ (SRC + zlen src <= FF \/ FF + 128 <= SRC).
  Hypothesis G_flg : FLG = fflag L 1 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB1 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)).
  Hypothesis R_ff : rng RNG FF 128 /\ rng RNG SHF 16 /\ rng RNG FLG 1.
  Hypothesis R_fsi : rng RNG (shad (SPA + 64)) (shspan (SPA + 64) 24).
  Hypothesis LBH : ablkLB LB.
  (* [comment removed for export] *)
  Variable SZB : Z.

  Notation POST := (zd_finddsize_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV src size0 lo m0).
  Notation RES := (find_decompressed_size src size0).
  Notation BINV := (AZ_finddsize_a.BINV AI L RNG st LB m0 SPV FF).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 (Z_to_bv 64 SHF) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) (Z_to_bv 64 KM8) x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition XINVg (sh : list cell) (m1 : amem) : Prop :=
    BINV m1 /\ rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ (exists jA, rw_cells bsegs m1 SPA [CB 16 jA; C8 (Z_to_bv 64 FF)])
    /\ (exists jB, rw_cells bsegs m1 (SPA + 24) [C8 (Z_to_bv 64 K9); CB 24 jB; C8 (Z_to_bv 64 FF)])
    /\ (exists jC, rw_cells bsegs m1 (SPA + 64) [CB 24 jC])
    /\ stk bsegs m1 lo SPA /\ stk bsegs m1 (SPA + 88) (SPV + -104)
    /\ (exists j, rw_cells bsegs m1 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20338); C8 (Z_to_bv 64 0x83c6c); CB 96 j; C8 (Z_to_bv 64 FLG)])
    /\ rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m1 SHF sh
    /\ bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) /\ unpoisoned m1 SRC (SRC + zlen src)
    /\ unpoisoned m1 (SPA + 64) (SPA + 88) /\ aro_client RNG m1.
  Notation XINV := (XINVg DSH0).

  (* [comment removed for export] *)
  Hypothesis PEXIT : forall m1 r jA csB csC w0 shb (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x27 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 16 jA; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m1 (SPA + 24) csB -> cells_size csB = 40%nat -> rw_cells bsegs m1 (SPA + 64) csC -> cells_size csC = 24%nat ->
    stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 88) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 120) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 16 shb] ->
    Z_to_bv 64 r = Z_to_bv 64 RES ->
    evtF bsegs RNG POST (STpc 0x83dac m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 r) x27 x28 x29 x30 x31).
  Hypothesis PHERR : forall m1 jA csB csC w0 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 16 jA; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m1 (SPA + 24) csB -> cells_size csB = 40%nat -> rw_cells bsegs m1 (SPA + 64) csC -> cells_size csC = 24%nat ->
    stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 88) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 120) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF DSHZ ->
    RES = ZD_CONTENTSIZE_ERROR ->
    evtF bsegs RNG POST (STpc 0x84074 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31).
  Hypothesis PADV : forall m1 off sz step total (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    XINV m1 -> 8 <= step <= sz -> 0 <= off -> off + sz <= size0 ->
    RES = find_dsize src (off + step) (sz - step) total -> 0 <= total < 18446744073709551616 -> sz <= SZB ->
    evtF bsegs RNG POST (STpc 0x83e30 m1 x1 x5 x6 x7 (Z_to_bv 64 step) x11 x12 x13 x14 x15 x16 x17 KSK (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (FF + 32))
                              x22 (Z_to_bv 64 total) x28 x29 x30 x31).
  Hypothesis PREG : forall m1 off sz total (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    XINV m1 -> 5 <= sz -> 0 <= off -> off + sz <= size0 ->
    RES = find_dsize src off sz total -> 0 <= total < 18446744073709551616 -> is_skippable_magic (le32 src off) = false -> sz <= SZB ->
    evtF bsegs RNG POST (STpc 0x83f04 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 KSK (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (FF + 32))
                              x22 (Z_to_bv 64 total) x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma p_xexit : forall sh m1 r (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x27 x28 x29 x30 x31 : word),
    XINVg sh m1 -> cells_size sh = 16%nat -> Z_to_bv 64 r = Z_to_bv 64 RES ->
    evtF bsegs RNG POST (STpc 0x83dac m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 r) x27 x28 x29 x30 x31).
  Proof.
    intros sh m1 r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x27 x28 x29 x30 x31
           (BI & SAV & [jA FRA] & [jB FRB] & [jC FRC] & STL & STG & [jH XH] & XL & XS & SB1 & US & UP & ARO) SZ ER.
    destruct (rw_cells_forget _ _ _ _ XS) as [shb XS']. rewrite SZ in XS'.
    pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3)] _) XH)) as XM.
    pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20338); C8 (Z_to_bv 64 0x83c6c); CB 96 jH] _) XH)) as XP.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XP.
    match type of XP with rw_cells _ _ ?a _ => replace a with (FF + 120) in XP by (clear; lia) end.
    eapply (PEXIT m1 r jA _ _ _ shb); [exact BI | exact SAV | exact FRA | exact FRB | reflexivity | exact FRC | reflexivity | exact STL | exact STG
                                      | exact XM | exact XP | exact XL | exact XS' | exact ER].
  Qed.

  Lemma p_xherr : forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31 : word),
    XINVg DSHZ m1 -> RES = ZD_CONTENTSIZE_ERROR ->
    evtF bsegs RNG POST (STpc 0x84074 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31).
  Proof.
    intros m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31
           (BI & SAV & [jA FRA] & [jB FRB] & [jC FRC] & STL & STG & [jH XH] & XL & XS & SB1 & US & UP & ARO) ER.
    pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3)] _) XH)) as XM.
    pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20338); C8 (Z_to_bv 64 0x83c6c); CB 96 jH] _) XH)) as XP.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XP.
    match type of XP with rw_cells _ _ ?a _ => replace a with (FF + 120) in XP by (clear; lia) end.
    eapply (PHERR m1 jA _ _ _); [exact BI | exact SAV | exact FRA | exact FRB | reflexivity | exact FRC | reflexivity | exact STL | exact STG
                                | exact XM | exact XP | exact XL | exact XS | exact ER].
  Qed.

  Ltac gf_unhold := unfold fk_held in *.
  (* [comment removed for export] *)
  Ltac gf_hold_all :=
    repeat match goal with H : ?T |- _ =>
      lazymatch T with
      | fk_held _ => fail
      | (0 <= Znth _ _ < 256)%Z => fail
      | bytes_at _ _ _ _ => fail
      | mem_inv _ _ => fail
      | (0 <= _ + _ /\ _ /\ _)%Z => fail
      | all_bytes _ => fail
      | rng _ _ _ => fail
      | (rng _ _ _ /\ _) => fail
      | unpoisoned _ _ _ => fail
      | stk _ _ _ _ => fail
      | _ => lazymatch type of T with Prop => fk_hold H end
      end
    end.
  Ltac keep_byte_facts := repeat match goal with H : ?T |- _ => lazymatch T with (0 <= Znth _ _ < 256)%Z => fail | _ => clear H end end.
  Ltac lor2add_sideF := keep_byte_facts; first [ lia | split; lia | Z.div_mod_to_equations; lia ].
  Ltac lor2add1F x y :=
    first [ rewrite (lor_add_disj 8 x y) by lor2add_sideF | rewrite (lor_add_disj 16 x y) by lor2add_sideF
          | rewrite (lor_add_disj 24 x y) by lor2add_sideF | rewrite (lor_add_disj 32 x y) by lor2add_sideF
          | rewrite (lor_add_disj 40 x y) by lor2add_sideF | rewrite (lor_add_disj 48 x y) by lor2add_sideF
          | rewrite (lor_add_disj 56 x y) by lor2add_sideF ].
  Ltac lor2addF := match goal with |- context [Z.lor ?x ?y] => first [ lor2add1F x y | rewrite (Z.lor_comm x y); lor2add1F y x ] end.
  Ltac clear_hyps := repeat match goal with H : _ |- _ => clear H end.
  Ltac shl2mulF :=
    repeat match goal with
    | |- context [Z.shiftl ?x ?k] => is_Zlit_zb k; rewrite (Z.shiftl_mul_pow2 x k) by (clear_hyps; lia);
          let v := eval vm_compute in (2^k) in change (2^k) with v
    end.
  (* [comment removed for export] *)
  Ltac zlbF SB OK IB i :=
    lazymatch type of SB with
    | bytes_at ?segs ?m ?SRC (map (Z_to_bv 8) ?src) =>
        let RD := fresh "RD" in
        assert (RD : ov_read_bytes segs m (Z_to_bv 64 (SRC + i)) 1 = Some [Z_to_bv 8 (Znth i src)])
          by (eapply zd_src_rd; [exact SB | clear - IB; lia | reflexivity]);
        first [ assert (0 <= Znth i src < 256) by assumption | let RB := fresh "RB" in assert (RB : 0 <= Znth i src < 256) by (apply OK) ];
        zstep; cbv beta; rewrite (byte_lit8 (Znth i src)) by assumption; clear RD; shl2mulF; repeat lor2addF
    end.
  Ltac zsF := zstep; shl2mulF; repeat lor2addF.

  Ltac fd_hold :=
    repeat match goal with
    | H : rw_cells bsegs _ _ _ |- _ => fk_hold H
    | H : stk bsegs _ _ _ |- _ => fk_hold H
    | H : AZ_finddsize_a.BINV _ _ _ _ _ _ _ _ _ |- _ => fk_hold H
    | H : XINVg _ _ |- _ => fk_hold H
    | H : unpoisoned _ (SPA + 64) _ |- _ => fk_hold H
    | H : rng RNG (shad (SPA + 64)) _ |- _ => fk_hold H
    | H : aro_client _ _ |- _ => fk_hold H
    | H : _ \/ _ |- _ => fk_hold H
    | H : exists _, _ |- _ => fk_hold H
    end.
  (* [comment removed for export] *)
  Ltac fd_run SL off p k STOP :=
    gf_unhold; fd_hold; unfold fk_held in SL;
    kx_autoFA [KAUnp (SRC + off + p) k; KAApp (SRC + off + p) k] [STOP] 40%nat [KZRange SRC 6443008 (2^47); KZRange off 0 (2^47)] [] [];
    [ .. | kx_mem; gf_unhold ].

  (* [comment removed for export] *)
  Lemma p_head : forall m1 off sz total (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    XINV m1 -> 5 <= sz -> 0 <= off -> off + sz <= size0 ->
    RES = find_dsize src off sz total -> 0 <= total < 18446744073709551616 -> sz <= SZB ->
    evtF bsegs RNG POST (STpc 0x83e40 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 KSK (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (FF + 32))
                              x22 (Z_to_bv 64 total) x28 x29 x30 x31).
  Proof.
    intros m1 off sz total x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 XI R5 ROFF RSZ ER RT RB.
    pose proof XI as (BI & SAV & [jA FRA] & [jB FRB] & [jC FRC] & STL & STG & [jH XH] & XL & XS & SB1 & US & UP & ARO).
    pose proof G_src as (S1 & S2). pose proof R_src as (RS1 & RS2).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (fk_ablk_lits _ _ S1) as SL.
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    assert (SRr : 6443008 <= SRC /\ SRC + zlen src + 8 <= 2^47) by (clear - SL ATR; lia).
    assert (SZr : 5 <= sz < 18446744073709551616) by (clear - R5 RSZ ROFF N40; lia).
    destruct BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    pose proof ER as ER0.
    rewrite (find_dsize_eq src OK) in ER by (change (2^64) with 18446744073709551616; clear - RSZ N40 ROFF; lia).
    unfold ZD_FRAMEHEADERSIZE_PREFIX in ER. replace (sz <? 5) with false in ER by (symmetry; apply Z.ltb_ge; clear - R5; lia).
    assert (ERRV : Z_to_bv 64 (-2) = Z_to_bv 64 ZD_CONTENTSIZE_ERROR) by (apply Z_to_bv_eqm; reflexivity).
    (* [comment removed for export] *)
    fd_run SL off 0 4 0x83e64.
    fd_hold. assert (IB : 0 <= off + 0 /\ off + 5 <= zlen src /\ 0 <= SRC) by (clear - R5 RSZ ROFF NLEN DB; lia). gf_hold_all.
    zlbF SB1 OK IB (off + 1). zlbF SB1 OK IB off. zlbF SB1 OK IB (off + 2). zlbF SB1 OK IB (off + 3).
    do 7 zsF.
    match goal with |- context [Z.shiftr ?e 4] => replace e with (le32 src off) by (rewrite le32_bytes; clear; lia) end.
    pose proof (le32_range src OK off) as RM. change (2^32) with 4294967296 in RM.
    rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^4) with 16.
    (* [comment removed for export] *)
    unfold fk_held in FRB, G_lo.
    zsF.                                                   (* [comment removed for export] *)
    if_cases KS; zify_cond KS.
    { (* [comment removed for export] *)
      gf_unhold. apply PREG; [exact XI | exact R5 | exact ROFF | exact RSZ | exact ER0 | exact RT | unfold is_skippable_magic; apply Z.eqb_neq; clear - KS; lia | exact RB]. }
    (* [comment removed for export] *)
    unfold is_skippable_magic in ER. rewrite KS, Z.eqb_refl in ER. cbv zeta in ER.
    unfold fk_held in SZr.
    zsF. zsF. zsF. if_cases K8; zify_cond K8.
    { (* [comment removed for export] *)
      gf_unhold. eapply p_xexit; [exact XI | reflexivity |]. rewrite ER. unfold read_skippable_frame_size, ZD_SKIPPABLEHEADERSIZE.
      replace (sz <? 8) with true by (symmetry; apply Z.ltb_lt; clear - K8 SZr; lia).
      rewrite zd_is_error_ZERR by (unfold ZE_srcSize_wrong, ZE_maxCode; clear; lia). exact ERRV. }
    (* [comment removed for export] *)
    try clear KXE KXA KXRD KXK KXMI.
    zsF.                                                   (* [comment removed for export] *)
    fd_run SL off 4 4 0x83ec8.
    try clear KXMI. fd_hold. assert (IB2 : 0 <= off + 4 /\ off + 8 <= zlen src /\ 0 <= SRC) by (unfold fk_held in K8; clear - K8 RSZ ROFF NLEN DB; lia). gf_hold_all.
    zlbF SB1 OK IB2 (off + 5). zlbF SB1 OK IB2 (off + 4). zlbF SB1 OK IB2 (off + 6). zlbF SB1 OK IB2 (off + 7).
    do 6 zsF.
    let w := getreg 10 in replace w with (Z_to_bv 64 (le32 src (off + 4)))
      by (f_equal; rewrite le32_bytes; replace (off + 4 + 1) with (off + 5) by (clear; lia); replace (off + 4 + 2) with (off + 6) by (clear; lia);
          replace (off + 4 + 3) with (off + 7) by (clear; lia); clear; lia).
    pose proof (le32_range src OK (off + 4)) as RS. change (2^32) with 4294967296 in RS.
    set (s32 := le32 src (off + 4)) in *.
    assert (RSK : read_skippable_frame_size src off sz =
                  if 4294967287 <? s32 then ZERR ZE_frameParameter_unsupported else if sz <? 8 + s32 then ZERR ZE_srcSize_wrong else 8 + s32).
    { unfold read_skippable_frame_size, ZD_SKIPPABLEHEADERSIZE. unfold fk_held in K8. replace (sz <? 8) with false by (symmetry; apply Z.ltb_ge; clear - K8; lia).
      cbv zeta. fold s32. pose proof (skippable_wrap_iff s32 ltac:(change (2^32) with 4294967296; clear - RS; lia)) as WI.
      unfold ZD_SKIPPABLEHEADERSIZE in WI. rewrite WI. reflexivity. }
    rewrite RSK in ER.
    (* [comment removed for export] *)
    unfold fk_held in FRB, G_lo.
    zsF.                                                   (* [comment removed for export] *)
    zsF. if_cases KW; zify_cond KW.
    { gf_unhold. eapply p_xexit; [exact XI | reflexivity |]. rewrite ER.
      replace (4294967287 <? s32) with true by (symmetry; apply Z.ltb_lt; clear - KW; lia).
      rewrite zd_is_error_ZERR by (unfold ZE_frameParameter_unsupported, ZE_maxCode; clear; lia). exact ERRV. }
    replace (4294967287 <? s32) with false in ER by (symmetry; apply Z.ltb_ge; clear - KW; lia).
    unfold fk_held in SZr.
    zsF.                                                   (* [comment removed for export] *)
    zsF. if_cases KFIT; zify_cond KFIT.                    (* [comment removed for export] *)
    - (* [comment removed for export] *)
      replace (sz <? 8 + s32) with false in ER by (symmetry; apply Z.ltb_ge; clear - KFIT SZr; lia).
      replace (zd_is_error (8 + s32)) with false in ER
        by (symmetry; apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; clear - RS; lia).
      try clear KXE KXA KXRD KXK KXMI.
      try (let w := getreg 10 in replace w with (Z_to_bv 64 (8 + s32)) by (first [f_equal; clear; lia | apply Z_to_bv_eqm; clear; lia])).
      gf_unhold. eapply (PADV _ off sz (8 + s32) total); [exact XI | clear - KFIT RS; lia | exact ROFF | exact RSZ | exact ER | exact RT | exact RB].
    - (* [comment removed for export] *)
      zsF.
      gf_unhold. eapply p_xexit; [exact XI | reflexivity |]. rewrite ER.
      replace (sz <? 8 + s32) with true by (symmetry; apply Z.ltb_lt; clear - KFIT SZr; lia).
      rewrite zd_is_error_ZERR by (unfold ZE_srcSize_wrong, ZE_maxCode; clear; lia). exact ERRV.
  Qed.
End FD.
End CANSEC1.
