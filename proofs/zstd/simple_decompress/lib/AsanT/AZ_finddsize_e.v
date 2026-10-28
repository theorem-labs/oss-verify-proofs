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
     AZ_frame_iface AZ_libc_iface AZ_kx AZ_globals AZ_globalsR AZ_findfsi_a AZ_findfsi_b AZ_findfsi_c AZ_finddsize_a AZ_finddsize_b AZ_finddsize_c AZ_finddsize_d.
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

  Notation POST := (zd_finddsize_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV src size0 lo m0).
  Notation RES := (find_decompressed_size src size0).
  Notation BINV := (AZ_finddsize_a.BINV AI L RNG st LB m0 SPV FF).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 (Z_to_bv 64 SHF) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) (Z_to_bv 64 KM8) x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Notation XINVg := (AZ_finddsize_b.XINVg AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA SRC src lo FF SHF FLG).
  Notation XINV := (XINVg DSH0).


  (* [comment removed for export] *)
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis GETFH : zd_getfh_stmtA AI rng_fs.
  Hypothesis FINDFSI : zd_findfsi_stmtA AI rng_fs.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis ASH : ashort LB 3.
  Hypothesis RFS : rng_fs L RNG.
  Hypothesis SPT : SPV + 16 < al_top L.
  Hypothesis RSTKT : rng RNG lo (al_top L - lo).
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis INS : 0 < zlen src -> ainimg LB SRC (zlen src).

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
  Hypothesis PEND : forall m1 off sz total jA csB csC w0 shb (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 16 jA; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m1 (SPA + 24) csB -> cells_size csB = 40%nat -> rw_cells bsegs m1 (SPA + 64) csC -> cells_size csC = 24%nat ->
    stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 88) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 120) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 16 shb] ->
    RES = find_dsize src off sz total -> 0 <= sz < 5 -> 0 <= total < 18446744073709551616 ->
    evtF bsegs RNG POST (STpc 0x83da0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 sz) x20 x21 x22 (Z_to_bv 64 total) x28 x29 x30 x31).

  Ltac gf_unhold := unfold fk_held in *.

  (* [comment removed for export] *)
  Definition EINV0 (m1 : amem) : Prop :=
    BINV m1 /\ rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ (exists jA, rw_cells bsegs m1 SPA [CB 16 jA; C8 (Z_to_bv 64 FF)])
    /\ (exists j24 jB, rw_cells bsegs m1 (SPA + 24) [CB 8 j24; CB 24 jB; C8 (Z_to_bv 64 FF)])
    /\ (exists jC, rw_cells bsegs m1 (SPA + 64) [CB 24 jC])
    /\ stk bsegs m1 lo SPA /\ stk bsegs m1 (SPA + 88) (SPV + -104)
    /\ (exists j, rw_cells bsegs m1 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20338); C8 (Z_to_bv 64 0x83c6c); CB 96 j; C8 (Z_to_bv 64 FLG)])
    /\ rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m1 SHF DSH0
    /\ bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) /\ unpoisoned m1 SRC (SRC + zlen src)
    /\ unpoisoned m1 (SPA + 64) (SPA + 88) /\ aro_client RNG m1.

  (* [comment removed for export] *)
  Lemma p_xend : forall m1 off sz total (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    XINV m1 -> RES = find_dsize src off sz total -> 0 <= sz < 5 -> 0 <= total < 18446744073709551616 ->
    evtF bsegs RNG POST (STpc 0x83da0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 sz) x20 x21 x22 (Z_to_bv 64 total) x28 x29 x30 x31).
  Proof.
    intros m1 off sz total x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31
           (BI & SAV & [jA FRA] & [jB FRB] & [jC FRC] & STL & STG & [jH XH] & XL & XS & SB1 & US & UP & ARO) ER RSZ RT.
    destruct (rw_cells_forget _ _ _ _ XS) as [shb XS']. cbn [cells_size csize Nat.add DSH0 length] in XS'.
    pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3)] _) XH)) as XM.
    pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20338); C8 (Z_to_bv 64 0x83c6c); CB 96 jH] _) XH)) as XP.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XP.
    match type of XP with rw_cells _ _ ?a _ => replace a with (FF + 120) in XP by (clear; lia) end.
    eapply (PEND m1 off sz total jA _ _ _ shb); [exact BI | exact SAV | exact FRA | exact FRB | reflexivity | exact FRC | reflexivity | exact STL | exact STG
                                      | exact XM | exact XP | exact XL | exact XS' | exact ER | exact RSZ | exact RT].
  Qed.

  (* [comment removed for export] *)
  Definition LOOPAT (n : nat) : Prop :=
    forall m1 off sz total (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    XINV m1 -> 5 <= sz -> 0 <= off -> off + sz <= size0 ->
    RES = find_dsize src off sz total -> 0 <= total < 18446744073709551616 -> sz <= Z.of_nat n ->
    evtF bsegs RNG POST (STpc 0x83e40 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 KSK (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (FF + 32))
                              x22 (Z_to_bv 64 total) x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma p_adv : forall n, LOOPAT n ->
    forall m1 off sz step total (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    XINV m1 -> 8 <= step <= sz -> 0 <= off -> off + sz <= size0 ->
    RES = find_dsize src (off + step) (sz - step) total -> 0 <= total < 18446744073709551616 -> sz <= Z.of_nat (S n) ->
    evtF bsegs RNG POST (STpc 0x83e30 m1 x1 x5 x6 x7 (Z_to_bv 64 step) x11 x12 x13 x14 x15 x16 x17 KSK (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (FF + 32))
                              x22 (Z_to_bv 64 total) x28 x29 x30 x31).
  Proof.
    intros n IH m1 off sz step total x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 XI RST ROFF RSZ ER RT RB.
    pose proof XI as (BI & REST). destruct BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    assert (SZr : 5 <= sz < 18446744073709551616) by (clear - RST RSZ ROFF N40; lia).
    fk_hold XI. fk_hold REST. fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold ER. fk_hold RB. fk_hold IH.
    fk_hold G_lo. fk_hold G_src. fk_hold G_ff. fk_hold G_flg. fk_hold R_src. fk_hold R_ff. fk_hold R_fsi. fk_hold LBH. fk_hold INS. fk_hold ASH.
    fk_hold PEXIT. fk_hold PHERR. fk_hold PEND.
    zstep.                                                 (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    replace (SRC + off + step) with (SRC + (off + step)) by (clear; lia).
    zstep.                                                 (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      gf_unhold. eapply (p_xend m1 (off + step) (sz - step) total); [exact XI | exact ER | | exact RT].
      first [ clear - K RST SZr; lia | rewrite Z.mod_small in K by (clear - RST SZr; lia); clear - K RST SZr; lia ].
    - gf_unhold. eapply (IH m1 (off + step) (sz - step) total); [exact XI | | clear - ROFF RST; lia | clear - RSZ RST; lia | exact ER | exact RT | clear - RB RST; lia].
      first [ clear - K RST SZr; lia | rewrite Z.mod_small in K by (clear - RST SZr; lia); clear - K RST SZr; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma p_loop : forall n, LOOPAT n.
  Proof.
    pose proof (AZ_finddsize_b.p_xexit AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA SRC src size0 lo FF SHF FLG PEXIT) as PXEXIT.
    pose proof (AZ_finddsize_b.p_xherr AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA SRC src size0 lo FF SHF FLG PHERR) as PXHERR.
    induction n as [|n IH]; intros m1 off sz total x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 XI R5 ROFF RSZ ER RT RN.
    { exfalso. clear - R5 RN. lia. }
    pose proof (p_adv n IH) as PADV.
    pose proof (AZ_finddsize_d.p_fsi AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA SRC src size0 lo FF SHF FLG
                  OK N40 NLEN SRCE G_lo KLO G_src G_ff G_flg RSTK RI R_src R_ff R_fsi LBH (Z.of_nat (S n)) rng_fs FINDFSI FHL FFLAG ASH RFS SPT RSTKT TP INS PXEXIT PADV) as PFSI.
    pose proof (AZ_finddsize_c.p_reg AI fflag L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA SRC src size0 lo FF SHF FLG
                  OK N0 N40 NLEN G_lo KLO G_src G_ff G_flg RSTK RI R_src R_ff R_fsi LBH (Z.of_nat (S n)) rng_fs GETFH FHL FFLAG ASH RFS SPT RSTKT TP INS PXEXIT PXHERR PFSI) as PREG.
    eapply (AZ_finddsize_b.p_head AI fflag FRL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA SRC src size0 lo FF SHF FLG
              OK N0 N40 NLEN SRCE G_lo KLO G_src G_ff G_flg RSTK R_src R_fsi LBH (Z.of_nat (S n)) PEXIT PHERR PADV PREG m1 off sz total);
      [exact XI | exact R5 | exact ROFF | exact RSZ | exact ER | exact RT | exact RN].
  Qed.

  (* [comment removed for export] *)
  Lemma p_lset : forall m1 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x28 x29 x30 x31 : word),
    EINV0 m1 -> 5 <= size0 ->
    evtF bsegs RNG POST (STpc 0x83e10 m1 x1 x5 x6 x7 (Z_to_bv 64 5) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 size0) (Z_to_bv 64 SRC) x21 x22 (Z_to_bv 64 0) x28 x29 x30 x31).
  Proof.
    intros m1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x28 x29 x30 x31 EI R5.
    destruct EI as (BI & SAV & [jA FRA] & (j24 & jB & FRB) & [jC FRC] & STL & STG & [jH XH] & XL & XS & SB1 & US & UP & ARO).
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    destruct BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    pose proof (munch_refl [(SPA + 24, SPA + 32)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold XH. fk_hold XL. fk_hold XS. fk_hold SB1. fk_hold US. fk_hold UP. fk_hold ARO.
    fk_hold G_src. fk_hold G_ff. fk_hold G_flg. fk_hold R_src. fk_hold R_ff. fk_hold R_fsi. fk_hold LBH. fk_hold INS. fk_hold ASH. fk_hold PEXIT. fk_hold PHERR. fk_hold PEND.
    zstep.                                                 (* [comment removed for export] *)
    zstep. zstep. zstep.                                   (* [comment removed for export] *)
    first [ let w := getreg 18 in replace w with KSK by (apply Z_to_bv_eqm; reflexivity) | idtac ].
    zstep.                                                 (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    first [ let w := getreg 10 in replace w with (Z_to_bv 64 K9) by (apply Z_to_bv_eqm; reflexivity) | idtac ].
    zstep.                                                 (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    gf_unhold.
    replace (Z_to_bv 64 SRC) with (Z_to_bv 64 (SRC + 0)) by (f_equal; clear; lia).
    assert (DJ : forall X k, (X + k <= SPA + 24 \/ SPA + 32 <= X) -> 0 <= k -> disjoint_from [(SPA + 24, SPA + 32)] X k)
      by (intros X k H1 Hk; cbn [disjoint_from]; clear - H1 Hk; split; [lia| exact I]).
    assert (DS : forall X nn, 0 <= X -> 0 <= nn -> X + nn <= 2^47 -> disjoint_from [(SPA + 24, SPA + 32)] (shad X) (shad (X + nn - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *.
      clear - X0 Hn Hb ATR G1 G2. Z.div_mod_to_equations. lia. }
    pose proof (fk_ablk_lits _ _ (proj1 G_src)) as SL. pose proof (fk_ablk_lits _ _ F1) as FL. pose proof (fk_ablk_lits _ _ (proj1 (proj2 G_flg))) as LL.
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    eapply (p_loop (Z.to_nat size0) m2 0 size0 0); [| exact R5 | clear; lia | clear; lia | reflexivity | clear; lia | clear - N0; lia].
    split; [| split; [| split; [exists jA| split; [exists jB| split; [exists jC| split; [| split; [| split; [exists jH| split; [| split; [| split; [| split; [| split]]]]]]]]]]]].
    - split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM1 WML) | assumption]]]].
      + eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |]. constructor; [cbn [fst snd]; left; left; clear - G1 G2 G3 G5; lia | constructor].
      + eapply ffr_pres_trans; [exact FFR1|].
        eapply (fk_ffr_fin AI L RNG st LB m1 m1 m2 1 FF 128 SHF 0 [] [(SPA + 24, SPA + 32)]);
          [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
          | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - G1 G2 G3 G5; lia] | constructor]
          | constructor
          | apply ffr_pres_refl
          | cbn [app]; eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
          | exact WML ].
      + eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx. clear - Hx G3. lia.
    - exact SAV.
    - exact FRA.
    - lazymatch goal with |- rw_cells _ _ _ ?cs => first [exact FRB | eapply rw_cells_recast; [exact FRB| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]] end.
    - exact FRC.
    - exact STL.
    - exact STG.
    - eapply rw_cells_transport; [exact XH | exact MUL | exact WML | apply DJ; [cbn; clear - F3 G1 G2; lia| clear; lia]].
    - eapply rw_cells_transport; [exact XL | exact MUL | exact WML | apply DJ; [cbn; clear - LL G1 G2 ATR; lia| clear; lia]].
    - eapply rw_cells_transport; [exact XS | exact MUL | exact WML | apply DJ; [| clear; lia]].
      rewrite F4, shad_div. unfold ASHOFF, DSH0. cbn. clear - FL G1 G2 ATR. Z.div_mod_to_equations. lia.
    - eapply bytes_at_transport; [exact SB1 | exact MUL | rewrite length_map; apply DJ; [clear - G_src G2 G3; destruct G_src as [_ S2]; lia| clear; lia]].
    - eapply unpoisoned_munch; [exact US | exact MUL | apply DS; clear - SL ATR DB; lia].
    - eapply unpoisoned_munch; [exact UP | exact MUL | replace (SPA + 88 - 1) with (SPA + 64 + 24 - 1) by (clear; lia); apply DS; clear - G1 G2 G3 G5 ATR KLO; unfold KHIGH in KLO; lia].
    - eapply aro_client_transport_gen; [exact WML | exact ARO | exact MUL |]. intros A n HIn.
      destruct (aclient_bounds A n HIn) as (B1 & B2 & B3). cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF.
      clear - B1 B2 B3 G1 G2 ATR. repeat split; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma p_top : forall m1 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x28 x29 x30 x31 : word),
    EINV0 m1 ->
    evtF bsegs RNG POST (STpc 0x83d9c m1 x1 x5 x6 x7 (Z_to_bv 64 5) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 size0) (Z_to_bv 64 SRC) x21 x22 (Z_to_bv 64 0) x28 x29 x30 x31).
  Proof.
    intros m1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x28 x29 x30 x31 EI.
    pose proof EI as (BI & SAV & [jA FRA] & (j24 & jB & FRB) & [jC FRC] & STL & STG & [jH XH] & XL & XS & SB1 & US & UP & ARO).
    pose proof BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    assert (SZr : 0 <= size0 < 18446744073709551616) by (clear - N0 N40; lia).
    fk_hold EI. fk_hold BI. fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold XH. fk_hold XL. fk_hold XS. fk_hold SB1. fk_hold US. fk_hold UP. fk_hold ARO. fk_hold SAV. fk_hold FRA. fk_hold FRB. fk_hold FRC. fk_hold STL. fk_hold STG.
    fk_hold G_lo. fk_hold G_src. fk_hold G_ff. fk_hold G_flg. fk_hold R_src. fk_hold R_ff. fk_hold R_fsi. fk_hold LBH. fk_hold INS. fk_hold ASH. fk_hold PEXIT. fk_hold PHERR. fk_hold PEND.
    zstep. if_cases K5; zify_cond K5.
    - gf_unhold. apply p_lset; [exact EI| clear - K5 SZr; lia].
    - gf_unhold.
      destruct (rw_cells_forget _ _ _ _ XS) as [shb XS']. cbn [cells_size csize Nat.add DSH0 length] in XS'.
      pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3)] _) XH)) as XM.
      pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20338); C8 (Z_to_bv 64 0x83c6c); CB 96 jH] _) XH)) as XP.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XP.
      match type of XP with rw_cells _ _ ?a _ => replace a with (FF + 120) in XP by (clear; lia) end.
      eapply (PEND m1 0 size0 0 jA _ _ _ shb); [exact BI | exact SAV | exact FRA | exact FRB | reflexivity | exact FRC | reflexivity | exact STL | exact STG
                                           | exact XM | exact XP | exact XL | exact XS' | reflexivity | clear - K5 SZr; lia | clear; lia].
  Qed.
End FD.
End CANSEC1.
