From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun FseRdKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_bdt_model
  RF_huf_bdt_bld RF_huf_bdt_fast RF_huf_bdt_tail.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Step MState.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Stdio_pure.
Import ListNotations.
Open Scope Z_scope.

Section FPath.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (SPV DT NC WK msv tl fm hT lo : Z) (nc : list Z) (jt : list byte) (syms1 : list (option Z)) (snext : list Z).
  Variable POST : machine_state -> Prop.
  Hypothesis TLR : 1 <= tl <= 12.
  Hypothesis MSVR : 0 <= msv <= 255.
  Hypothesis FMR : fm = 0 \/ fm = 1.
  Hypothesis HNCL : msv + 1 <= zlen nc.
  Hypothesis HNCR : Forall (fun c => - 32768 <= c < 32768) nc.
  Hypothesis HT0 : 0 <= hT < 2^32.
  Hypothesis HT1 : hT < 2^tl \/ hT = 2^32 - 1.
  Hypothesis EH : hT = 2^tl - 1.
  Hypothesis LS1 : length syms1 = Z.to_nat (2^tl).
  Hypothesis HJT : length jt = (4 * Z.to_nat (2^tl))%nat.
  Hypothesis LSN : zlen snext = msv + 1.
  Hypothesis FSN : Forall (fun v => 0 <= v < 65536) snext.
  Hypothesis HDT : 0 < DT /\ DT mod 4 = 0 /\ DT + (1 + 2^tl) * 4 <= 2^64.
  Hypothesis HWK : 0 < WK /\ WK mod 2 = 0 /\ WK + (2 * (msv + 1) + 2^tl + 8) <= 2^64.
  Hypothesis HNC : 0 < NC /\ NC mod 2 = 0 /\ NC + 2 * zlen nc <= 2^64.
  Hypothesis DTW : DT + (1 + 2^tl) * 4 <= WK \/ WK + (2 * (msv + 1) + 2^tl + 8) <= DT.
  Hypothesis DTN : DT + (1 + 2^tl) * 4 <= NC \/ NC + 2 * zlen nc <= DT.
  Hypothesis DWN : WK + (2 * (msv + 1) + 2^tl + 8) <= NC \/ NC + 2 * zlen nc <= WK.
  Hypothesis HSP : SPV <= 2^64.
  Hypothesis HLO : lo <= SPV - 128.
  Hypothesis DLO : DT + (1 + 2^tl) * 4 <= lo \/ SPV <= DT.
  Hypothesis WLO : WK + (2 * (msv + 1) + 2^tl + 8) <= lo \/ SPV <= WK.
  Hypothesis NLO : NC + 2 * zlen nc <= lo \/ SPV <= NC.

  Notation FRC := [C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (WK + 2 * msv)); C8 (Z_to_bv 64 tl);
      C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma bdt_fpath : forall syms2 position m0 (jw' : list byte) (y7 y18 y24 : word),
    forall spread, spread_loop nc (Z.to_nat (msv + 1)) 0 (repeat None (Z.to_nat (2^tl + 8))) 0 = Ok spread ->
    place_loop tl (Z.to_nat (2^tl / 2)) 0 spread syms1 0 = Ok (syms2, position) ->
    length jw' = Z.to_nat (2^tl + 8) ->
    u8arr usegs m0 DT (le2 (Z_to_bv 64 tl) ++ le2 (Z_to_bv 64 fm)) ->
    u8arr usegs m0 (DT + 4) (tsym jt syms1) ->
    u8arr usegs m0 WK (u16s (map (Z_to_bv 64) snext) ++ jw') ->
    bytes_at usegs m0 NC (u16s (map (Z_to_bv 64) nc)) ->
    rw_cells usegs m0 (SPV + -128) FRC ->
    stk usegs m0 lo (SPV + -128) ->
    munch [(SPV - 128, SPV); (DT, DT + (1 + 2^tl) * 4); (WK, WK + (2 * (msv + 1) + 2^tl + 8))] m m0 ->
    wmono usegs m m0 -> mem_inv usegs m0 ->
    (forall m1 (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
       length syms2 = Z.to_nat (2^tl) ->
       u8arr usegs m1 DT (le2 (Z_to_bv 64 tl) ++ le2 (Z_to_bv 64 fm)) ->
       u8arr usegs m1 (DT + 4) (tsym jt syms2) ->
       u8arr usegs m1 WK (u16s (map (Z_to_bv 64) snext)) ->
       rw_cells usegs m1 (SPV + -128) FRC ->
       stk usegs m1 lo (SPV + -128) ->
       munch [(SPV - 128, SPV); (DT, DT + (1 + 2^tl) * 4); (WK, WK + (2 * (msv + 1) + 2^tl + 8))] m m1 ->
       wmono usegs m m1 -> mem_inv usegs m1 ->
       evt usegs POST
         (MS (mkR x1 (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13
                  (Z_to_bv 64 WK) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (Z.lxor WK 18446744073709551615)) (Z_to_bv 64 (DT + 4))
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (Z_to_bv 64 0x1f508) fc None m1 (seg_rom usegs))) ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 (SPV + -128)) gp tp (Z_to_bv 64 (Z.lxor (DT + 4) 18446744073709551615)) (Z_to_bv 64 (2 ^ tl + -1)) y7
               (Z_to_bv 64 (msv + 1)) (Z_to_bv 64 (bv_swrap 32 (bv_wrap 32 (2 ^ tl) ≫ 1)))
               (Z_to_bv 64 (Z.lor ((fm mod 18446744073709551616) ≪ 16 mod 18446744073709551616) tl)) (Z_to_bv 64 NC) (Z_to_bv 64 (msv + 1 - 1))
               (Z_to_bv 64 DT) (Z_to_bv 64 WK) (Z_to_bv 64 (2 ^ tl)) (Z_to_bv 64 (Z.lxor WK 18446744073709551615)) (Z_to_bv 64 (DT + 4))
               y18 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 ((fm mod 18446744073709551616) ≪ 16)) (Z_to_bv 64 (2 ^ (tl - 1)))
               (Z_to_bv 64 65535) y24 s9 s10 s11 (Z_to_bv 64 (Z.lxor NC 18446744073709551615)) (Z_to_bv 64 (WK + 2 * (msv + 1)))
               (Z_to_bv 64 (bv_swrap 32 hT)) (Z_to_bv 64 (msv + 1)))
          F (Z_to_bv 64 0x1f31c) fc None m0 (seg_rom usegs)).
  Proof using All.
    intros syms2 position m0 jw' y7 y18 y24 spread HSPL HPL LJW ADH ADT AWK NCB FR STK MU WM MI CONT.
    pose proof (rw_cells_bound usegs _ _ _ FR) as FRB. cbn [cells_size csize] in FRB.
    assert (P2 : 2 <= 2^tl <= 4096).
    { assert (Q1 : 2^1 <= 2^tl) by (apply Z.pow_le_mono_r; lia). assert (Q2 : 2^tl <= 2^12) by (apply Z.pow_le_mono_r; lia).
      change (2^1) with 2 in Q1. change (2^12) with 4096 in Q2. lia. }
    assert (ZJW : zlen jw' = 2^tl + 8) by (rewrite LJW; lia).
    assert (TLC : tl = 1 \/ tl = 2 \/ tl = 3 \/ tl = 4 \/ tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11
                  \/ tl = 12) by lia.
    repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1f358) _ _ _ _) => fail
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; lia)
      | _ => zstep end).
    apply (proj1 (u8arr_app usegs m0 WK _ _)) in AWK. destruct AWK as (ASN & AJW).
    lazymatch type of AJW with u8arr _ _ (WK + ?L) _ =>
      assert (EL : L = 2 * (msv + 1)) by (rewrite ?u16s_length, ?length_map; lia); rewrite EL in AJW; clear EL end.
    destruct (proj1 (Stdio_pure.rw_cells_app usegs m0 (SPV + -128) [C8 (Z_to_bv 64 DT)] _) FR) as (FR0 & FR1).
    cbn [cells_size csize] in FR1.
    destruct (proj1 (Stdio_pure.rw_cells_app usegs m0 (SPV + -128 + Z.of_nat 8) [C8 (Z_to_bv 64 (WK + 2 * msv))] _) FR1)
      as (FR1a & FR1b).
    cbn [cells_size csize] in FR1b.
    assert (SP80 : rw_cells usegs m0 (bv_unsigned (Z_to_bv 64 (SPV + -128)) + 8) [C8 (Z_to_bv 64 (WK + 2 * (msv + 1) - 2))]).
    { rewrite unsigned_lit by lia. replace (WK + 2 * (msv + 1) - 2) with (WK + 2 * msv) by lia.
      replace (SPV + -128 + 8) with (SPV + -128 + Z.of_nat 8) by reflexivity. exact FR1a. }
    eapply sp_outer with (m := m0) (m1 := m0) (NC := NC) (SPR := WK + 2 * (msv + 1)) (nc := nc) (M1 := msv + 1) (js := jw')
      (f := Z.to_nat (msv + 1)) (s := 0) (spr := repeat None (Z.to_nat (2^tl + 8))) (pos := 0) (r := spread)
      (sp := Z_to_bv 64 (SPV + -128)).
    all: try exact HSPL.
    all: try exact NCB.
    all: try exact SP80.
    all: try exact HNCR.
    all: try (rewrite unsigned_lit by lia; lia).
    all: try (rewrite repeat_length; rewrite LJW; reflexivity).
    all: try (unfold sp_inv; rewrite omerge_none; split; [exact AJW | split; [apply munch_refl | split; [apply wmono_refl | exact MI]]]).
    all: try lia.
    intros m2 z1 z7 z8 z10 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z30 z31 SPI LR.
    unfold sp_inv in SPI. destruct SPI as (ASP & MU2 & WM2 & MI2).
    pose proof (rw_cells_transport usegs _ m0 m2 _ _ FR0 MU2 WM2 ltac:(cbn; lia)) as FR02.
    pose proof (rw_cells_transport usegs _ m0 m2 _ _ FR1a MU2 WM2 ltac:(cbn; lia)) as FR1a2.
    pose proof (rw_cells_transport usegs _ m0 m2 _ _ FR1b MU2 WM2 ltac:(cbn; lia)) as FR1b2.
    assert (FR2 : rw_cells usegs m2 (SPV + -128) FRC) by
      (apply (proj2 (Stdio_pure.rw_cells_app usegs m2 (SPV + -128) [C8 (Z_to_bv 64 DT)] _)); split; [exact FR02|];
       apply (proj2 (Stdio_pure.rw_cells_app usegs m2 _ [C8 (Z_to_bv 64 (WK + 2 * msv))] _)); split; [exact FR1a2 | exact FR1b2]).
    clear FR02 FR1a2 FR1b2.
    repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1f4a4) _ _ _ _) => fail
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; lia)
      | _ => zstep end).
    replace (Z_to_bv 64 (WK + 2 * msv + 3)) with (Z_to_bv 64 (WK + 2 * (msv + 1) + 1)) by (f_equal; lia).
    lazymatch goal with |- context [Z_to_bv 64 (Z.land (bv_swrap 32 ?E) ?K ≪ 1)] =>
      assert (ET : Z.land (bv_swrap 32 E) K ≪ 1 = 2 * table_step (2^tl))
        by (clear - TLC; repeat (destruct TLC as [TLC|TLC]; [rewrite TLC; vm_compute; reflexivity|]);
            rewrite TLC; vm_compute; reflexivity);
      rewrite ET;
      assert (ES : bv_swrap 32 E = table_step (2^tl))
        by (clear - TLC; repeat (destruct TLC as [TLC|TLC]; [rewrite TLC; vm_compute; reflexivity|]);
            rewrite TLC; vm_compute; reflexivity);
      rewrite ES end.
    assert (STB : 0 < table_step (2^tl) < 8192)
      by (clear - TLC; repeat (destruct TLC as [TLC|TLC]; [rewrite TLC; vm_compute; split; reflexivity|]);
          rewrite TLC; vm_compute; split; reflexivity).
    assert (HALF : 2 * Z.of_nat (Z.to_nat (2^tl / 2)) = 2^tl - 0).
    { assert (EV : 2^tl = 2 * 2^(tl - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
      assert (MD : 2^tl mod 2 = 0) by (rewrite EV, Z.mul_comm, Z_mod_mult; reflexivity).
      pose proof (Z.div_mod (2^tl) 2 ltac:(lia)) as DM.
      assert (DP0 : 0 <= 2^tl / 2) by (apply Z.div_pos; lia).
      rewrite Z2Nat.id by lia. lia. }
    eapply pl_loop with (m := m2) (m1 := m2) (TD := DT + 4) (SPR := WK + 2 * (msv + 1)) (tl := tl)
      (stp := table_step (2^tl)) (jt := jt) (js := jw') (spread := spread) (f := Z.to_nat (2^tl / 2)) (s := 0)
      (syms := syms1) (position := 0) (r := (syms2, position)).
    all: try exact HPL.
    all: try exact HALF.
    all: try exact ASP.
    all: try exact STB.
    all: try reflexivity.
    all: try assumption.
    all: try (symmetry; exact LR).
    all: try (rewrite LR; lia).
    all: try lia.
    all: try (unfold pl_inv; split;
                [exact (u8arr_transport usegs _ m0 m2 _ _ ADT MU2 WM2 ltac:(rewrite tsym_length, HJT; cbn; lia))
                | split; [apply munch_refl | split; [apply wmono_refl | exact MI2]]]).
    intros m3 syms' pos' w5 w6 w7 w10 w11 w12 w13 w28 w29 w30 w31 HR LS3 PLI.
    injection HR as E1 E2. subst syms' pos'.
    unfold pl_inv in PLI. destruct PLI as (ATD3 & MU3 & WM3 & MI3).
    assert (SUB2 : sub_fp [(WK + 2 * (msv + 1), WK + 2 * (msv + 1) + zlen jw')]
                          [(SPV - 128, SPV); (DT, DT + (1 + 2^tl) * 4); (WK, WK + (2 * (msv + 1) + 2^tl + 8))])
      by (intros x HX; cbn [outside] in *; lia).
    assert (SUB3 : sub_fp [(DT + 4, DT + 4 + 4 * 2^tl)]
                          [(SPV - 128, SPV); (DT, DT + (1 + 2^tl) * 4); (WK, WK + (2 * (msv + 1) + 2^tl + 8))])
      by (intros x HX; cbn [outside] in *; lia).
    pose proof (munch_trans _ m m0 m2 MU (munch_weaken _ _ m0 m2 SUB2 MU2)) as MUa.
    pose proof (munch_trans _ m m2 m3 MUa (munch_weaken _ _ m2 m3 SUB3 MU3)) as MUb.
    pose proof (wmono_trans usegs m m0 m2 WM WM2) as WMa.
    pose proof (wmono_trans usegs m m2 m3 WMa WM3) as WMb.
    eapply CONT.
    - exact LS3.
    - exact (u8arr_transport usegs _ m2 m3 _ _ (u8arr_transport usegs _ m0 m2 _ _ ADH MU2 WM2 ltac:(simpl; lia))
               MU3 WM3 ltac:(simpl; lia)).
    - exact ATD3.
    - exact (u8arr_transport usegs _ m2 m3 _ _
               (u8arr_transport usegs _ m0 m2 _ _ ASN MU2 WM2 ltac:(cbn [disjoint_from]; rewrite ?u16s_length, ?length_map; lia))
               MU3 WM3 ltac:(cbn [disjoint_from]; rewrite ?u16s_length, ?length_map; lia)).
    - exact (rw_cells_transport usegs _ m2 m3 _ _ FR2 MU3 WM3 ltac:(cbn; lia)).
    - assert (STK2 : stk usegs m2 lo (SPV + -128))
        by (apply (stk_transport usegs _ m0 m2 _ _ STK MU2 WM2); intros x Hx; left; cbn [outside]; split; [lia | exact I]).
      apply (stk_transport usegs _ m2 m3 _ _ STK2 MU3 WM3); intros x Hx; left; cbn [outside]; split; [lia | exact I].
    - exact MUb.
    - exact WMb.
    - exact MI3.
  Qed.
End FPath.
