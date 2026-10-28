From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun FseRdKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_bdt_model
  RF_huf_bdt_bld RF_huf_bdt_gen RF_huf_bdt_tail.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Step MState.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Stdio_pure.
Import ListNotations.
Open Scope Z_scope.

Local Ltac upto pc := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
  | _ => zstep end).

Lemma gp_step : forall tl, 1 <= tl <= 12 ->
  bv_swrap 32 (bv_wrap 32 (2 ^ tl) ≫ 3) + bv_swrap 32 (bv_wrap 32 (2 ^ tl) ≫ 1) + 3 = table_step (2 ^ tl)
  /\ 0 < table_step (2 ^ tl) < 8192.
Proof.
  intros tl H.
  assert (C : tl = 1 \/ tl = 2 \/ tl = 3 \/ tl = 4 \/ tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12) by lia.
  destruct C as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]; subst tl;
    (split; [vm_compute; reflexivity | unfold table_step; vm_compute; split; reflexivity]).
Qed.

Section GPath.
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
  Hypothesis NH : hT <> 2^tl - 1.
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

  Lemma bdt_gpath : forall syms2 position m0 (jw' : list byte) (y7 y18 y24 : word),
    gen_loop nc tl (Z.to_nat (msv + 1)) 0 syms1 0 hT = Ok (syms2, position) ->
    position = 0 ->
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
          F (Z_to_bv 64 0x1f418) fc None m0 (seg_rom usegs)).
  Proof using All.
    intros syms2 position m0 jw' y7 y18 y24 GL EP LJW HDR TSY WKA NCB FR STK MU WM MI K.
    pose proof (gp_step tl TLR) as (STV & STR).
    assert (P2 : 2 <= 2^tl <= 4096).
    { assert (Q1 : 2^1 <= 2^tl) by (apply Z.pow_le_mono_r; lia). assert (Q2 : 2^tl <= 2^12) by (apply Z.pow_le_mono_r; lia).
      change (2^1) with 2 in Q1. change (2^12) with 4096 in Q2. lia. }
    upto 128064.
    rewrite STV.
    replace (msv + 1 + Z.b2z (msv + 1 <? 1)) with (msv + 1) by (destruct (Z.ltb_spec (msv + 1) 1); cbn [Z.b2z]; lia).
    rewrite (swrap32_small (msv + 1)) by lia.
    replace (2 ^ tl + -1) with (2 ^ tl - 1) by lia.
    apply u8arr_app in WKA. destruct WKA as (WKS & WKJ).
    eapply (gn_loop ra (Z_to_bv 64 (SPV + -128)) gp tp F fc) with (m := m0) (NC := NC) (TD := DT + 4) (nc := nc) (tl := tl)
      (stp := table_step (2^tl)) (M1 := msv + 1) (hT := hT) (jt := jt) (POST := POST)
      (f := Z.to_nat (msv + 1)) (s := 0) (syms := syms1) (position := 0) (r := (syms2, position)) (m1 := m0).
    all: lazymatch goal with
      | |- forall (m2 : fmem) (syms' : list (option Z)) (p' : Z) (y8 y9 y10 y13 : word), _ =>
          intros m2 syms' p' z8 z9 z10 z13 ER HPP HLS GI2;
          injection ER as E1 E2; subst syms' p';
          destruct GI2 as (TS2 & MU2 & WM2 & MI2);
          subst position;
          repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (Z_to_bv 64 128264) _ _ _ _) => fail
            | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
                let KC := fresh "KC" in if_cases KC; zify_cond KC; try (exfalso; lia)
            | _ => zstep end);
          assert (HDR2 : u8arr usegs m2 DT (le2 (Z_to_bv 64 tl) ++ le2 (Z_to_bv 64 fm)))
            by (eapply u8arr_transport; [exact HDR | exact MU2 | exact WM2 | rewrite length_app, !length_le2; cbn [disjoint_from]; lia]);
          assert (LWS : Z.of_nat (length (u16s (map (Z_to_bv 64) snext))) = 2 * (msv + 1))
            by (rewrite u16s_length, length_map, Nat2Z.inj_mul; change (Z.of_nat 2) with 2; change (Z.of_nat (length snext)) with (zlen snext); rewrite LSN; ring);
          assert (WKS2 : u8arr usegs m2 WK (u16s (map (Z_to_bv 64) snext)))
            by (eapply u8arr_transport; [exact WKS | exact MU2 | exact WM2 | rewrite LWS; cbn [disjoint_from]; lia]);
          assert (FR2 : rw_cells usegs m2 (SPV + -128) FRC)
            by (eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add disjoint_from]; lia]);
          assert (STK2 : stk usegs m2 lo (SPV + -128))
            by (eapply stk_transport_disjoint; [exact STK | exact MU2 | exact WM2 | cbn [disjoint_from]; lia]);
          assert (MU3 : munch [(SPV - 128, SPV); (DT, DT + (1 + 2^tl) * 4); (WK, WK + (2 * (msv + 1) + 2^tl + 8))] m m2)
            by (eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU2]];
                unfold sub_fp; intros x Hx; cbn [outside] in *; intuition lia);
          pose proof (wmono_trans usegs _ _ _ WM WM2) as WM3;
          eapply K; [exact HLS | exact HDR2 | exact TS2 | exact WKS2 | exact FR2 | exact STK2 | exact MU3 | exact WM3 | exact MI2]
      | |- _ => idtac end.
    all: try exact (Z_to_bv 64 0).
    all: try exact GL; try exact NCB; try exact HNCR; try exact HJT; try exact LS1; try reflexivity.
    all: try (unfold gn_inv; split; [exact TSY | split; [apply munch_refl | split; [apply wmono_refl | exact MI]]]).
    all: try (rewrite Z2Nat.id by lia; lia).
    all: try (destruct HDT as (? & ? & ?); destruct HNC as (? & ? & ?); unfold zlen in *; rewrite ?Z2Nat.id by lia; lia).
  Qed.
End GPath.
