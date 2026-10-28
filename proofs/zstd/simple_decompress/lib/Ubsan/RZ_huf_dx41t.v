(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_fkit huf411_kit_rs huf41_kit_x41ck huf413_kit_t.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.BothW Require Import AZ_hufkit42e.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41T.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl : Z).
  Hypothesis TL11 : tl = 11.
  Hypothesis NBOK : huf_nb_ok false dtb tl.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis DTA : rsk_al DT 4.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WDL := [(DST, DST + dcap); (SPV - 224, SPV - 112)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation LOC mm p0 p1 p2 p3 g0 i0 i1 i2 i3 g1 c0 c1 c2 c3 :=
    (rw_cells usegs mm (SPV + -224) [C8 p0; C8 p1; C8 p2; C8 p3; C8 g0; C8 i0; C8 i1; C8 i2; C8 i3; C8 g1;
                                     C8 c0; C8 c1; C8 c2; C8 c3]).

  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Ltac fi_walk o0 o1 o2 o3 f3 i0 i1 i2 i3 n SRC :=
    kx_auto [0x23ff8; 0x253c0] 800%nat
      [KZRange (dcap - o0) 5 (2^32); KZRange (dcap - o1) 5 (2^32); KZRange (dcap - o2) 5 (2^32); KZRange (dcap - o3) 5 (2^32);
       KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32); KZRange f3 0 (2^32);
       KZRange i0 7 (2^32); KZRange i1 7 (2^32); KZRange i2 7 (2^32); KZRange i3 7 (2^32);
       KZRange (n - i0) 8 (2^32); KZRange (n - i1) 8 (2^32); KZRange (n - i2) 8 (2^32); KZRange (n - i3) 8 (2^32);
       KZRange n 15 (2^32); KZRange dcap 5 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange DST 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47); KZAlign DT 4; KZTbl HUF_CTZ_TBL 64 1 0 0 63;
       KZImg 0x10000 0x14000; KZWr DST dcap; KZWr (SPV - 224) 112;
       KZDisj DST dcap DT 16388; KZDisj DST dcap SRC n; KZDisj (SPV - 224) 112 SRC n; KZDisj (SPV - 224) 112 DT 16388;
       KZDisj DST dcap (SPV - 224) 112]
      [(DT, 16388); (SRC, n); (0x110b8, 64); (0x11060, 8); (SPV - 224, 112)].

  Ltac fi_ipc S0 HI0 HI1 HI2 HI3 := lazymatch goal with
    | H : Z.lxor 1 (bv_unsigned (edenot ?E (EAlu ALU_SLTU _ _))) = 0 |- _ =>
        kx_sltu_in H; kx_ub_norm H;
        lazymatch type of H with context [bv_unsigned (ev E ?j)] =>
          let R := fresh "KXVR" in kx_erange R (EVar j); cbn [edenot] in R;
          lazymatch type of H with context [Z.eqb ?a ?b] =>
            replace (Z.eqb a b) with false in H
              by (symmetry; apply Z.eqb_neq; clear - R S0 HI0 HI1 HI2 HI3; Z.div_mod_to_equations; lia) end end;
        cbn [Z.b2z Z.lxor Pos.lxor] in H; discriminate H
    end.

  Ltac fi_lb7 X := let W := fresh "W" in let LW := fresh "LW" in
    assert (LW : LBW 8 X) by (clear; rewrite ?Z_to_bv_bv_unsigned; e42_lb_reload); set (W := X) in *; clearbody W.

  Ltac fi_ipr SRC := lazymatch goal with
    | H : rw_cells usegs ?m2 (SPV + -224) ?L |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
        lazymatch L with context [Z_to_bv 64 (?i + (SRC + -1 * (bv_unsigned (ev ?E ?j) / 8)))] =>
          let R := fresh "KXVR" in kx_erange R (EVar j); cbn [edenot] in R;
          let Y := fresh "Y" in let YR := fresh "YR" in
          set (Y := bv_unsigned (ev E j) / 8) in *;
          assert (YR : 0 <= Y <= 7) by (subst Y; clear - R; Z.div_mod_to_equations; lia);
          clearbody Y; clear R;
          replace (i + (SRC + -1 * Y)) with (SRC + (i + -1 * Y)) in * by ring
        end
    end.

  Ltac fi_junk := lazymatch goal with
    | KXA : atoms_ok _ ?E |- _ =>
        repeat match goal with
        | H : ?T |- _ => lazymatch T with rw_cells _ _ _ _ => fail | context [E] => clear H end
        end
    end.


  Lemma x41_fi : forall (r : nat) mb mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3 f0 f1 f2 f3 (c0 c1 c2 c3 g0 g1 : word)
      (x9 x14 x15 x18 x19 x20 x21 x22 x26 x27 : word),
    munch WDL mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    LOC mm (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) g0
           (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) g1 c0 c1 c2 c3 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 -> (DST + dcap <= SRC \/ SRC + n <= DST) ->
    (SRC + n <= lo \/ SPV <= SRC) ->
    (1 <= r)%nat -> f0 = o0 + 5 * Z.of_nat r -> f1 = o1 + 5 * Z.of_nat r -> f2 = o2 + 5 * Z.of_nat r -> f3 = o3 + 5 * Z.of_nat r ->
    0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 -> f0 <= dcap -> f1 <= dcap -> f2 <= dcap -> f3 <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    (forall mm' I0 I1 I2 I3 (d0 d1 d2 d3 : word) (y8 y9 y15 y18 y19 y20 y22 y27 : word),
        munch WDL mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        LOC mm' (Z_to_bv 64 (DST + f0)) (Z_to_bv 64 (DST + f1)) (Z_to_bv 64 (DST + f2)) (Z_to_bv 64 (DST + f3)) g0
                (Z_to_bv 64 (SRC + I0)) (Z_to_bv 64 (SRC + I1)) (Z_to_bv 64 (SRC + I2)) (Z_to_bv 64 (SRC + I3)) g1 d0 d1 d2 d3 ->
        0 <= I0 -> 0 <= I1 -> 0 <= I2 -> 0 <= I3 -> I0 + 8 <= n -> I1 + 8 <= n -> I2 + 8 <= n -> I3 + 8 <= n ->
        LBW 8 d0 -> LBW 8 d1 -> LBW 8 d2 -> LBW 8 d3 ->
        evt usegs POST (ST 0x23618 mm' (Z_to_bv 64 (SPV + -184)) (Z_to_bv 64 (-16)) (Z_to_bv 64 (SPV + -224)) (Z_to_bv 64 (-25)) y8 y9
                          (Z_to_bv 64 0x110b8) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 0x112f0) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (DST + f3)) y15
                          (Z_to_bv 64 (SPV + -144)) (Z_to_bv 64 (-17)) y18 y19 y20 x21 y22 (Z_to_bv 64 5) (Z_to_bv 64 6) (Z_to_bv 64 (DST + f3))
                          (Z_to_bv 64 (SRC + I0)) y27 (Z_to_bv 64 (-24)) (Z_to_bv 64 2) (Z_to_bv 64 3) (Z_to_bv 64 4))) ->
    evt usegs POST (ST 0x236ac mm (Z_to_bv 64 (SPV + -184)) (Z_to_bv 64 (-16)) (Z_to_bv 64 (SPV + -224)) (Z_to_bv 64 (-25)) c0 x9
                      (Z_to_bv 64 0x110b8) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 0x112f0) (Z_to_bv 64 (-1 * DT + -5)) x14 x15
                      (Z_to_bv 64 (SPV + -144)) (Z_to_bv 64 (-17)) x18 x19 x20 x21 x22 (Z_to_bv 64 5) (Z_to_bv 64 6) (Z_to_bv 64 (DST + f3))
                      x26 x27 (Z_to_bv 64 (-24)) (Z_to_bv 64 2) (Z_to_bv 64 3) (Z_to_bv 64 4)).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    pose proof (rsk_al_e _ _ DTA) as DTA'.
    assert (NB11 : huf_nb_ok false dtb 11) by (rewrite <- TL11; exact NBOK).
    induction r as [|r IH]; intros mb mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3 f0 f1 f2 f3 c0 c1 c2 c3 g0 g1
      x9 x14 x15 x18 x19 x20 x21 x22 x26 x27
      MU WM MI OUT DTB LC SB SL S0 S1 SL32 DJS DKS HR HF0 HF1 HF2 HF3 HO0 HO1 HO2 HO3 HD0 HD1 HD2 HD3
      HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 HB0 HB1 HB2 HB3 K;
      [exfalso; lia|].
    assert (TBLC : tbl_in usegs mm HUF_CTZ_TBL 64 1 0 0 63) by exact (huf_ctz_tbl mm MI).
    pose proof (lbw_pos _ _ HB0). pose proof (lbw_pos _ _ HB1). pose proof (lbw_pos _ _ HB2). pose proof (lbw_pos _ _ HB3).
    assert (KS : SRC + n <= SPV - 224 \/ SPV - 112 <= SRC) by (clear - DKS LO; lia).
    assert (KD : DST + dcap <= SPV - 224 \/ SPV - 112 <= DST) by (clear - OS1 LO; lia).
    assert (KT : DT + 16388 <= SPV - 224 \/ SPV - 112 <= DT) by (clear - DJ3 LO; lia).
    assert (DTR : 0 <= DT /\ DT + 16388 < 2 ^ 64) by lia.
    fi_walk o0 o1 o2 o3 f3 i0 i1 i2 i3 n SRC.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x253c0) _ _ _ _) =>
            first [ h413t_ctz DTB DL NB11 DTR
                  | fi_ipc S0 HI0 HI1 HI2 HI3
                   | x41_ck ]
         | _ => idtac end.
    all: kx_ev_ranges; kx_mem.
    all: rewrite ?Z_to_bv_bv_unsigned.
    all: replace (DST + o0 + 5) with (DST + (o0 + 5)) in * by lia; replace (DST + o1 + 5) with (DST + (o1 + 5)) in * by lia;
         replace (DST + o2 + 5) with (DST + (o2 + 5)) in * by lia; replace (DST + o3 + 5) with (DST + (o3 + 5)) in * by lia.
    all: clear DTA'; fi_ipr SRC; fi_ipr SRC; fi_ipr SRC; fi_ipr SRC; fi_junk.
    all: lazymatch goal with
         | H : rw_cells usegs ?m2 (SPV + -224) [_; _; _; _; _; _; _; _; _; _; C8 ?X0; C8 ?X1; C8 ?X2; C8 ?X3]
           |- evt _ _ (MS _ _ _ _ _ ?m2 _) => fi_lb7 X0; fi_lb7 X1; fi_lb7 X2; fi_lb7 X3
         end.
    all: lazymatch goal with
         | H : rw_cells usegs ?m2 (SPV + -224) [_; _; _; _; _; C8 (Z_to_bv 64 (_ + ?I0)); C8 (Z_to_bv 64 (_ + ?I1));
                                               C8 (Z_to_bv 64 (_ + ?I2)); C8 (Z_to_bv 64 (_ + ?I3)); _; _; _; _; _]
           |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
             zstep; if_cases KB; zify_cond KB;
             [ eapply (IH mb m2 SRC n src I0 I1 I2 I3 (o0 + 5) (o1 + 5) (o2 + 5) (o3 + 5) f0 f1 f2 f3);
               try eassumption; try lia; intros; eapply K; try eassumption; lia
             | zstep; replace (o0 + 5) with f0 in * by lia; replace (o1 + 5) with f1 in * by lia;
               replace (o2 + 5) with f2 in * by lia; replace (o3 + 5) with f3 in * by lia;
               eapply (K m2 I0 I1 I2 I3); try eassumption; try lia ]
         end.
  Qed.

End DX41T.
