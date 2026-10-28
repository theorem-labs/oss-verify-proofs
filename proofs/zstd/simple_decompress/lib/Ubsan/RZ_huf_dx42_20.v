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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_fkit2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.BothW Require Import AZ_hufkit42e.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_20.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis TL11 : tl = 11.
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WDL := [(DST, DST + dcap); (SPV - 232, SPV - 104)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation LOC mm e0 e1 e2 e3 p0 p1 p2 p3 i0 i1 i2 i3 c0 c1 c2 c3 :=
    (rw_cells usegs mm (SPV + -232) [C8 e0; C8 e1; C8 e2; C8 e3; C8 p0; C8 p1; C8 p2; C8 p3; C8 i0; C8 i1; C8 i2; C8 i3;
                                     C8 c0; C8 c1; C8 c2; C8 c3]).

  (* [comment removed for export] *)
  Lemma x42_tblf : forall mm, bytes_at usegs mm DT dtb -> tbl_in usegs mm DT 8196 4 7 1 2.
  Proof using X2OK TL11.
    intros mm DTB i I0 I1.
    destruct (X2OK i) as (b & Hn & Hr); [rewrite TL11; lia|].
    replace (DT + 4 * i + 7) with (DT + (4 * i + 7)) by lia.
    rewrite (rdval_bytes_at_1 usegs mm DT dtb (4 * i + 7) b DTB ltac:(lia) Hn). exact Hr.
  Qed.
  Lemma x42_tbnf : forall mm, bytes_at usegs mm DT dtb -> tbl_in usegs mm DT 8196 4 6 0 11.
  Proof using NBOK TL11.
    intros mm DTB i I0 I1.
    destruct (NBOK i) as (b & Hn & Hr); [rewrite TL11; lia|].
    replace (DT + 4 * i + 6) with (DT + (4 * i + 6)) by lia.
    rewrite (rdval_bytes_at_1 usegs mm DT dtb (4 * i + 6) b DTB ltac:(lia) Hn). pose proof (bv_unsigned_in_range 8 b). rewrite TL11 in Hr. lia.
  Qed.

  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Ltac fi_tp := lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x220dc) _ _ _ _) => kx_trap_fast
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2213c) _ _ _ _) => kx_trap_fast
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22180) _ _ _ _) => kx_trap_fast
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22188) _ _ _ _) => kx_trap_fast
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22190) _ _ _ _) => kx_trap_fast
    | _ => idtac end.

  Ltac fi_walk STOPS FUEL o0 o1 o2 o3 i0 i1 i2 i3 OL n SRC :=
    kx_auto STOPS FUEL
      [KZRange (dcap - o0) 10 (2^32); KZRange (dcap - o1) 10 (2^32); KZRange (dcap - o2) 10 (2^32); KZRange (dcap - o3) 10 (2^32);
       KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32); KZRange OL 0 (2^32);
       KZRange i0 7 (2^32); KZRange i1 7 (2^32); KZRange i2 7 (2^32); KZRange i3 7 (2^32);
       KZRange (n - i0) 8 (2^32); KZRange (n - i1) 8 (2^32); KZRange (n - i2) 8 (2^32); KZRange (n - i3) 8 (2^32);
       KZRange n 15 (2^32); KZRange dcap 10 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange DST 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47); KZTbl HUF_CTZ_TBL2 64 1 0 0 63; KZTbl DT 8196 4 7 1 2; KZTbl DT 8196 4 6 0 11;
       KZImg 0x10000 0x14000; KZWr DST dcap; KZWr (SPV - 232) 128;
       KZDisj DST dcap DT 16388; KZDisj DST dcap SRC n; KZDisj (SPV - 232) 128 SRC n; KZDisj (SPV - 232) 128 DT 16388;
       KZDisj DST dcap (SPV - 232) 128]
      [(DT, 16388); (SRC, n); (0x11078, 64); (0x11060, 8); (SPV - 232, 128)].

  Ltac fi_ctz := lazymatch goal with
    | H : bv_unsigned (edenot ?E ?X) = 0, A : atoms_ok _ ?E |- _ =>
        let LW := fresh "LW" in
        assert (LW : LBW 63 (edenot E X)) by e42_lb_chain A;
        exfalso; exact (lbw_nz _ _ LW H)
    end.

  Ltac fi_lb7 X := let W := fresh "W" in let LW := fresh "LW" in
    set (W := X) in *; assert (LW : LBW 8 W) by (subst W; rewrite ?Z_to_bv_bv_unsigned; e42_lb_reload); clearbody W.

  Ltac fi_ipc := lazymatch goal with
    | H : Z.lxor 1 (bv_unsigned (edenot ?E (EAlu ALU_SLTU _ _))) = 0 |- _ =>
        kx_sltu_in H; kx_ub_norm H;
        lazymatch type of H with context [bv_unsigned (ev E ?j)] =>
          let R := fresh "KXVR" in kx_erange R (EVar j); cbn [edenot] in R end;
        lazymatch type of H with context [Z.eqb ?a ?b] =>
          replace (Z.eqb a b) with false in H by (symmetry; apply Z.eqb_neq; clear H; Z.div_mod_to_equations; lia) end;
        cbn [Z.b2z Z.lxor Pos.lxor] in H; discriminate H
    end.

  Lemma x42_fi : forall (r : nat) mb mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3 OL E0 E1 E2 E3
      (c0 c1 c2 c3 e0 e1 e2 e3 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 : word)
      (x9 x11 x14 x19 x21 x24 x28 : word),
    munch WDL mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    LOC mm e0 e1 e2 e3 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 -> (DST + dcap <= SRC \/ SRC + n <= DST) ->
    (SRC + n <= lo \/ SPV <= SRC) ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r ->
    0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= E0 -> o1 + 10 * Z.of_nat r <= E1 -> o2 + 10 * Z.of_nat r <= E2 -> o3 + 10 * Z.of_nat r <= E3 ->
    E0 <= dcap -> E1 <= dcap -> E2 <= dcap -> E3 <= dcap -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    (forall mm' I0 I1 I2 I3 F0 F1 F2 F3 (d0 d1 d2 d3 : word) (y5 y7 y8 y10 y12 y20 y21 y24 y26 y27 y28 y29 y31 : word),
        munch WDL mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        LOC mm' e0 e1 e2 e3 (Z_to_bv 64 (DST + F0)) (Z_to_bv 64 (DST + F1)) (Z_to_bv 64 (DST + F2)) (Z_to_bv 64 (DST + F3))
                (Z_to_bv 64 (SRC + I0)) (Z_to_bv 64 (SRC + I1)) (Z_to_bv 64 (SRC + I2)) (Z_to_bv 64 (SRC + I3)) d0 d1 d2 d3 ->
        0 <= I0 -> 0 <= I1 -> 0 <= I2 -> 0 <= I3 -> I0 + 8 <= n -> I1 + 8 <= n -> I2 + 8 <= n -> I3 + 8 <= n ->
        o0 <= F0 <= E0 -> o1 <= F1 <= E1 -> o2 <= F2 <= E2 -> o3 + 5 <= F3 <= E3 ->
        LBW 8 d0 -> LBW 8 d1 -> LBW 8 d2 -> LBW 8 d3 ->
        evt usegs POST (ST 0x20fe4 mm' (Z_to_bv 64 (-25)) y5 (Z_to_bv 64 (DST + F3)) y7 y8 (Z_to_bv 64 (SRC + I2)) y10 (Z_to_bv 64 (SRC + I3)) y12
                          (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC + I0)) (Z_to_bv 64 (DST + F1)) (Z_to_bv 64 (DST + F2)) (Z_to_bv 64 (SPV + -168))
                          (Z_to_bv 64 (DST + F0)) (Z_to_bv 64 (SRC + I1)) y20 y21 d0 (Z_to_bv 64 (SPV + -136)) y24 (Z_to_bv 64 (-16)) y26 y27 y28 y29
                          (Z_to_bv 64 (-1 * DT + -5)) y31)) ->
    evt usegs POST (ST 0x2112c mm (Z_to_bv 64 (-25)) (Z_to_bv 64 0x110e0) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) c1 x9 (Z_to_bv 64 (DST + OL)) x11
                      (Z_to_bv 64 0x11078) (Z_to_bv 64 (DT + 4)) x14 (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (SPV + -168))
                      (Z_to_bv 64 (DST + o0)) x19 (Z_to_bv 64 (SRC + i1)) x21 c0 (Z_to_bv 64 (SPV + -136)) x24 (Z_to_bv 64 (-16)) c3 (Z_to_bv 64 (SRC + i2)) x28 c2
                      (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (SRC + i3))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction r as [|r IH]; intros mb mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3 OL E0 E1 E2 E3 c0 c1 c2 c3 e0 e1 e2 e3 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11
      x9 x11 x14 x19 x21 x24 x28
      MU WM MI OUT DTB LC SB SL S0 S1 SL32 DJS DKS HR HOL HO0 HO1 HO2 HO3 HD0 HD1 HD2 HD3 HE0 HE1 HE2 HE3 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3
      HB0 HB1 HB2 HB3 K;
      [exfalso; lia|].
    assert (TBLC : tbl_in usegs mm HUF_CTZ_TBL2 64 1 0 0 63) by exact (huf_ctz_tbl2 mm MI).
    assert (TBL : tbl_in usegs mm DT 8196 4 7 1 2) by (apply x42_tblf; exact DTB).
    assert (TBN : tbl_in usegs mm DT 8196 4 6 0 11) by (apply x42_tbnf; exact DTB).
    pose proof (lbw_pos _ _ HB0). pose proof (lbw_pos _ _ HB1). pose proof (lbw_pos _ _ HB2). pose proof (lbw_pos _ _ HB3).
    assert (KS : SRC + n <= SPV - 232 \/ SPV - 104 <= SRC) by (clear - DKS LO; lia).
    assert (KD : DST + dcap <= SPV - 232 \/ SPV - 104 <= DST) by (clear - OS1 LO; lia).
    assert (KT : DT + 16388 <= SPV - 232 \/ SPV - 104 <= DT) by (clear - DJ3 LO; lia).
    fi_walk [0x2199c; 0x220dc; 0x2213c; 0x22180; 0x22188; 0x22190] 600%nat o0 o1 o2 o3 i0 i1 i2 i3 OL n SRC.
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x22180) _ _ _ _) => first [ fi_ctz | fi_ipc ] | _ => idtac end.
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2199c) _ _ _ _) => idtac | _ => fi_tp end.
    all: kx_ev_ranges; kx_mem.
    all: rewrite ?Z_to_bv_bv_unsigned.
    all: lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ ?X1 _ _ _ _ _ _ _ _ _ _ _ _ _ ?X0 _ _ _ ?X3 _ _ ?X2 _ _) _ _ _ _ _ _) =>
           fi_lb7 X0; fi_lb7 X1; fi_lb7 X2; fi_lb7 X3 end.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ (Z_to_bv 64 (DST + ?F3)) (Z_to_bv 64 (_ + ?I0)) _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?F1)) (Z_to_bv 64 (DST + ?F2)) _
                               (Z_to_bv 64 (DST + ?F0)) _ (Z_to_bv 64 (_ + ?I1)) _ _ _ _ _ _ (Z_to_bv 64 (_ + ?I2)) _ _ _ (Z_to_bv 64 (_ + ?I3))) _ _ _ _ ?m2 _) =>
             zstep; if_cases KB; zify_cond KB;
             [ eapply (IH mb m2 SRC n src I0 I1 I2 I3 F0 F1 F2 F3 OL E0 E1 E2 E3);
               try eassumption; try lia; intros; eapply K; try eassumption; lia
             | zstep; eapply (K m2 I0 I1 I2 I3 F0 F1 F2 F3); try eassumption; try lia ]
         end.
  Qed.

End DX42_20.
