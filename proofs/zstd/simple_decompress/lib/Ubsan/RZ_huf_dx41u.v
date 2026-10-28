(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2 ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_fkit RZ_huf_dx41r RZ_huf_dx41r2 RZ_huf_dx41t huf411_kit_rs huf41_kit_x41ck.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.BothW Require Import AZ_hufkit42e.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41U.
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
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw ilo oew ie0 ie1 ie2 ie3 :=
    (rw_cells usegs mm (SPV + -376) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 bt0; C8 bt1; C8 bt2; C8 bt3; C8 dtw; C8 ilo; C8 oew; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).
  Notation LOC mm p0 p1 p2 p3 g0 i0 i1 i2 i3 g1 c0 c1 c2 c3 :=
    (rw_cells usegs mm (SPV + -224) [C8 p0; C8 p1; C8 p2; C8 p3; C8 g0; C8 i0; C8 i1; C8 i2; C8 i3; C8 g1; C8 c0; C8 c1; C8 c2; C8 c3]).
  Notation TOP mm g2 := (rw_cells usegs mm (SPV + -112) [C8 g2]).
  Notation M5 := (Z_to_bv 64 14757395258967641293).
  Notation M7 := (Z_to_bv 64 2635249153387078803).
  Notation FRS0 mm w0 w1 w2 w3 w4 w5 w6 SRC n :=
    (FRA mm w0 w1 w2 w3 w4 w5 w6 M5 M7 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 SRC) (Z_to_bv 64 DT) (Z_to_bv 64 n) (Z_to_bv 64 dcap)
         (Z_to_bv 64 DST) (Z_to_bv 64 SRC) (Z_to_bv 64 (DST + dcap))).
  Notation ARGS0 mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 SRC l1 l2 l3 :=
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 SRC) (Z_to_bv 64 (DST + dcap))
          (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))).
  Notation LOC0 mm o0 o1 o2 o3 g0 SRC i0 i1 i2 i3 g1 c0 c1 c2 c3 :=
    (LOC mm (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) g0
         (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) g1 c0 c1 c2 c3).
  Notation X41PF := (RZ_huf_dx41r.X41PF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41_fi := (RZ_huf_dx41t.x41_fi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl TL11 NBOK DJ3 DTA).
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Ltac x41_mulhu_rb :=
    repeat match goal with
    | KXA : atoms_ok ?zs ?E |- _ =>
        let go a b :=
            let nz := kx_len zs in let ua := kx_uz E zs nz a in let ub := kx_uz E zs nz b in
            let HD := fresh "HD" in
            assert (HD : bv_unsigned (edenot E (EMd M_MULHU a b)) = ua * ub / 2 ^ 64)
              by (change (edenot E (EMd M_MULHU a b)) with (mul_div M_MULHU (edenot E a) (edenot E b)); rewrite KXS.u_mulhu64;
                  rewrite (uz_sound zs E a KXA), (uz_sound zs E b KXA); reflexivity);
            rewrite HD in *; clear HD in
        match goal with
        | |- context [bv_unsigned (edenot E (EMd M_MULHU ?a ?b))] => go a b
        | H : context [bv_unsigned (edenot E (EMd M_MULHU ?a ?b))] |- _ => go a b
        end
    end.

  Lemma x41_l5 : forall x, 0 <= x < 2^64 -> x * 14757395258967641293 / 2^64 / 4 = x / 5.
  Proof using. intros x Hx. Z.div_mod_to_equations; lia. Qed.
  Lemma x41_l7 : forall x, 0 <= x < 2^64 ->
    ((x + -1 * (x * 2635249153387078803 / 2^64)) / 2 + x * 2635249153387078803 / 2^64) / 4 = x / 7.
  Proof using.
    intros x Hx.
    set (h := x * 2635249153387078803 / 2^64).
    assert (Hh : 0 <= h <= x) by (subst h; Z.div_mod_to_equations; lia).
    subst h. Z.div_mod_to_equations; lia.
  Qed.

  Lemma x41pf_tr : forall mm mm', X41PF mm -> munch WDL mm mm' -> wmono usegs mm mm' -> X41PF mm'.
  Proof using CTX DJ3.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm mm' (SV & STK & MU & WM) MU' WM'.
    split; [|split; [|split]].
    - eapply (rw_cells_transport usegs _ mm mm' _ _ SV MU' WM');
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - eapply (stk_transport_disjoint usegs _ mm mm' _ _ STK MU' WM'); cbn [disjoint_from]; lia.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. unfold sub_fp; cbn [outside]; intros; lia.
    - exact (wmono_trans usegs m0 mm mm' WM WM').
  Qed.

  Ltac f2_merge :=
    lazymatch goal with
    | LC : rw_cells usegs ?m (SPV + -224) ?cs, TP : rw_cells usegs ?m (SPV + -112) [C8 ?g] |- _ =>
        let LT := fresh "LT" in let lj := fresh "lj" in let LJ := fresh "LJ" in
        replace (SPV + -112) with (SPV + -224 + Z.of_nat (cells_size cs)) in TP
          by (cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
        pose proof (proj2 (rw_cells_app usegs m (SPV + -224) cs [C8 g]) (conj LC TP)) as LT;
        destruct (Tac.rw_cells_forget usegs m (SPV + -224) _ LT) as [lj LJ];
        cbn [cells_size csize Nat.add app] in LJ; clear LT
    end.

  Lemma x41_f2 : forall mm SRC n src l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (c0 c1 c2 c3 g0 g1 g2 : word)
      (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 w0 w1 w2 w3 w4 w5 w6 : word)
      (x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRS0 mm w0 w1 w2 w3 w4 w5 w6 SRC n -> ARGS0 mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 SRC l1 l2 l3 ->
    LOC0 mm o0 o1 o2 o3 g0 SRC i0 i1 i2 i3 g1 c0 c1 c2 c3 -> TOP mm g2 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 < dcap -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    0 <= o0 <= dcap -> 0 <= o1 <= dcap -> 0 <= o2 <= dcap -> 0 <= o3 <= dcap ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    evt usegs POST (ST 0x22660 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 HUF_CTZ_TBL) x11 (Z_to_bv 64 0x112f0) x13 x14 x15 x16 x17 x18 x19 x20
                      (Z_to_bv 64 (DT + 4)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm SRC n src l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 g0 g1 g2 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      w0 w1 w2 w3 w4 w5 w6 x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      PV MI OUT DTB FS AS LC TP SB SL S0 S1 SL32 DJS DKS HDC HL1 HL2 HL3 HLN HI0 HJ0 HI1 HJ1 HI2 HJ2 HI3 HJ3 HO0 HO1 HO2 HO3
      HB0 HB1 HB2 HB3.
    pose proof (lbw_pos _ _ HB0) as HC0. pose proof (lbw_pos _ _ HB1) as HC1.
    pose proof (lbw_pos _ _ HB2) as HC2. pose proof (lbw_pos _ _ HB3) as HC3.
    destruct PV as (SV & STK & MUP & WMP).
    kx_auto [0x226fc] 60%nat
      [KZImg 0x10000 0x14000; KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange SRC 4096 (2^47);
       KZRange SPV 4096 (2^47); KZRange DT 4096 (2^47); KZWr (SPV - 376) 152; KZWr (SPV - 512) 136]
      [(SPV - 512, 136); (SPV - 376, 152); (SPV - 224, 112)].
    all: kx_ev_ranges; kx_mem.
    all: replace ((dcap + 3) mod 2 ^ 64 / 4) with ((dcap + 3) / 4) by (rewrite Z.mod_small by lia; reflexivity).
    all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia).
    all: replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
    all: f2_merge.
    all: pose proof (conj SV (conj STK (conj MUP WMP))) as PV2.
    all: eapply RZ_huf_dx41r2.x41_f3_0 with (eprev := 0) (q := (dcap + 3) / 4) (SRC := SRC) (n := n) (src := src)
           (i0 := i0) (o0 := o0) (i1 := i1) (o1 := o1) (i2 := i2) (o2 := o2) (i3 := i3) (o3 := o3)
           (bt0 := c0) (bt1 := c1) (bt2 := c2) (bt3 := c3) (lj := lj)
           (ie0 := Z_to_bv 64 (SRC + 6)) (ie1 := Z_to_bv 64 (SRC + 6 + l1)) (ie2 := Z_to_bv 64 (SRC + 6 + l1 + l2))
           (ie3 := Z_to_bv 64 (SRC + 6 + l1 + l2 + l3)).
    all: first [ exact PV2 | eassumption | lia | (rewrite u_small by lia; lia) ].
  Qed.

  Lemma x41_fo : forall (k : nat) mm SRC n src l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (c0 c1 c2 c3 g0 g1 g2 : word)
      (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 w0 w1 w2 w3 w4 w5 w6 : word)
      (x8 x9 x15 x18 x19 x20 x22 x25 x27 : word),
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRS0 mm w0 w1 w2 w3 w4 w5 w6 SRC n -> ARGS0 mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 SRC l1 l2 l3 ->
    LOC0 mm o0 o1 o2 o3 g0 SRC i0 i1 i2 i3 g1 c0 c1 c2 c3 -> TOP mm g2 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 < dcap -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    0 <= o0 <= o3 -> 0 <= o1 <= o3 -> 0 <= o2 <= o3 -> o3 <= dcap ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    dcap - o3 < Z.of_nat k ->
    evt usegs POST (ST 0x23618 mm (Z_to_bv 64 (SPV + -184)) (Z_to_bv 64 (-16)) (Z_to_bv 64 (SPV + -224)) (Z_to_bv 64 (-25)) x8 x9
                      (Z_to_bv 64 HUF_CTZ_TBL) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 0x112f0) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (DST + o3)) x15
                      (Z_to_bv 64 (SPV + -144)) (Z_to_bv 64 (-17)) x18 x19 x20 (Z_to_bv 64 (DT + 4)) x22 (Z_to_bv 64 5) (Z_to_bv 64 6) x25
                      (Z_to_bv 64 (SRC + i0)) x27 (Z_to_bv 64 (-24)) (Z_to_bv 64 2) (Z_to_bv 64 3) (Z_to_bv 64 4)).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mm SRC n src l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 g0 g1 g2
      av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 w0 w1 w2 w3 w4 w5 w6 x8 x9 x15 x18 x19 x20 x22 x25 x27
      PV MI OUT DTB FS AS LC TP SB SL S0 S1 SL32 DJS DKS HDC HL1 HL2 HL3 HLN HI0 HJ0 HI1 HJ1 HI2 HJ2 HI3 HJ3 HO0 HO1 HO2 HO3
      HB0 HB1 HB2 HB3 HK;
      [exfalso; lia|].
    kx_auto [0x236ac; 0x22660; 0x253c0] 60%nat
      [KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
       KZRange i0 0 (2^32); KZRange i1 0 (2^32); KZRange i2 0 (2^32); KZRange i3 0 (2^32);
       KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange SRC 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DT 4096 (2^47)]
      [(SPV - 512, 136); (SPV - 224, 112)].
    all: try x41_ck.
    all: x41_mulhu_rb.
    all: kx_strip_mod.
    all: rewrite ?(x41_l5 (-1 * o3 + dcap) ltac:(lia)) in *.
    all: rewrite ?(x41_l7 i0 ltac:(lia)) in *.
    all: assert (HQ5 : 0 <= (dcap - o3) / 5 /\ 5 * ((dcap - o3) / 5) <= dcap - o3) by (Z.div_mod_to_equations; lia).
    all: assert (HQ7 : 0 <= i0 / 7 /\ 7 * (i0 / 7) <= i0) by (Z.div_mod_to_equations; lia).
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x253c0) _ _ _ _) => exfalso; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22660) _ _ _ _) =>
             eapply (x41_f2 mm SRC n src l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 g0 g1 g2
                       av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 w0 w1 w2 w3 w4 w5 w6);
             first [ exact PV | eassumption | lia ]
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + (_ + 5 * ?R))) _ _ _ _ _ _) _
                          (Z_to_bv 64 0x236ac) _ _ _ _) =>
             assert (HR1 : 1 <= R) by lia;
             assert (HR5 : 5 * R <= dcap - o3) by lia;
             assert (HR7 : 7 * R <= i0) by lia;
             assert (HIO : i0 <= i1 /\ i1 <= i2 /\ i2 <= i3) by lia;
             set (RR := R) in *; clearbody RR;
             eapply (x41_fi (Z.to_nat RR) mm mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3
                       (o0 + 5 * RR) (o1 + 5 * RR) (o2 + 5 * RR) (o3 + 5 * RR))
         end.
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | _ => first [ apply munch_refl | apply wmono_refl | eassumption | lia ]
         end.
    all: intros mm' I0 I1 I2 I3 d0 d1 d2 d3; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
         intros MU' WM' MI' OUT' DTB' LC' HI0' HI1' HI2' HI3' HN0' HN1' HN2' HN3' HB0' HB1' HB2' HB3'.
    all: pose proof (x41pf_tr mm mm' PV MU' WM') as PV';
         pose proof (rw_cells_transport usegs _ mm mm' _ _ FS MU' WM') as FS';
         pose proof (rw_cells_transport usegs _ mm mm' _ _ AS MU' WM') as AS';
         pose proof (rw_cells_transport usegs _ mm mm' _ _ TP MU' WM') as TP';
         pose proof (bytes_at_transport usegs _ mm mm' SRC src SB MU') as SB'.
    all: cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FS', AS', TP', SB'.
    all: specialize (FS' ltac:(lia)); specialize (AS' ltac:(lia)); specialize (TP' ltac:(lia)); specialize (SB' ltac:(lia)).
    all: eapply (IH mm' SRC n src l1 l2 l3 I0 I1 I2 I3 (o0 + 5 * RR) (o1 + 5 * RR) (o2 + 5 * RR) (o3 + 5 * RR) d0 d1 d2 d3 g0 g1 g2
                 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 w0 w1 w2 w3 w4 w5 w6);
         first [ exact PV' | eassumption | lia ].
  Qed.

End DX41U.
(* [comment removed for export] *)
(* [comment removed for export] *)
