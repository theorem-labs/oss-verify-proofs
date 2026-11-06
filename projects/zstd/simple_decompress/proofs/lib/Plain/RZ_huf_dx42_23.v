(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_fkit2 RZ_huf_dx41r RZ_huf_dx42_5 RZ_huf_dx42_20 RZ_huf_dx42_22a RZ_huf_dx42_22b.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_23.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis TL11 : tl = 11.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation WDF := [(DST, DST + dcap); (SPV - 416, SPV - 216)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 :=
    (rw_cells psegs mm (SPV + -416) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19]).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation WD4 := [(DST, DST + dcap); (SPV - 256, SPV - 216)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells psegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).

  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw ilo oew ie0 ie1 ie2 ie3 :=
    (rw_cells psegs mm (SPV + -256) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 bt0; C8 bt1; C8 bt2; C8 bt3; C8 dtw; C8 ilo; C8 oew; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).
  Notation X41PF := (RZ_huf_dx41r.X41PF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41pf_transport := (RZ_huf_dx41r.x41pf_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation x42_f3_0 := (RZ_huf_dx42_22b.x42_f3_0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK TL11 DJ3).
  Notation x42_fi := (RZ_huf_dx42_20.x42_fi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK TL11).
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  (* [comment removed for export] *)
  Ltac x42_mulhu_rb :=
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

  Lemma x42_l10 : forall x, 0 <= x < 2^64 -> x mod 2^64 * 14757395258967641293 / 2^64 / 8 = x / 10.
  Proof using. intros x Hx. rewrite (Z.mod_small x) by lia. Z.div_mod_to_equations; lia. Qed.
  Lemma x42_l7 : forall x, 0 <= x < 2^64 ->
    ((x + -1 * (x mod 2^64 * 2635249153387078803 / 2^64)) mod 2^64 / 2 + x mod 2^64 * 2635249153387078803 / 2^64) mod 2^64 / 4 = x / 7.
  Proof using.
    intros x Hx. rewrite (Z.mod_small x) by lia.
    set (h := x * 2635249153387078803 / 2^64).
    assert (Hh : 0 <= h <= x) by (subst h; Z.div_mod_to_equations; lia).
    replace (x + -1 * h) with (x - h) by lia. rewrite (Z.mod_small (x - h)) by lia.
    rewrite (Z.mod_small ((x - h) / 2 + h)) by (Z.div_mod_to_equations; lia).
    subst h. Z.div_mod_to_equations; lia.
  Qed.

  Lemma x42_fo_eqs : forall q dcap o0 o1 o2 o3 i0 n,
    0 <= o0 <= q -> 0 <= o1 <= 2 * q -> 0 <= o2 <= 3 * q -> 0 <= o3 <= dcap -> 0 <= q -> 3 * q <= dcap -> dcap < 2^32 ->
    0 <= i0 -> i0 + 8 <= n -> n < 2^32 ->
    ((-1 * o0 + q) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (q - o0) / 10) /\
    ((-1 * o1 + 2 * q) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (2 * q - o1) / 10) /\
    ((-1 * o2 + 3 * q) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (3 * q - o2) / 10) /\
    ((-1 * o3 + dcap) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (dcap - o3) / 10) /\
    (((i0 + -1 * (i0 mod 2^64 * 2635249153387078803 / 2^64)) mod 2^64 / 2 + i0 mod 2^64 * 2635249153387078803 / 2^64) mod 2^64 / 4 = i0 / 7) /\
    (0 <= (q - o0) / 10 /\ 10 * ((q - o0) / 10) <= q - o0) /\ (0 <= (2 * q - o1) / 10 /\ 10 * ((2 * q - o1) / 10) <= 2 * q - o1) /\
    (0 <= (3 * q - o2) / 10 /\ 10 * ((3 * q - o2) / 10) <= 3 * q - o2) /\ (0 <= (dcap - o3) / 10 /\ 10 * ((dcap - o3) / 10) <= dcap - o3) /\
    (0 <= i0 / 7 /\ 7 * (i0 / 7) <= i0).
  Proof using.
    intros q dcap' o0 o1 o2 o3 i0 n H0 H1 H2 H3 HQ HQ3 HD HI HJ HN.
    split; [rewrite x42_l10 by lia; f_equal; lia|]. split; [rewrite x42_l10 by lia; f_equal; lia|].
    split; [rewrite x42_l10 by lia; f_equal; lia|]. split; [rewrite x42_l10 by lia; f_equal; lia|].
    split; [apply x42_l7; lia|].
    repeat split; Z.div_mod_to_equations; lia.
  Qed.

  Lemma x42_f2 : forall mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3
      (ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3 : word)
      (x1 x6 x8 x9 x11 x12 x13 x18 x19 x20 x21 x22 x24 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w15 w16 w17 w18 w19 : word),
    X41PF mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + dcap)) w15 w16 w17 w18 w19 ->
    ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw (Z_to_bv 64 SRC) oew ie0 ie1 ie2 ie3 ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 < dcap -> 0 <= i0 -> i0 + 8 <= n -> 0 <= o0 -> 0 <= i1 -> i1 + 8 <= n -> 0 <= o1 -> 0 <= i2 -> i2 + 8 <= n -> 0 <= o2 -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 -> o0 <= dcap -> o1 <= dcap -> o2 <= dcap -> o3 <= dcap ->
    evt psegs POST (ST 0x1efe4 mm x1 (Z_to_bv 64 (SRC + i0)) x6 (Z_to_bv 64 (DST + o2)) x8 x9 (Z_to_bv 64 (DT + 4)) x11 x12 x13 (Z_to_bv 64 69880) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i1)) x18 x19 x20 x21 x22 (Z_to_bv 64 67960) x24 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o3)) x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3
      ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3
      x1 x6 x8 x9 x11 x12 x13 x18 x19 x20 x21 x22 x24 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w15 w16 w17 w18 w19 PV MI OUT DTB FA AR SB SL S0 S1 SL32 DJS DKS HDC HI0 HJ0 HO0 HI1 HJ1 HO1 HI2 HJ2 HO2 HI3 HJ3 HO3 HD0 HD1 HD2 HD3.
    assert (KS : SRC + n <= SPV - 416 \/ SPV <= SRC) by (clear - DKS LO; lia).
    assert (KD : DST + dcap <= SPV - 416 \/ SPV <= DST) by (clear - OS1 LO; lia).
    assert (KT : DT + 16388 <= SPV - 416 \/ SPV <= DT) by (clear - DJ3 LO; lia).
    destruct PV as (SV & STK & MUP & WMP).
    kx_autoLx [0x1f048] 60%nat
      [KZImg 0x10000 0x14000; KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 256) 152]
      [(SPV - 416, 160); (SPV - 256, 152); (0x110e0, 8)].
    kx_mem. kx_strip_mod.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
        let HF := fresh "HF" in
        pose proof (x42_f3_0 m2 0 ((dcap + 3) / 4) SRC n src i0 o0 i1 o1 i2 o2 i3 o3) as HF;
        replace (DST + 0) with DST in HF by lia; eapply HF
    end.
    all: first [ exact (conj SV (conj STK (conj MUP WMP))) | exact KXMI | exact OUT | exact DTB | exact FA | exact AR | exact SB | exact SL
               | exact DJS | exact DKS | lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma x42_fo_b : forall mm SRC n src q i0 i1 i2 i3 o0 o1 o2 o3 R
      (ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3 : word)
      (x1 x6 x9 x11 x12 x14 x18 x19 x20 x21 x24 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : word),
    X41PF mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 2635249153387078803) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 SRC) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) ->
    ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw (Z_to_bv 64 SRC) oew ie0 ie1 ie2 ie3 ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 < dcap -> 0 <= i0 -> i0 + 8 <= n -> 0 <= o0 -> 0 <= i1 -> i1 + 8 <= n -> 0 <= o1 -> 0 <= i2 -> i2 + 8 <= n -> 0 <= o2 -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 ->
    0 <= q -> 3 * q <= dcap -> o0 <= q -> o1 <= 2 * q -> o2 <= 3 * q -> o3 <= dcap ->
    0 <= R -> 10 * R <= q - o0 -> 10 * R <= 2 * q - o1 -> 10 * R <= 3 * q - o2 -> 10 * R <= dcap - o3 -> 7 * R <= i0 ->
    (forall mm' I0 I1 I2 I3 F0' F1' F2' F3' (y1 y6 y9 y11 y12 y13 y14 y18 y19 y20 y21 y24 y29 y30 y31 : word),
        X41PF mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 2635249153387078803) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 SRC) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) ->
        ARGS mm' ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw (Z_to_bv 64 SRC) oew ie0 ie1 ie2 ie3 ->
        bytes_at psegs mm' SRC src ->
        0 <= I0 -> I0 + 8 <= n -> 0 <= I1 -> I1 + 8 <= n -> 0 <= I2 -> I2 + 8 <= n -> 0 <= I3 -> I3 + 8 <= n ->
        0 <= F0' <= q -> 0 <= F1' <= 2 * q -> 0 <= F2' <= 3 * q -> o3 + 5 <= F3' <= dcap ->
        evt psegs POST (ST 0x1e97c mm' y1 (Z_to_bv 64 (SRC + I0)) y6 (Z_to_bv 64 (DST + F2')) (Z_to_bv 64 (DT + 4)) y9 (Z_to_bv 64 (DT + 4)) y11 y12 y13 y14 (Z_to_bv 64 (SRC + I3)) (Z_to_bv 64 (SRC + I2)) (Z_to_bv 64 (SRC + I1)) y18 y19 y20 y21 (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 67960) y24 (Z_to_bv 64 (DST + F0')) (Z_to_bv 64 (DST + F1')) (Z_to_bv 64 (DST + F3')) (Z_to_bv 64 (DST + 3 * q)) y29 y30 y31)) ->
    evt psegs POST (ST 0x1ea34 mm x1 (Z_to_bv 64 (SRC + i0)) x6 (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DT + 4)) x9 (Z_to_bv 64 (DT + 4)) x11 x12 (Z_to_bv 64 R) x14 (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i1)) x18 x19 x20 x21 (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 67960) x24 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + 3 * q)) x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm SRC n src q i0 i1 i2 i3 o0 o1 o2 o3 R
      ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3
      x1 x6 x9 x11 x12 x14 x18 x19 x20 x21 x24 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 PV MI OUT DTB FA AR SB SL S0 S1 SL32 DJS DKS HDC HI0 HJ0 HO0 HI1 HJ1 HO1 HI2 HJ2 HO2 HI3 HJ3 HO3 HQ0 HQ3 HE0 HE1 HE2 HE3
      HR0 HRA HRB HRC HRD HR7 KO.
    kx_autoLx [0x1efe4; 0x1ea58] 40%nat
      [KZImg 0x10000 0x14000; KZRange R 0 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
       KZRange i0 0 (2^32); KZRange i1 0 (2^32); KZRange i2 0 (2^32); KZRange i3 0 (2^32);
       KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange SRC 4096 (2^47); KZRange SPV 4096 (2^47)]
      (@nil (Z * Z)).
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 126948) _ _ _ _) =>
             eapply (x42_f2 mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3);
             first [ exact PV | exact MI | exact OUT | exact DTB | exact FA | exact AR | exact SB | exact SL | exact DJS | exact DKS | lia ]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 125528) _ _ _ _) =>
             assert (HR1 : 1 <= R) by lia;
             try replace (DST + (5 * R + o3)) with (DST + (o3 + 5 * R)) by lia;
             eapply (x42_fi (Z.to_nat R) mm mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3 (o3 + 5 * R) q (2 * q) (3 * q) dcap)
         end.
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | _ => first [ apply munch_refl | apply wmono_refl | exact MI | exact OUT | exact DTB | exact SB | exact SL | exact DJS | lia ]
         end.
    (* [comment removed for export] *)
    all: intros mm' I0 I1 I2 I3 F0' F1' F2' F3'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
         intros MU' WM' MI' OUT' DTB' HI0' HI1' HI2' HI3' HN0' HN1' HN2' HN3' HF0' HF1' HF2' HF3'.
    all: pose proof (rw_cells_transport psegs _ mm mm' _ _ FA MU' WM') as FA';
         pose proof (rw_cells_transport psegs _ mm mm' _ _ AR MU' WM') as AR';
         pose proof (x41pf_transport mm mm' PV MU' WM') as PV';
         pose proof (bytes_at_transport psegs _ mm mm' SRC src SB MU') as SB'.
    all: cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FA', AR', SB'.
    all: specialize (FA' ltac:(clear - OS1 LO; lia)); specialize (AR' ltac:(clear - OS1 LO; lia)); specialize (SB' ltac:(clear - DJS SL; lia)).
    all: eapply (KO mm' I0 I1 I2 I3 F0' F1' F2' F3');
         first [ exact PV' | exact MI' | exact OUT' | exact DTB' | exact FA' | exact AR' | exact SB' | lia ].
  Qed.

  (* [comment removed for export] *)
  Ltac x42_kx_lia_fast := kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].
  #[local] Ltac kx_lia ::= lazymatch goal with |- context [edenot _ _] => fail "opaque" | _ => x42_kx_lia_fast end.

  Lemma x42_fo : forall (k : nat) mm SRC n src q i0 i1 i2 i3 o0 o1 o2 o3
      (ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3 : word)
      (x1 x6 x9 x11 x12 x13 x14 x18 x19 x20 x21 x24 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : word),
    X41PF mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 2635249153387078803) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 SRC) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) ->
    ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw (Z_to_bv 64 SRC) oew ie0 ie1 ie2 ie3 ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 < dcap -> 0 <= i0 -> i0 + 8 <= n -> 0 <= o0 -> 0 <= i1 -> i1 + 8 <= n -> 0 <= o1 -> 0 <= i2 -> i2 + 8 <= n -> 0 <= o2 -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 ->
    0 <= q -> 3 * q <= dcap -> o0 <= q -> o1 <= 2 * q -> o2 <= 3 * q -> o3 <= dcap -> dcap - o3 < Z.of_nat k ->
    evt psegs POST (ST 0x1e97c mm x1 (Z_to_bv 64 (SRC + i0)) x6 (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DT + 4)) x9 (Z_to_bv 64 (DT + 4)) x11 x12 x13 x14 (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i1)) x18 x19 x20 x21 (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 67960) x24 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + 3 * q)) x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mm SRC n src q i0 i1 i2 i3 o0 o1 o2 o3
      ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3
      x1 x6 x9 x11 x12 x13 x14 x18 x19 x20 x21 x24 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 PV MI OUT DTB FA AR SB SL S0 S1 SL32 DJS DKS HDC HI0 HJ0 HO0 HI1 HJ1 HO1 HI2 HJ2 HO2 HI3 HJ3 HO3 HQ0 HQ3 HE0 HE1 HE2 HE3 HK;
      [exfalso; lia|].
    kx_autoLx [0x1ea34] 60%nat
      [KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32); KZRange q 0 (2^32);
       KZRange i0 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange SRC 4096 (2^47); KZRange SPV 4096 (2^47)]
      [(SPV - 416, 160)].
    all: x42_mulhu_rb.
    all: clear KXK KXRD KXA.
    (* [comment removed for export] *)
    all: pose proof (x42_fo_eqs q dcap o0 o1 o2 o3 i0 n ltac:(clear - HO0 HE0; lia) ltac:(clear - HO1 HE1; lia) ltac:(clear - HO2 HE2; lia)
                       ltac:(clear - HO3 HE3; lia) HQ0 HQ3 ltac:(clear - R1; lia) HI0 HJ0 SL32) as (E0 & E1 & E2 & E3 & E7 & HQA & HQB & HQC & HQD & HQ7).
    all: rewrite ?E0, ?E1, ?E2, ?E3, ?E7 in *.
    all: clear E0 E1 E2 E3 E7.
    all: set (Q0 := (q - o0) / 10) in *; set (Q1 := (2 * q - o1) / 10) in *; set (Q2 := (3 * q - o2) / 10) in *;
         set (Q3 := (dcap - o3) / 10) in *; set (Q7 := i0 / 7) in *.
    all: clearbody Q0 Q1 Q2 Q3 Q7.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?R) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 125492) _ _ _ _) =>
             eapply (x42_fo_b mm SRC n src q i0 i1 i2 i3 o0 o1 o2 o3 R);
             first [ exact PV | exact MI | exact OUT | exact DTB | exact FA | exact AR | exact SB | exact SL | exact DJS | exact DKS
                   | lazymatch goal with |- forall _, _ => idtac end | lia ]
         end.
    all: intros mm' I0 I1 I2 I3 F0' F1' F2' F3'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
         intros PV' MI' OUT' DTB' FA' AR' SB' HI0' HN0' HI1' HN1' HI2' HN2' HI3' HN3' HF0' HF1' HF2' HF3'.
    all: eapply (IH mm' SRC n src q I0 I1 I2 I3 F0' F1' F2' F3');
         first [ exact PV' | exact MI' | exact OUT' | exact DTB' | exact FA' | exact AR' | exact SB' | exact SL | exact DJS | exact DKS | lia ].
  Qed.

End DX42_23.
