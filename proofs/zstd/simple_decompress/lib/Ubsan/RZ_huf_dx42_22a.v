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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_fkit2 RZ_huf_dx41r RZ_huf_dx42_5 RZ_huf_dx42_20 RZ_huf_dx42_21d.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf411_kit_rs huf42_2_ftkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_22A.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis TL11 : tl = 11.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis DTA : rsk_al DT 4.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11;
                                     C8 w12; C8 w13; C8 w14; C8 w15]).
  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw ilo oew ie0 ie1 ie2 ie3 :=
    (rw_cells usegs mm (SPV + -384) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 bt0; C8 bt1; C8 bt2;
                                     C8 bt3; C8 dtw; C8 ilo; C8 oew; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).
  Notation LOC mm u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 :=
    (rw_cells usegs mm (SPV + -232) [C8 u0; C8 u1; C8 u2; C8 u3; C8 u4; C8 u5; C8 u6; C8 u7; C8 u8; C8 u9; C8 u10; C8 u11;
                                     C8 u12; C8 u13; C8 u14; C8 u15]).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation X41PF := (RZ_huf_dx41r.X41PF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41pf_transport := (RZ_huf_dx41r.x41pf_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation x41_einv_f := (RZ_huf_dx41r.x41_einv_f ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation x42_retf := (RZ_huf_dx42_5.x42_retf ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_p5 := (RZ_huf_dx42_21d.x42_p5 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK TL11 DTA).
  Notation x42_s5 := (RZ_huf_dx42_21d.x42_s5 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK TL11 DTA).
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] | solve [ft_al] ].

  Ltac ft_einv PVT :=
    match goal with FR : rw_cells _ ?m (SPV + -512) _, AR : rw_cells _ ?m (SPV + -384) _, LC : rw_cells _ ?m (SPV + -232) _ |- _ =>
      let FA := fresh "FA" in let SZ := fresh "SZ" in
      destruct (ft_frame408 usegs m SPV _ _ _ FR AR LC eq_refl eq_refl eq_refl) as [FA SZ];
      eapply (x41_einv_f m _ PVT); [eassumption | eassumption | exact FA | exact SZ]
    end.

  Ltac ft_pf :=
    lazymatch goal with |- _ ?m =>
      lazymatch goal with
      | SV : rw_cells usegs m (SPV + -104) _, STK : stk usegs m lo (SPV + -512), MUP : munch _ m0 m, WMP : wmono usegs m0 m |- _ =>
          exact (conj SV (conj STK (conj MUP WMP)))
      end
    end.

  Ltac ft_einv0 :=
    lazymatch goal with |- _ ?m =>
      lazymatch goal with
      | SV : rw_cells usegs m (SPV + -104) _, STK : stk usegs m lo (SPV + -512), MUP : munch _ m0 m, WMP : wmono usegs m0 m |- _ =>
          ft_einv (conj SV (conj STK (conj MUP WMP)))
      end
    end.

  Ltac f3_go PE ok ik SRC n src :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22098) _ _ ?m2 _) =>
        eapply (x42_retf m2); [ft_einv0 | first [left; reflexivity | right; split; reflexivity]]
    | |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
        ft_w22; kx_ev_ranges; ft_s18 (SRC + ik); ft_s8 (DST + PE); ft_s23 (DST + PE);
        lazymatch goal with
        | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?BC) _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x21b4c) _ _ _ _) =>
            ft_s26 (DST + PE - 9); eapply (x42_p5 (Z.to_nat dcap) m2 m2 ok PE ik SRC n src BC)
        | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?BC) _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x21d6c) _ _ _ _) =>
            ft_s26 (PE - ok); eapply (x42_s5 m2 m2 ok PE ik SRC n src BC)
        end
    end.

  Ltac f3_case R1 R2 R3 ep q ik ok ek bk SRC n src PE SB :=
    kx_autoLx [0x21b4c; 0x21d6c; 0x22098; 0x220dc; 0x2213c; 0x22180; 0x22188; 0x22190] 120%nat
      [R1; R2; R3; KZTbl HUF_CTZ_TBL2 64 1 0 0 63; KZImg 0x10000 0x14000;
       KZRange ep 0 (2^32); KZRange q 0 (2^32); KZRange dcap 1 (2^32); KZRange (dcap - ep) 0 (2^32);
       KZRange ik 0 (2^32); KZRange (n - ik) 8 (2^32); KZRange ok 0 (2^32); KZRange ek 0 (2^32); KZRange (bv_unsigned bk) 1 (2^64 - 1);
       KZRange n 8 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange DST 4096 (2^47);
       KZRange SPV 4096 (2^47); KZRange DT 4096 (2^47)]
      [(SRC, n); (SPV - 512, 128); (SPV - 384, 152); (0x11078, 64)];
    ft_ck;
    (lazymatch goal with |- sc_resid _ _ _ _ => kx_rd SB | _ => idtac end);
    kx_ev_ranges; kx_mem; kx_strip_mod;
    f3_go PE ok ik SRC n src.

  Ltac f3_side :=
    lazymatch goal with
    | |- forall _, _ => idtac
    | _ => first [ apply munch_refl | apply wmono_refl | eassumption | lia | (unfold SINV; lia) | exact (bv_unsigned_in_range 64 _) ]
    end.

  Ltac f3_tr MU' WM' :=
    lazymatch type of MU' with munch _ ?mb ?mm2 =>
      lazymatch goal with
      | SV : rw_cells usegs mb (SPV + -104) _, STK : stk usegs mb lo (SPV + -512), MUP : munch _ m0 mb, WMP : wmono usegs m0 mb |- _ =>
          let PV' := fresh "PV" in
          pose proof (x41pf_transport mb mm2 (conj SV (conj STK (conj MUP WMP))) MU' WM') as PV';
          clear SV STK MUP WMP; destruct PV' as (SV & STK & MUP & WMP)
      end;
      repeat match goal with
      | H : rw_cells usegs mb ?A ?cs |- _ =>
          let H' := fresh "T" in
          pose proof (rw_cells_transport usegs _ mb mm2 A cs H MU' WM') as H';
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H';
          specialize (H' ltac:(lia)); clear H
      | H : bytes_at usegs mb ?A ?bs |- _ =>
          let H' := fresh "T" in
          pose proof (bytes_at_transport usegs _ mb mm2 A bs H MU') as H';
          cbn [disjoint_from] in H'; specialize (H' ltac:(lia)); clear H
      end
    end.

  Ltac f3_kgoal STOPS NEXT :=
    intros mm' j' y1 y7 y17 y18 y19 y21 y22 y23 y25 y26 y27 MU' WM' MI' OUT' DTB' HJ';
    f3_tr MU' WM'; clear MU';
    lazymatch type of HJ' with ?ok <= _ <= ?pe =>
      destruct (Z_lt_le_dec j' pe) as [JL|JE];
      [ kx_autoLx STOPS 60%nat
          [KZRange (pe - j') 1 (2^32); KZRange j' 0 (2^32); KZRange ok 0 (2^32); KZRange (j' - ok) 0 (2^32); KZRange pe 0 (2^32);
           KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 384) 152]
          [(SPV - 512, 128); (SPV - 384, 152)]
      | kx_autoLx STOPS 60%nat
          [KZRange (pe - j') 0 0; KZRange j' 0 (2^32); KZRange ok 0 (2^32); KZRange (j' - ok) 0 (2^32); KZRange pe 0 (2^32);
           KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 384) 152]
          [(SPV - 512, 128); (SPV - 384, 152)] ];
      ft_ck; kx_ev_ranges; kx_mem; kx_strip_mod;
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22098) _ _ ?m3 _) =>
          eapply (x42_retf m3); [ft_einv0 | first [left; reflexivity | right; split; reflexivity]]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x21a48) _ _ ?m3 _) => NEXT m3 pe
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x25d44) _ _ _ _) => exfalso; first [solve [lia] | solve [kx_lia]]
      end
    end.

  Lemma x42_f3_3 : forall mm eprev q SRC n src i0 o0 e0 i1 o1 e1 i2 o2 e2 i3 o3 e3
      (b0 b1 b2 b3 dtw oew : word)
      (x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 : word)
      (w0 w1 w2 w3 w4 w5 w8 w9 w10 w11 w12 w13 w14 : word)
      (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 : word),
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRS mm w0 w1 w2 w3 w4 w5 (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + dcap)) w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 (DT + 4)) ->
    ARGS mm (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3))
            (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3))
            b0 b1 b2 b3 dtw (Z_to_bv 64 SRC) oew
            (Z_to_bv 64 (SRC + e0)) (Z_to_bv 64 (SRC + e1)) (Z_to_bv 64 (SRC + e2)) (Z_to_bv 64 (SRC + e3)) ->
    LOC mm u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 <= q < 2^32 -> 0 < dcap -> 0 <= eprev <= dcap ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= o0 <= dcap -> 0 <= e0 <= n -> 1 <= bv_unsigned b0 ->
    0 <= i1 -> i1 + 8 <= n -> 0 <= o1 <= dcap -> 0 <= e1 <= n -> 1 <= bv_unsigned b1 ->
    0 <= i2 -> i2 + 8 <= n -> 0 <= o2 <= dcap -> 0 <= e2 <= n -> 1 <= bv_unsigned b2 ->
    0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap -> 0 <= e3 <= n -> 1 <= bv_unsigned b3 ->
    evt usegs POST (ST 0x21a48 mm x1 (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 (DST + eprev)) x9 (Z_to_bv 64 3)
                      (Z_to_bv 64 (SPV + -264)) (Z_to_bv 64 0x11078) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (SPV + -384))
                      (Z_to_bv 64 9) (Z_to_bv 64 0x218a392cd3d5dbf) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                      (Z_to_bv 64 64) (Z_to_bv 64 q) (Z_to_bv 64 (DT + 4)) x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm eprev q SRC n src i0 o0 e0 i1 o1 e1 i2 o2 e2 i3 o3 e3 b0 b1 b2 b3 dtw oew
      x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 w0 w1 w2 w3 w4 w5 w8 w9 w10 w11 w12 w13 w14
      u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15
      PV MI OUT DTB FR AR LC SB SL S0 S1 SL32 DJS DKS HQ HDC HEP
      HI0 HN0 HO0 HE0 HB0 HI1 HN1 HO1 HE1 HB1 HI2 HN2 HO2 HE2 HB2 HI3 HN3 HO3 HE3 HB3.
    destruct PV as (SV & STK & MUP & WMP).
    pose proof (ft_frs15 usegs mm SPV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as FC.
    assert (TBLC : tbl_in usegs mm HUF_CTZ_TBL2 64 1 0 0 63) by exact (huf_ctz_tbl2 mm MI).
    destruct (Z_lt_le_dec (dcap - eprev) q) as [DC|DC];
      [ (destruct (Z_lt_le_dec dcap o3) as [E1|E1]; [|destruct (Z_lt_le_dec i3 (e3 - 8)) as [E2|E2];
           [|destruct (Z_lt_le_dec (dcap - o3) 8) as [E3|E3]]]);
        [ first [solve [exfalso; lia] | f3_case (KZRange (q - (dcap - eprev)) 1 (2^32)) (KZRange (o3 - dcap) 1 (2^32)) (KZRange q 0 (2^32))
                                                eprev q i3 o3 e3 b3 SRC n src dcap SB]
        | f3_case (KZRange (q - (dcap - eprev)) 1 (2^32)) (KZRange (dcap - o3) 0 (2^32)) (KZRange (e3 - 8 - i3) 1 (2^32))
                  eprev q i3 o3 e3 b3 SRC n src dcap SB
        | f3_case (KZRange (q - (dcap - eprev)) 1 (2^32)) (KZRange (dcap - o3) 0 7) (KZRange (i3 - (e3 - 8)) 0 (2^33))
                  eprev q i3 o3 e3 b3 SRC n src dcap SB
        | f3_case (KZRange (q - (dcap - eprev)) 1 (2^32)) (KZRange (dcap - o3) 8 (2^32)) (KZRange (i3 - (e3 - 8)) 0 (2^33))
                  eprev q i3 o3 e3 b3 SRC n src dcap SB ]
      | (destruct (Z_lt_le_dec (eprev + q) o3) as [E1|E1]; [|destruct (Z_lt_le_dec i3 (e3 - 8)) as [E2|E2];
           [|destruct (Z_lt_le_dec (eprev + q - o3) 8) as [E3|E3]]]);
        [ f3_case (KZRange (dcap - eprev - q) 0 (2^32)) (KZRange (o3 - (eprev + q)) 1 (2^32)) (KZRange q 0 (2^32))
                  eprev q i3 o3 e3 b3 SRC n src (eprev + q) SB
        | f3_case (KZRange (dcap - eprev - q) 0 (2^32)) (KZRange (eprev + q - o3) 0 (2^32)) (KZRange (e3 - 8 - i3) 1 (2^32))
                  eprev q i3 o3 e3 b3 SRC n src (eprev + q) SB
        | f3_case (KZRange (dcap - eprev - q) 0 (2^32)) (KZRange (eprev + q - o3) 0 7) (KZRange (i3 - (e3 - 8)) 0 (2^33))
                  eprev q i3 o3 e3 b3 SRC n src (eprev + q) SB
        | f3_case (KZRange (dcap - eprev - q) 0 (2^32)) (KZRange (eprev + q - o3) 8 (2^32)) (KZRange (i3 - (e3 - 8)) 0 (2^33))
                  eprev q i3 o3 e3 b3 SRC n src (eprev + q) SB ] ].
    all: f3_side.
    (* [comment removed for export] *)
    all: f3_kgoal [0x22098; 0x220dc; 0x2213c; 0x22180; 0x22188; 0x22190] ltac:(fun m3 pe => fail).
  Qed.

  Ltac f3_next3 m3 pe q SRC n src i0 o0 e0 i1 o1 e1 i2 e2 i3 o3 e3 :=
    match goal with AR : rw_cells usegs m3 (SPV + -384) [_; _; _; _; _; _; C8 (Z_to_bv 64 ?V); _; _; _; _; _; _; _; _; _; _; _; _] |- _ =>
      replace V with (DST + pe) in AR by lia end;
    ft_s8 (DST + pe);
    eapply (x42_f3_3 m3 pe q SRC n src i0 o0 e0 i1 o1 e1 i2 pe e2 i3 o3 e3);
    first [ft_pf | eassumption | lia].


  Lemma x42_f3_2 : forall mm eprev q SRC n src i0 o0 e0 i1 o1 e1 i2 o2 e2 i3 o3 e3
      (b0 b1 b2 b3 dtw oew : word)
      (x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 : word)
      (w0 w1 w2 w3 w4 w5 w8 w9 w10 w11 w12 w13 w14 : word)
      (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 : word),
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRS mm w0 w1 w2 w3 w4 w5 (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + dcap)) w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 (DT + 4)) ->
    ARGS mm (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3))
            (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3))
            b0 b1 b2 b3 dtw (Z_to_bv 64 SRC) oew
            (Z_to_bv 64 (SRC + e0)) (Z_to_bv 64 (SRC + e1)) (Z_to_bv 64 (SRC + e2)) (Z_to_bv 64 (SRC + e3)) ->
    LOC mm u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 <= q < 2^32 -> 0 < dcap -> 0 <= eprev <= dcap ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= o0 <= dcap -> 0 <= e0 <= n -> 1 <= bv_unsigned b0 ->
    0 <= i1 -> i1 + 8 <= n -> 0 <= o1 <= dcap -> 0 <= e1 <= n -> 1 <= bv_unsigned b1 ->
    0 <= i2 -> i2 + 8 <= n -> 0 <= o2 <= dcap -> 0 <= e2 <= n -> 1 <= bv_unsigned b2 ->
    0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap -> 0 <= e3 <= n -> 1 <= bv_unsigned b3 ->
    evt usegs POST (ST 0x21a48 mm x1 (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 (DST + eprev)) x9 (Z_to_bv 64 2)
                      (Z_to_bv 64 (SPV + -264)) (Z_to_bv 64 0x11078) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (SPV + -384))
                      (Z_to_bv 64 9) (Z_to_bv 64 0x218a392cd3d5dbf) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                      (Z_to_bv 64 64) (Z_to_bv 64 q) (Z_to_bv 64 (DT + 4)) x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm eprev q SRC n src i0 o0 e0 i1 o1 e1 i2 o2 e2 i3 o3 e3 b0 b1 b2 b3 dtw oew
      x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 w0 w1 w2 w3 w4 w5 w8 w9 w10 w11 w12 w13 w14
      u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15
      PV MI OUT DTB FR AR LC SB SL S0 S1 SL32 DJS DKS HQ HDC HEP
      HI0 HN0 HO0 HE0 HB0 HI1 HN1 HO1 HE1 HB1 HI2 HN2 HO2 HE2 HB2 HI3 HN3 HO3 HE3 HB3.
    destruct PV as (SV & STK & MUP & WMP).
    pose proof (ft_frs15 usegs mm SPV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as FC.
    assert (TBLC : tbl_in usegs mm HUF_CTZ_TBL2 64 1 0 0 63) by exact (huf_ctz_tbl2 mm MI).
    destruct (Z_lt_le_dec (dcap - eprev) q) as [DC|DC];
      [ (destruct (Z_lt_le_dec dcap o2) as [E1|E1]; [|destruct (Z_lt_le_dec i2 (e2 - 8)) as [E2|E2];
           [|destruct (Z_lt_le_dec (dcap - o2) 8) as [E3|E3]]]);
        [ first [solve [exfalso; lia] | f3_case (KZRange (q - (dcap - eprev)) 1 (2^32)) (KZRange (o2 - dcap) 1 (2^32)) (KZRange q 0 (2^32))
                                                eprev q i2 o2 e2 b2 SRC n src dcap SB]
        | f3_case (KZRange (q - (dcap - eprev)) 1 (2^32)) (KZRange (dcap - o2) 0 (2^32)) (KZRange (e2 - 8 - i2) 1 (2^32))
                  eprev q i2 o2 e2 b2 SRC n src dcap SB
        | f3_case (KZRange (q - (dcap - eprev)) 1 (2^32)) (KZRange (dcap - o2) 0 7) (KZRange (i2 - (e2 - 8)) 0 (2^33))
                  eprev q i2 o2 e2 b2 SRC n src dcap SB
        | f3_case (KZRange (q - (dcap - eprev)) 1 (2^32)) (KZRange (dcap - o2) 8 (2^32)) (KZRange (i2 - (e2 - 8)) 0 (2^33))
                  eprev q i2 o2 e2 b2 SRC n src dcap SB ]
      | (destruct (Z_lt_le_dec (eprev + q) o2) as [E1|E1]; [|destruct (Z_lt_le_dec i2 (e2 - 8)) as [E2|E2];
           [|destruct (Z_lt_le_dec (eprev + q - o2) 8) as [E3|E3]]]);
        [ f3_case (KZRange (dcap - eprev - q) 0 (2^32)) (KZRange (o2 - (eprev + q)) 1 (2^32)) (KZRange q 0 (2^32))
                  eprev q i2 o2 e2 b2 SRC n src (eprev + q) SB
        | f3_case (KZRange (dcap - eprev - q) 0 (2^32)) (KZRange (eprev + q - o2) 0 (2^32)) (KZRange (e2 - 8 - i2) 1 (2^32))
                  eprev q i2 o2 e2 b2 SRC n src (eprev + q) SB
        | f3_case (KZRange (dcap - eprev - q) 0 (2^32)) (KZRange (eprev + q - o2) 0 7) (KZRange (i2 - (e2 - 8)) 0 (2^33))
                  eprev q i2 o2 e2 b2 SRC n src (eprev + q) SB
        | f3_case (KZRange (dcap - eprev - q) 0 (2^32)) (KZRange (eprev + q - o2) 8 (2^32)) (KZRange (i2 - (e2 - 8)) 0 (2^33))
                  eprev q i2 o2 e2 b2 SRC n src (eprev + q) SB ] ].
    all: f3_side.
    (* [comment removed for export] *)
    all: f3_kgoal [0x21a48; 0x22098; 0x220dc; 0x2213c; 0x22180; 0x22188; 0x22190]
           ltac:(fun m3 pe => f3_next3 m3 pe q SRC n src i0 o0 e0 i1 o1 e1 i2 e2 i3 o3 e3).
  Qed.


End DX42_22A.
