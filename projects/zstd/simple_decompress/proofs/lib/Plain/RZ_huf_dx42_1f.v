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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_1a RZ_huf_dx42_1b RZ_huf_dx42_1c RZ_huf_dx42_1d RZ_huf_dx42_1e.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_1F.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.

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

  Notation x42_tbl := (RZ_huf_dx42_0.x42_tbl SPV DST dcap DT lo dtb CTX tl X2OK).
  Notation x42_la1 := (RZ_huf_dx42_1a.x42_la1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_t1 := (RZ_huf_dx42_1a.x42_t1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_w1 := (RZ_huf_dx42_1b.x42_w1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_c1 := (RZ_huf_dx42_1c.x42_c1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_p1 := (RZ_huf_dx42_1d.x42_p1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_q1 := (RZ_huf_dx42_1e.x42_q1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).

  (* [comment removed for export] *)
  Lemma x42_s1 : forall mb mm j pe off S len bs dl bc A0
      (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w8 w9 w10 w12 w13 w15 w16 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 (Z_to_bv 64 dl) (Z_to_bv 64 S) w8 w9 w10 (Z_to_bv 64 (DT + 4)) w12 w13 (Z_to_bv 64 (S + 8)) w15 w16 w17 w18 w19 ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^31 -> (bc <= 64 -> SINV off len bc) ->
    (forall mm' D7 (y1 y6 y7 y8 y9 y10 y11 y13 y16 y17 y28 y29 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 (Z_to_bv 64 dl) (Z_to_bv 64 S) w8 w9 w10 (Z_to_bv 64 (DT + 4)) w12 w13 (Z_to_bv 64 (S + 8)) w15 w16 w17 w18 w19 -> D7 = dl ->
        evt psegs POST (ST 0x208d0 mm' y1 x5 y6 y7 y8 y9 y10 y11 x12 y13 x14 x15 y16 y17 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + pe)) x20 (Z_to_bv 64 dl) x22 (Z_to_bv 64 D7) x24 x25 x27 w13 y28 y29 w12 w19)) ->
    evt psegs POST (ST 0x20468 mm (Z_to_bv 64 bc) x5 x6 x7 (Z_to_bv 64 (DST + j)) x9 (Z_to_bv 64 A0) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + pe)) x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (S + off)) x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe off S len bs dl bc A0 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w8 w9 w10 w12 w13 w15 w16 w17 w18 w19 MU WM MI OUT DTB FA SB SL S0 S1 SL32 DJS HJ HPE HDL HB HS K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64];
      [destruct (HS B64) as [-> | (O1 & O2 & B1)]; [|destruct (Z_lt_le_dec off 8) as [O8|O8]]|].
    all: lazymatch goal with
         | O8 : 8 <= _ |- _ =>
             kx_autoLx [0x206fc] 60%nat
               [KZRange (len - off) 8 (2^32); KZRange off 8 (2^32); KZRange bc 0 64; KZRange len 9 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32);
                KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47)]
               [(S, len); (SPV - 416, 160)]
         | O8 : _ < 8 |- _ =>
             kx_autoLx [0x206fc] 60%nat
               [KZRange (len - off) 8 (2^32); KZRange off 1 7; KZRange bc 0 64; KZRange len 9 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32);
                KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47)]
               [(S, len); (SPV - 416, 160)]
         | B64 : _ <= 64 |- _ =>
             kx_autoLx [0x206fc] 60%nat
               [KZRange bc 0 64; KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
                KZRange S 4096 (2^47); KZRange SPV 4096 (2^47)] [(SPV - 416, 160)]
         | _ =>
             kx_autoLx [0x206fc] 60%nat
               [KZRange bc 65 (2^31 - 1); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
                KZRange S 4096 (2^47); KZRange SPV 4096 (2^47)] [(SPV - 416, 160)]
         end.
    all: kx_ev_ranges; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m2' _) => set (m2 := m2') end.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR (Z_to_bv 64 ?BC) _ _ _ _ _ _ (Z_to_bv 64 (DST + ?J)) _ (Z_to_bv 64 ?A) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 132860) _ _ _ _) =>
             eapply (x42_c1 mb m2 J pe S len bs dl BC A); try eassumption; try lia;
             lazymatch goal with
             | |- _ <= 64 -> _ => intro B; first [exfalso; lia | exists (A - S); split; [lia | unfold RZ_huf_dx41.SINV; lia]]
             | |- _ => intros mm' D7; intros; eapply (K mm' D7); try eassumption; first [reflexivity | lia]
             end
         end.
  Qed.

  Notation WDG := [(DST, DST + dcap); (SPV - 416, SPV - 256)].
  Ltac x42_d1_k K mb :=
    intros mm' D7; intros;
    lazymatch goal with
    | MU2 : munch _ mb ?m2, WM2 : wmono _ mb ?m2, MU' : munch _ ?m2 mm', WM' : wmono _ ?m2 mm' |- _ =>
        eapply (K mm' D7);
        [ eapply munch_trans; [exact MU2|]; eapply munch_weaken; [|exact MU']; unfold sub_fp; cbn [outside]; intros; lia
        | exact (wmono_trans psegs mb m2 mm' WM2 WM') | eassumption | eassumption | eassumption | eassumption | first [reflexivity | lia] ]
    end.

  (* [comment removed for export] *)
  Lemma x42_d1 : forall mb mm j pe off S len bs dl bc
      (x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w8 w9 w10 w12 w13 w15 w16 w17 w18 w19 : word),
    munch WDG mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 (Z_to_bv 64 dl) (Z_to_bv 64 S) w8 w9 w10 (Z_to_bv 64 (DT + 4)) w12 w13 (Z_to_bv 64 (S + 8)) w15 w16 w17 w18 w19 ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (DT + 16388 <= lo \/ SPV <= DT) -> (S + len <= lo \/ SPV <= S) ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^31 -> (bc <= 64 -> SINV off len bc) ->
    (forall mm' D7 (y1 y6 y7 y8 y9 y10 y11 y13 y16 y17 y28 y29 : word) (v8 : word),
        munch WDG mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 (Z_to_bv 64 dl) (Z_to_bv 64 S) v8 w9 w10 (Z_to_bv 64 (DT + 4)) w12 w13 (Z_to_bv 64 (S + 8)) w15 w16 w17 w18 w19 -> D7 = dl ->
        evt psegs POST (ST 0x208d0 mm' y1 x5 y6 y7 y8 y9 y10 y11 x12 y13 x14 x15 y16 y17 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + pe)) x20 (Z_to_bv 64 dl) x18 (Z_to_bv 64 D7) x24 x25 x27 w13 y28 y29 w12 w19)) ->
    evt psegs POST (ST 0x20238 mm (Z_to_bv 64 bc) x5 x6 x7 x8 (Z_to_bv 64 (DST + j)) x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (DST + pe)) x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (S + off)) x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe off S len bs dl bc x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w8 w9 w10 w12 w13 w15 w16 w17 w18 w19 MU WM MI OUT DTB FA SB SL S0 S1 SL32 DJS DJ3 DJF HJ HPE HDL HB HS K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64].
    all: lazymatch goal with
         | B64 : _ <= 64 |- _ =>
             kx_autoLx [0x20468; 0x20284; 0x2050c; 0x206fc] 40%nat
               [KZRange bc 0 64; KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
                KZRange dl 0 65535; KZRange SPV 4096 (2^47); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange DT 4096 (2^47);
                KZWr (SPV - 416) 160; KZDisj (SPV - 416) 160 DST dcap; KZDisj (SPV - 416) 160 DT 16388; KZDisj (SPV - 416) 160 S len]
               [(SPV - 416, 160)]
         | _ =>
             kx_autoLx [0x20468; 0x20284; 0x2050c; 0x206fc] 40%nat
               [KZRange bc 65 (2^31 - 1); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
                KZRange dl 0 65535; KZRange SPV 4096 (2^47); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange DT 4096 (2^47);
                KZWr (SPV - 416) 160; KZDisj (SPV - 416) 160 DST dcap; KZDisj (SPV - 416) 160 DT 16388; KZDisj (SPV - 416) 160 S len]
               [(SPV - 416, 160)]
         end.
    all: kx_mem.
    all: subst dl; rewrite ?(neg_dl_sh tl rsv TL).
    all: try replace (DST + pe + -9) with (DST + pe - 9) by lia; try replace (DST + pe + -7) with (DST + pe - 7) by lia.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m2' _) => set (m2 := m2') in * end.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 131716) _ _ _ _) =>
             eapply (x42_p1 (Z.to_nat dcap) m2 m2 j pe off S len bs (tl + 256 * rsv) (64 - tl) bc A);
             try apply munch_refl; try apply wmono_refl; try eassumption; try lia; try reflexivity; try solve [apply HS; lia];
             x42_d1_k K mb
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 132364) _ _ _ _) =>
             eapply (x42_q1 (Z.to_nat dcap) m2 m2 j pe off S len bs (tl + 256 * rsv) (64 - tl) bc A);
             try apply munch_refl; try apply wmono_refl; try eassumption; try lia; try reflexivity; try solve [apply HS; lia];
             x42_d1_k K mb
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 132200) _ _ _ _) =>
             eapply (x42_s1 m2 m2 j pe off S len bs (tl + 256 * rsv) bc A);
             try apply munch_refl; try apply wmono_refl; try eassumption; try lia; try reflexivity;
             x42_d1_k K mb
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 132860) _ _ _ _) =>
             eapply (x42_c1 m2 m2 j pe S len bs (tl + 256 * rsv) bc A);
             try apply munch_refl; try apply wmono_refl; try eassumption; try lia; try reflexivity;
             lazymatch goal with
             | |- _ <= 64 -> _ => intro B; exfalso; lia
             | |- _ => x42_d1_k K mb
             end
         end.
  Qed.

End DX42_1F.
