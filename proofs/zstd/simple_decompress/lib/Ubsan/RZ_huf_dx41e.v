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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41d.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf411_kit_rs huf41_kit_reload huf41_kit_x41ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41E.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).


  Notation WD4 := [(DST, DST + dcap); (SPV - 224, SPV - 184)].
  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD4 mm c b pad p st lm := (BDAT mm (SPV + -224) c b pad p st lm).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).

  Notation SINV := RZ_huf_dx41.SINV.
  Notation K4E mb st lm pad dl x8 x9 x18 x22 x23 x24 x26 :=
    (forall mm' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y27 y28 y29 y30 y31 c' b' p' : word),
        munch WD4 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) ->
        BD4 mm' c' b' pad p' st lm ->
        evt usegs POST (ST 0x24fcc mm' y1 y5 y6 y7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) y21
                           x22 x23 x24 (Z_to_bv 64 (DT + 4)) x26 y27 y28 y29 y30 y31)).
  Notation x41_p4 := (x41_p4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3).
  Notation x41_l4 := (x41_l4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3).

  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  (* [comment removed for export] *)
  Lemma x41_e4 : forall mb mm j off S len bs dl tl rsv bc (c0 : word) pad
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x22 x23 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w9 w11 w12 w13 w14 w15 w16 : word),
    munch WD4 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 (DST + dcap)) w9 (Z_to_bv 64 (DST + dcap - 3)) w11 w12 w13 w14 w15 w16 ->
    BD4 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> rsk_al SPV 16 ->
    0 <= j <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^31 ->
    K4E mb (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) pad dl x8 x9 x18 x22 x23 x24 x26 ->
    evt usegs POST (ST 0x24e84 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 bc) x18 (Z_to_bv 64 dl)
                       (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + j)) x22 x23 x24 (Z_to_bv 64 (DT + 4)) x26 (Z_to_bv 64 (DST + dcap)) x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    pose proof huf_reload_proof as HRL. unfold huf_reload_stmt, huf_reload_stmt_at, bitd_cells in HRL.
    intros mb mm j off S len bs dl tl rsv bc c0 pad x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x22 x23 x24 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w9 w11 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK SPA HJ HDL HTL HRSV HS HB K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64]; [destruct HS as [-> | (O1 & O2 & B1)]; [|destruct (Z_lt_le_dec off 8) as [O8|O8]]|].
    all: lazymatch goal with
         | B64 : _ > 64 |- _ =>
             kx_autoLx [0x24f6c; 0x24fcc] 30%nat
               [KZRange bc 65 (2^31 - 1); KZRange SPV 4096 (2^47); KZRange j 0 (2^32); KZRange dcap 0 (2^32);
                KZRange DST 4096 (2^47); KZWr (SPV - 224) 40; KZDisj (SPV - 224) 40 (SPV - 512) 136]
               [(SPV - 512, 136); (SPV - 224, 40)]
         | O8 : _ < 8 |- _ =>
             kx_autoLx [0x24f6c; 0x24fcc] 120%nat
               [KZRange (len - off) 8 (2^32); KZRange off 1 7; KZRange bc 0 64; KZRange len 9 (2^32); KZRange S 4096 (2^47);
                KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange j 0 (2^32); KZRange dcap 0 (2^32);
                KZRange DST 4096 (2^47); KZWr (SPV - 224) 40; KZDisj (SPV - 224) 40 S len; KZDisj (SPV - 224) 40 (SPV - 512) 136]
               [(S, len); (SPV - 512, 136); (SPV - 224, 40)]
         | O8 : 8 <= _ |- _ =>
             kx_autoLx [0x24f6c; 0x24fcc; 0x25ca0] 40%nat
               [KZRange (len - off) 8 (2^32); KZRange off 8 (2^32); KZRange bc 0 64; KZRange len 9 (2^32); KZRange S 4096 (2^47);
                KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange j 0 (2^32); KZRange dcap 0 (2^32);
                KZRange DST 4096 (2^47)]
               [(S, len); (SPV - 512, 136); (SPV - 224, 40)]
         | _ => kx_autoLx [0x24f6c; 0x24fcc] 30%nat [KZRange bc 0 64; KZRange S 4096 (2^47); KZRange SPV 4096 (2^47); KZRange j 0 (2^32);
                                    KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)] [(SPV - 512, 136); (SPV - 224, 40)]
         end.
    all: x41_ck.
    all: lazymatch goal with |- evt _ _ _ => idtac | |- _ => try solve [lia] end.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x25ca0) _ _ _ _) =>
             eapply evt_cut;
             [ eapply HRL; [ exact MI | exact BD | (apply rsk_al_e in SPA; clear - SPA; Z.div_mod_to_equations; lia) | exact SB | exact SL
                           | lia | lia | lia | lia | lia | lia | lia | lia ]
             | post_call usegs mm ];
             unfold bitd_cells in *;
             kx_autoLx [0x24f6c; 0x24fcc] 20%nat
               [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47)]
               [(SPV - 512, 136); (SPV - 224, 40)]
         | _ => idtac
         end.
    all: kx_ev_ranges; kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24f6c) _ _ _ _) =>
             eapply (x41_p4 mb); try eassumption; try lia; intros; eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24fcc) _ _ _ _) => eapply K; eassumption
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_d4 : forall mb mm j off S len bs dl tl rsv bc (c0 : word) pad
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w9 w11 w12 w13 w14 w15 w16 : word),
    munch WD4 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 (DST + dcap)) w9 (Z_to_bv 64 (DST + dcap - 3)) w11 w12 w13 w14 w15 w16 ->
    BD4 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> rsk_al SPV 16 ->
    0 <= j <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^31 ->
    K4E mb (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) pad dl x8 x9 x18 x22 x23 x24 x26 ->
    evt usegs POST (ST 0x24c18 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl)
                       (Z_to_bv 64 (2^62)) (Z_to_bv 64 (DST + j)) x22 x23 x24 (Z_to_bv 64 (DT + 4)) x26 (Z_to_bv 64 (DST + dcap)) x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j off S len bs dl tl rsv bc c0 pad x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w9 w11 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK SPA HJ HDL HTL HRSV HS HB K.
    kx_autoLx [0x24e84; 0x24c4c; 0x24f6c; 0x24fcc] 40%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange bc 0 (2^31 - 1);
       KZRange dl 0 65535; KZRange SPV 4096 (2^47); KZWr (SPV - 224) 40; KZDisj (SPV - 224) 40 (SPV - 512) 136]
      [(SPV - 512, 136); (SPV - 224, 40)].
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24f6c) _ _ _ _) =>
             eapply (x41_p4 mb); try eassumption; try lia; intros; eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24fcc) _ _ _ _) => eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24e84) _ _ _ _) =>
             eapply (x41_e4 mb); try eassumption; try lia; intros; eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24c4c) _ _ _ _) =>
             subst dl; rewrite (neg_dl_sh tl rsv HTL);
             replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity);
             eapply (x41_l4 (Z.to_nat (dcap - j)) mb); try eassumption; try lia; try reflexivity;
             intros; eapply K; eassumption
         end.
  Qed.

End DX41E.
