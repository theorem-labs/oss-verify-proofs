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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_huf_dx42_0b huf41_kit_reload.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

  Ltac x3_uim := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2965c) _ _ _ _) => kx_trap_fast | _ => idtac end.

  Ltac x3_clean := repeat match goal with
                          | H : know_ok _ _ _ _ |- _ => clear H | H : reads_ok _ _ _ _ _ |- _ => clear H
                          | H : atoms_ok _ _ |- _ => clear H | H : log_flat _ _ |- _ => clear H
                          end.

  Ltac x3_call SPV :=
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x25ca0) _ _ _ _) =>
      lazymatch goal with
      | BD : rw_cells usegs ?m (SPV + -736) [C8 ?c; C4 (Z_to_bv 64 ?bc); CB 4 ?pad; C8 (Z_to_bv 64 ?P); C8 (Z_to_bv 64 ?S); C8 (Z_to_bv 64 (?S + 8))],
        SB : bytes_at usegs ?m ?S ?bs, SL : zlen ?bs = ?len, SPM : SPV mod 16 = 0 |- _ =>
          x3_clean;
          replace (Z_to_bv 64 A0) with (Z_to_bv 64 (SPV + -736)) by (f_equal; lia);
          eapply evt_cut;
          [ eapply (huf_reload_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (SPV + -736) S len bc P c pad bs);
            first [ exact BD | exact SB | exact SL | assumption
                  | lazymatch goal with |- _ mod 8 = 0 => clear - SPM; Z.div_mod_to_equations; lia end | lia ]
          | unfold huf_reload_post; post_call usegs m;
            match goal with H : rw_cells _ _ (SPV + -736) (bitd_cells _ _ _ _ _) |- _ => unfold bitd_cells in H end ]
      end
    end.

Section DX42_3A.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis NBOK : huf_nb_ok true dtb tl.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation WDF := [(DST, DST + dcap); (SPV - 912, SPV - 616)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -912)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -912) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation WD3 := [(DST, DST + dcap); (SPV - 736, SPV - 696)].
  Notation BD3 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -736) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).

  Notation x42_tbl := (RZ_huf_dx42_0.x42_tbl SPV DST dcap DT lo dtb CTX tl X2OK).
  Notation x42_tbl_nb := (RZ_huf_dx42_0b.x42_tbl_nb SPV DST dcap DT lo dtb CTX tl TL NBOK).

  (* [comment removed for export] *)
  Lemma x42_la3 : forall mb mm j e pe dl (c0 b0 p0 st lm : word) pad
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x26 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
    munch WD3 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD3 mm c0 b0 pad p0 st lm ->
    0 <= j <= e -> e <= dcap -> dl = tl + 256 * rsv ->
    (forall mm' (y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y24 y28 y29 y30 c' b' p' : word),
        munch WD3 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
        BD3 mm' c' b' pad p' st lm ->
        evt usegs POST (ST 0x287cc mm' y1 y5 (Z_to_bv 64 (DT + 4)) y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 (2^61)) y20 y21 y22 y23 y24
                          (Z_to_bv 64 dl) x26 (Z_to_bv 64 tl) y28 y29 y30 (Z_to_bv 64 (DST + pe)))) ->
    evt usegs POST (ST 0x28740 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (DST + j))
                      (Z_to_bv 64 (DST + e)) x22 x23 x24 (Z_to_bv 64 dl) x26 (Z_to_bv 64 tl) x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j e pe dl c0 b0 p0 st lm pad x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x26 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 MU WM MI OUT DTB FA BD HJ HE HDL K.
    destruct (Z_lt_le_dec j e) as [ROOM|FULL]; cycle 1.
    - kx_autoLx [0x287cc; 0x2965c] 10%nat [KZRange (j - e) 0 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange DST 4096 (2^47);
                                           KZRange SPV 4096 (2^47)] [(SPV - 912, 136); (SPV - 736, 40)].
      all: eapply K; eassumption.
    - subst dl.
      assert (TLC : tl = 1 \/ tl = 2 \/ tl = 3 \/ tl = 4 \/ tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12) by lia.
      repeat (destruct TLC as [TLC|TLC]); rewrite TLC in *;
        kx_autoLx [0x287cc; 0x2965c] 60%nat
          [KZRange (dcap - j) 1 (2^32); KZRange (e - j) 1 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange dcap 0 (2^32);
           KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange rsv 0 255; KZRange SPV 4096 (2^47); KZWr DST dcap; KZWr (SPV - 736) 40;
           KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 912) 296; KZDisj (SPV - 912) 296 DT 16388]
          [(DT, 16388); (SPV - 912, 136); (SPV - 736, 40)].
      all: kx_ev_ranges.
      all: x3_uim.
      all: kx_mem.
      all: eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_t3 : forall (k : nat) mb mm j e pe dl sh (c0 b0 p0 st lm : word) pad
      (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x26 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
    munch WD3 mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
    BD3 mm c0 b0 pad p0 st lm ->
    e - j <= Z.of_nat k -> 0 <= j -> j + 2 <= e -> e <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl ->
    (forall mm' (y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y24 y28 y29 y30 c' b' p' : word),
        munch WD3 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) ->
        BD3 mm' c' b' pad p' st lm ->
        evt usegs POST (ST 0x287cc mm' y1 y5 (Z_to_bv 64 (DT + 4)) y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 (2^61)) y20 y21 y22 y23 y24
                          (Z_to_bv 64 dl) x26 (Z_to_bv 64 tl) y28 y29 y30 (Z_to_bv 64 (DST + pe)))) ->
    evt usegs POST (ST 0x286e8 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 (Z_to_bv 64 (DST + e - 2)) (Z_to_bv 64 sh) x10 x11 x12 x13 x14 x15 x16 x17 x18
                      (Z_to_bv 64 (2^61)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DST + e)) (Z_to_bv 64 (-1 * DT + -5)) x23 x24 (Z_to_bv 64 dl) x26
                      (Z_to_bv 64 tl) x28 x29 x30 (Z_to_bv 64 (DST + pe))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j e pe dl sh c0 b0 p0 st lm pad x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x26 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 MU WM MI OUT DTB FA BD HK HJ0 HJ HE HDL HSH K; [exfalso; lia|].
    assert (TBL : tbl_in_log usegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x42_tbl; exact DTB).
    kx_autoLx [0x286e8; 0x28740; 0x2965c] 40%nat
      [KZRange (dcap - j) 2 (2^32); KZRange (e - j) 2 (2^32); KZRange j 0 (2^32); KZRange e 0 (2^32); KZRange dcap 0 (2^32);
       KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange sh 52 63; KZRange SPV 4096 (2^47); KZWr DST dcap; KZWr (SPV - 736) 40;
       KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 912) 296; KZDisj (SPV - 912) 296 DT 16388; KZTblLog DT sh 4 7 1 2]
      [(DT, 16388); (SPV - 912, 136); (SPV - 736, 40)].
    all: kx_ev_ranges.
    all: x3_uim.
    all: kx_mem; kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x286e8) _ _ ?m2 _) =>
             replace (Z_to_bv 64 P) with (Z_to_bv 64 (DST + (P - DST))) by (f_equal; lia);
             eapply (IH mb m2 (P - DST) e pe dl sh); first [eassumption | lia]
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?P) _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x28740) _ _ ?m2 _) =>
             replace (Z_to_bv 64 P) with (Z_to_bv 64 (DST + (P - DST))) by (f_equal; lia);
             eapply (x42_la3 mb m2 (P - DST) e pe dl); first [eassumption | lia]
         end.
  Qed.

End DX42_3A.
