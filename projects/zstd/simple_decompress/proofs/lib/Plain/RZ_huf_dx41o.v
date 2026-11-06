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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx41h RZ_huf_dx41i RZ_huf_dx41j RZ_huf_dx41k RZ_huf_dx41l RZ_huf_dx41m RZ_huf_dx41n.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41O.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis BITINIT : bit_init_stmt.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 :=
    (rw_cells psegs mm (SPV + -416) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19]).


  Notation WD4 := [(DST, DST + dcap); (SPV - 256, SPV - 216)].
  Notation WDF := [(DST, DST + dcap); (SPV - 416, SPV - 216)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells psegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SINV := RZ_huf_dx41.SINV.

  Notation WFR := [(SPV - 416, SPV - 216)].
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation HINV := RZ_huf_dx41g.HINV.

  (* [comment removed for export] *)
  Lemma sbuf_sub : forall mm SRC n src A k len,
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 <= k -> 0 <= len -> k + len <= n -> A = SRC + k ->
    SBUF mm A len (firstn (Z.to_nat len) (skipn (Z.to_nat k) src)).
  Proof.
    intros mm SRC n src A k len HB HL R0 R1' R2 D1 D2 HK HLEN HKL ->.
    assert (LEN : zlen (firstn (Z.to_nat len) (skipn (Z.to_nat k) src)) = len) by (rewrite firstn_length, skipn_length; lia).
    split; [|split; [exact LEN|]; repeat split; lia].
    rewrite <- (firstn_skipn (Z.to_nat k) src) in HB. apply bytes_at_app in HB as [_ HB].
    rewrite firstn_length, Nat.min_l in HB by lia. rewrite Z2Nat.id in HB by lia.
    rewrite <- (firstn_skipn (Z.to_nat len) (skipn (Z.to_nat k) src)) in HB. apply bytes_at_app in HB as [HB _]. exact HB.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_dl_read : forall tl rsv, nth_error dtb 2 = Some (Z_to_bv 8 tl) -> nth_error dtb 3 = Some (Z_to_bv 8 rsv) ->
    1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    extz false 2 (bytes_le_to_Z (firstn 2 (skipn (Z.to_nat 2) dtb))) = tl + 256 * rsv.
  Proof.
    intros tl rsv DT2 DT3 HTL HRSV.
    assert (E : firstn 2 (skipn (Z.to_nat 2) dtb) = [Z_to_bv 8 tl; Z_to_bv 8 rsv]).
    { change (Z.to_nat 2) with 2%nat.
      destruct dtb as [|y0 [|y1 [|y2 [|y3 r]]]]; cbn in DT2, DT3; try discriminate.
      injection DT2 as ->. injection DT3 as ->. reflexivity. }
    rewrite E. unfold extz. rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val].
    rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia). lia.
  Qed.

  Lemma x41_s0 : forall mm rest SRC n src tl rsv junk
      (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    X41P mm rest -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb -> huf_nb_ok false dtb tl ->
    nth_error dtb 2 = Some (Z_to_bv 8 tl) -> nth_error dtb 3 = Some (Z_to_bv 8 rsv) -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    rw_cells psegs mm (SPV + -256) [CB 40 junk] ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    evt psegs POST (ST 0x226c0 mm (Z_to_bv 64 n) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 SRC) x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) x29 x30 (Z_to_bv 64 DT)).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest SRC n src tl rsv junk
      x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 PV MI OUT DTB NBOK DT2 DT3 HTL HRSV FA BD SRCB SRCL R20 R21 R22 DJS DKS.
    assert (MU : munch WDF mm mm) by apply munch_refl.
    assert (WM : wmono psegs mm mm) by apply wmono_refl.
    kx_autoLx [0x23454; 0x22748] 80%nat
      [KZRange n 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange SRC 4096 (2^47);
       KZRange (SRC + n) 4096 (2^47)]
      [(SRC, n); (DT, 16388)].
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144468) _ _ ?mm' _) =>
             eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm');
             [ eapply RZ_huf_dx41k.x41_einv_gen with (rest := rest);
               first [ exact CTX | exact DJ3 | exact MI | exact OUT | exact FA | exact BD | reflexivity | exact PV ]
             | right; split; reflexivity ]
         | _ => idtac
         end.
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ev _ ?J) _) _ _ _ _ _ _) =>
        kx_read_eq J RD;
        rewrite (rdval_bytes_at psegs _ DT dtb 2 2 false DTB ltac:(lia) ltac:(change (Z.to_nat 2) with 2%nat; lia)),
                (x41_dl_read tl rsv DT2 DT3 HTL HRSV) in RD;
        rewrite RD
    end.
    kx_read_ranges. kx_strip_mod.
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?L2) (Z_to_bv 64 ?TOT) (Z_to_bv 64 ?L3) (Z_to_bv 64 ?L1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        replace (SRC + L1 + 6) with (SRC + 6 + L1) by lia;
        replace (dcap + DST) with (DST + dcap) by lia;
        replace (Z_to_bv 64 SRC) with (Z_to_bv 64 (SRC + 6 - 6)) by (f_equal; lia);
        eapply (x41_i1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 BITINIT mm rest ((dcap + 3) / 4) n TOT (SRC + 6)
                  L1 (firstn (Z.to_nat L1) (skipn (Z.to_nat 6) src))
                  L2 (firstn (Z.to_nat L2) (skipn (Z.to_nat (6 + L1)) src))
                  L3 (firstn (Z.to_nat L3) (skipn (Z.to_nat (6 + L1 + L2)) src))
                  (n - TOT) (firstn (Z.to_nat (n - TOT)) (skipn (Z.to_nat TOT) src)) (tl + 256 * rsv) tl rsv junk)
    end.
    all: first [ exact PV | exact MI | exact OUT | exact DTB | exact NBOK | exact FA | exact BD | exact HTL | exact HRSV | reflexivity | lia
               | eapply (sbuf_sub mm SRC n src); first [eassumption | lia] ].
  Qed.

End DX41O.
