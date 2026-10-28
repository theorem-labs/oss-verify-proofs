(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx41f RZ_huf_dx42_5 RZ_huf_dx42_13 huf411_kit_rs huf421_kit huf421_kit_c1_entry.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_14.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  Hypothesis BITINIT : bit_init_stmt.
  Hypothesis SPVA : rsk_al SPV 16.
  Hypothesis DTA : rsk_al DT 4.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -912)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -912) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X42P := (RZ_huf_dx42_5.X42P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation EINVB := (RZ_huf_dx42_5.EINVB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation X42S := (RZ_huf_dx42_0.X42S ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).



  Lemma x42_c1ret : forall mm (y2 y10 : Z) (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EINVB mm -> y2 mod 2^64 = (SPV + -912) mod 2^64 -> zd_is_error (y10 mod 2^64) = true ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 y2) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 y10) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                            x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x29160) fc None mm (seg_rom usegs)).
  Proof using All.
    intros mm y2 y10 x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 EI HSP HE.
    rewrite (zbv_eqm _ _ HSP), (zbv_eqm y10 (y10 mod 2^64) ltac:(rewrite Z.mod_mod by lia; reflexivity)).
    pose proof (Z.mod_pos_bound y10 (2^64) ltac:(lia)) as HB.
    eapply RZ_huf_dx42_5.x42_ret; first [exact CTX | exact TL | exact RSV | exact X2OK | exact EI | right; split; [exact HE | lia]].
  Qed.

  Ltac x42p_close := unfold RZ_huf_dx42_5.X42P;
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
    first [eassumption | (do 12 eexists; eassumption) | (apply rsk_al_e; exact SPVA)].
  Ltac sbuf_close := unfold RZ_huf_dx41f.SBUF; repeat split; first [eassumption | lia].

  Lemma x42_c1 : forall mm rest S1 n1 b1 S2 n2 b2 S3 n3 b3 S4 n4 b4 e1 tot n dl j1 j2 j3 j4
      (y1 y2 y8 y9 y10 y11 y12 y18 y19 y20 y21 y22 y24 y25 y26 y27 : Z)
      (x5 x6 x7 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word),
    X42P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    w12 = Z_to_bv 64 (DST + e1) -> w13 = Z_to_bv 64 (DST + 2 * e1) -> w15 = Z_to_bv 64 (DST + dcap) -> w16 = Z_to_bv 64 (DT + 4) ->
    rw_cells usegs mm (SPV + -656) [CB 40 j1] -> rw_cells usegs mm (SPV + -696) [CB 40 j2] ->
    rw_cells usegs mm (SPV + -736) [CB 40 j3] -> rw_cells usegs mm (SPV + -776) [CB 40 j4] ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    S2 = S1 + n1 -> S3 = S2 + n2 -> S4 = S3 + n3 ->
    n4 = n - tot -> 0 <= tot <= n -> n < 2^32 -> 0 <= e1 -> 3 * e1 <= dcap -> dcap <= 4 * e1 -> dl = tl + 256 * rsv ->
    y1 mod 2^64 = 0x25efc mod 2^64 -> y2 mod 2^64 = (SPV + -912) mod 2^64 ->
    y8 mod 2^64 = DST mod 2^64 -> y9 mod 2^64 = S3 mod 2^64 -> y10 mod 2^64 = (SPV + -656) mod 2^64 ->
    y11 mod 2^64 = S1 mod 2^64 -> y12 mod 2^64 = n1 mod 2^64 -> y18 mod 2^64 = n3 mod 2^64 -> y19 mod 2^64 = S2 mod 2^64 ->
    y20 mod 2^64 = n2 mod 2^64 -> y21 mod 2^64 = tot mod 2^64 -> y22 mod 2^64 = n mod 2^64 ->
    y24 mod 2^64 = dl mod 2^64 -> y25 mod 2^64 = (DST + 2 * e1) mod 2^64 -> y26 mod 2^64 = dcap mod 2^64 ->
    y27 mod 2^64 = (DST + 3 * e1) mod 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 y1) (Z_to_bv 64 y2) gp tp x5 x6 x7 (Z_to_bv 64 y8) (Z_to_bv 64 y9) (Z_to_bv 64 y10) (Z_to_bv 64 y11)
                            (Z_to_bv 64 y12) x13 x14 x15 x16 x17 (Z_to_bv 64 y18) (Z_to_bv 64 y19) (Z_to_bv 64 y20) (Z_to_bv 64 y21)
                            (Z_to_bv 64 y22) x23 (Z_to_bv 64 y24) (Z_to_bv 64 y25) (Z_to_bv 64 y26) (Z_to_bv 64 y27) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x25a0c) fc None mm (seg_rom usegs)).
  Proof using All.
    intros mm rest S1 n1 b1 S2 n2 b2 S3 n3 b3 S4 n4 b4 e1 tot n dl j1 j2 j3 j4 y1 y2 y8 y9 y10 y11 y12 y18 y19 y20 y21 y22 y24 y25 y26 y27
      x5 x6 x7 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
      (SV & STK & (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & SA) & RS & MU & WM & AL) MI OUT DTB FA E12 E13 E15 E16
      B1 B2 B3 B4 SB1 SB2 SB3 SB4 ES2 ES3 ES4 HN4 HTOT HN HE1 HE3 HE4 HDL H1 H2 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H24 H25 H26 H27.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    assert (BD8 : (SPV + -656) mod 8 = 0) by (clear - AL; lia). clear AL.
    rewrite (zbv_eqm _ _ H1), (zbv_eqm _ _ H2), (zbv_eqm _ _ H8), (zbv_eqm _ _ H9), (zbv_eqm _ _ H10), (zbv_eqm _ _ H11), (zbv_eqm _ _ H12),
            (zbv_eqm _ _ H18), (zbv_eqm _ _ H19), (zbv_eqm _ _ H20), (zbv_eqm _ _ H21), (zbv_eqm _ _ H22), (zbv_eqm _ _ H24),
            (zbv_eqm _ _ H25), (zbv_eqm _ _ H26), (zbv_eqm _ _ H27).
    clear H1 H2 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H24 H25 H26 H27. subst w12 w13 w15 w16 S2 S3 S4 n4 dl.
    destruct SB1 as (BB1 & L1 & R10 & R11 & R12 & D11 & D12).
    destruct SB2 as (BB2 & L2 & R20 & R21 & R22 & D21 & D22).
    destruct SB3 as (BB3 & L3 & R30 & R31 & R32 & D31 & D32).
    destruct SB4 as (BB4 & L4 & R40 & R41 & R42 & D41 & D42).
    eapply evt_cut.
    { eapply (BITINIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm (SPV + -656) S1 n1 b1 j1);
        first [exact BD8 | eassumption | clear BD8; lia]. }
    unfold bit_init_post. clear BD8. post_call usegs mm.
    try rewrite (ret_pc_even 0x25efc) by lia.
    lazymatch goal with
    | H : (_ = n1 /\ _) \/ _ |- _ => destruct H as [(HR & HN1 & k1 & c1 & pad1 & HC1 & HC8 & BD1) | (HER & HRB & bs & BD1)]
    end.
    - lazymatch type of HR with ?r = n1 => subst r end. unfold bitd_cells in BD1.
      kx_autoLx [0x25f14; 0x29160] 12%nat [KZRange n1 1 (2^32); KZRange SPV 4096 (2^47)] (@nil (Z * Z)).
      all: try solve [exfalso; kx_lia].
      all: kx_mem.
      eapply RZ_huf_dx42_13.x42_i1 with (DT := DT) (dtb := dtb) (tl := tl) (rsv := rsv) (rest := rest) (e1 := e1) (n := n) (tot := tot)
        (S1 := S1) (n1 := n1) (b1 := b1) (k1 := k1) (c1 := c1) (pad1 := pad1) (S2 := S1 + n1) (n2 := n2) (b2 := b2)
        (S3 := S1 + n1 + n2) (n3 := n3) (b3 := b3) (S4 := S1 + n1 + n2 + n3) (n4 := n - tot) (b4 := b4) (dl := tl + 256 * rsv)
        (junk2 := j2) (junk3 := j3) (junk4 := j4).
      all: first [ exact CTX | exact TL | exact RSV | exact X2OK | exact DJ3 | exact NBOK | exact BITINIT | exact SPVA | exact DTA
                 | x42p_close | sbuf_close | exact BD1 | eassumption | reflexivity | (f_equal; lia) | lia ].
    - pose proof HER as HER'. unfold zd_is_error, ZE_maxCode in HER'. apply Z.ltb_lt in HER'.
      lazymatch type of HER with zd_is_error ?r = true =>
        kx_autoLx [0x25f14; 0x29160] 12%nat [KZRange r (2^64 - 119) (2^64 - 1); KZRange SPV 4096 (2^47)] (@nil (Z * Z)) end.
      all: try solve [exfalso; kx_lia].
      all: kx_mem.
      eapply x42_c1ret; [ eapply c1_einvb_chunks; first [exact CTX | eassumption | reflexivity] | first [reflexivity | lia] | ].
      rewrite Z.mod_small by (unfold zd_is_error, ZE_maxCode in HER; apply Z.ltb_lt in HER; lia). exact HER.
  Qed.

  Lemma x42_s0 : forall mm rest SRC n src (x1 x5 x6 x7 x8 x9 x10 x11 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    X42S mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    nth_error dtb 2 = Some (Z_to_bv 8 tl) -> nth_error dtb 3 = Some (Z_to_bv 8 rsv) ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 DT) x15 x16 x17 x18 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x22084) fc None mm (seg_rom usegs)).
  Proof using All.
    intros mm rest SRC n src x1 x5 x6 x7 x8 x9 x10 x11 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      (SV & RS & STK & MU & WM) MI OUT DTB DT2 DT3 SRCB SRCL R20 R21 R22 DJS DKS.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    destruct DTA as [DTA4].
    carve_frame 400%nat STK.
    assert (FRW : wr_at usegs mm (SPV + -912) 400) by kx_wr_at.
    destruct (c1_frame400 mm (SPV + -912) junk FR) as ((w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & FA)
      & (j4 & B4) & (j3 & B3) & (j2 & B2) & (j1 & B1) & (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & SA)).
    clear FR.
    replace (SPV + -912 + 136) with (SPV + -776) in B4 by lia. replace (SPV + -912 + 176) with (SPV + -736) in B3 by lia.
    replace (SPV + -912 + 216) with (SPV + -696) in B2 by lia. replace (SPV + -912 + 256) with (SPV + -656) in B1 by lia.
    replace (SPV + -912 + 296) with (SPV + -616) in SA by lia.
    pose proof (c1_dl_read dtb tl rsv DT2 DT3 TL RSV) as DLR.
    kx_autoLx [0x25d44] 10%nat [KZRange SPV 4096 (2^47)] (@nil (Z * Z)).
    all: kx_mem.
    kx_autoLx [0x25a0c; 0x29160] 150%nat
      [KZRange n 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47);
       KZAlign DT 4; KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV + -912) 400;
       KZDisj (SPV + -912) 400 DT 16388; KZDisj (SPV + -912) 400 SRC n]
      [(SRC, n); (DT, 16388)].
    all: ub_at 0x2965c.
    all: try (lazymatch goal with
              | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ev _ ?J) _ _ _ _ _ _ _) _ _ _ _ _ _) =>
                  kx_read_eq J RD;
                  rewrite (rdval_bytes_at usegs _ DT dtb 2 2 false DTB ltac:(lia) ltac:(change (Z.to_nat 2) with 2%nat; lia)), DLR in RD;
                  rewrite RD
              end).
    all: try kx_read_ranges.
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x29160) _ _ _ _) =>
             eapply x42_c1ret; [ eapply c1_einvb_chunks; first [exact CTX | eassumption | reflexivity] | first [reflexivity | (f_equal; lia) | lia] | vm_compute; reflexivity ]
         | _ => idtac
         end.
    all: kx_strip_mod.
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?N1) _ _ _ _ _ (Z_to_bv 64 ?N3) _ (Z_to_bv 64 ?N2) (Z_to_bv 64 ?TOT) _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        eapply (x42_c1 _ rest (SRC + 6) N1 (firstn (Z.to_nat N1) (skipn (Z.to_nat 6) src))
                  (SRC + 6 + N1) N2 (firstn (Z.to_nat N2) (skipn (Z.to_nat (6 + N1)) src))
                  (SRC + 6 + N1 + N2) N3 (firstn (Z.to_nat N3) (skipn (Z.to_nat (6 + N1 + N2)) src))
                  (SRC + 6 + N1 + N2 + N3) (n - TOT) (firstn (Z.to_nat (n - TOT)) (skipn (Z.to_nat TOT) src))
                  ((dcap + 3) / 4) TOT n (tl + 256 * rsv) j1 j2 j3 j4)
    end.
    all: first [ x42p_close | eassumption | (eapply (c1_sbuf_sub SPV DST dcap lo _ SRC n src); first [eassumption | lia])
               | reflexivity | (f_equal; lia) | lia ].
  Qed.

End DX42_14.
