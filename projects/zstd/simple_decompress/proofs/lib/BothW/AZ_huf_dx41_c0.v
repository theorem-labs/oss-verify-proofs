(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx1e AZ_huf_dx41 AZ_huf_dx41_4a AZ_huf_dx41_4b AZ_huf_dx41_4c AZ_huf_dx41_4d AZ_huf_dx41_4e AZ_huf_dx41_1e AZ_huf_dx41_2e AZ_huf_dx41_3e.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.
#[local] Ltac kx_path_hyp E zs nz KXA BR ::= kx_rr_dedup; kx_path_hyp_fast E zs nz KXA BR.
#[local] Ltac kx_sx3 ::= kx_rr_dedup; repeat kx_sx3_1.     (* [comment removed for export] *)
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
#[local] Ltac kxl_rd_exact ::=
  lazymatch goal with
  | |- rd_at ?segs ?m ?A ?N =>
      match goal with
      | H : rw_cells segs m A _ |- _ => apply (kxl_rd_rw segs m A _ N H); reflexivity
      | H : ro_cells segs m A _ |- _ => apply (kxl_rd_ro segs m A _ N H); reflexivity
      | H : bytes_at segs m A ?bs, L : Z.of_nat (length ?bs) = N |- _ => rewrite <- L; exact (rd_at_bytes_at segs m A bs H)
      end
  end.
(* [comment removed for export] *)
#[local] Ltac kxl_lia ::= first [kxl_hyp | solve [kxl_lia_small] | kx_lia].
(* [comment removed for export] *)
#[local] Ltac kx_wr_at ::=
  lazymatch goal with
  | |- wr_at ?segs ?m ?A ?N =>
      first [ match goal with
              | H : wr_at segs m A ?N0 |- _ => apply (wr_at_sub segs m A N0 A N H); kx_lia
              | H : rw_cells segs m A ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (wr_at_sub segs m A n A N (proj2 H)); kx_lia
              | H : stk segs m A ?hi |- _ => apply (wr_at_sub segs m A (hi - A) A N); [apply (wr_at_stk segs m A hi H); kx_lia | kx_lia | kx_lia]
              end
            | match goal with
              | H : wr_at segs m ?A0 ?N0 |- _ => apply (wr_at_sub segs m A0 N0 A N H); kx_lia
              | H : u8arr segs m ?A0 ?bs |- _ => apply (wr_at_sub segs m A0 (Z.of_nat (length bs)) A N (proj2 H)); kx_lia
              | H : rw_cells segs m ?A0 ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (wr_at_sub segs m A0 n A N (proj2 H)); kx_lia
              | H : stk segs m ?lo ?hi |- _ => apply (wr_at_sub segs m lo (hi - lo) A N); [apply (wr_at_stk segs m lo hi H); kx_lia | kx_lia | kx_lia]
              end ]
  end.
Section CANSEC1. Context {rc : runConstT}.
Section DX41AC0.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x41a_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x41a_actx RNG m0 SPV DST dcap SRC n DT lo.
  Hypothesis HRL : huf_reload_int_stmtA.
  Hypothesis DHI : dst_hi dcap DST.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2720 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -480)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 :=
    (rw_cells bsegs mm (SPV + -480) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12]).
  Notation BD1 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -376) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD2 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -144) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD3 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -184) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD4 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -224) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation W0 := [(DST, DST + dcap); (SPV - 2720, SPV)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation Q62 := (Z_to_bv 64 4611686018427387904).
  Notation OEND := (Z_to_bv 64 (DST + dcap)).
  Notation EINVA := (AZ_huf_dx41.EINVA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41_end := (AZ_huf_dx41.x41_end RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_ret := (AZ_huf_dx41.x41_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_d1 := (AZ_huf_dx41_1e.x41_d1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX HRL DHI).
  Notation x41_d2 := (AZ_huf_dx41_2e.x41_d2 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX HRL DHI).
  Notation x41_d3 := (AZ_huf_dx41_3e.x41_d3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX HRL DHI).
  Notation x41_d4 := (AZ_huf_dx41_4e.x41_d4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX HRL DHI).

  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\ (4096 <= SRC <= 140737488355328) /\
                 (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\ (17594333495296 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\
                 (0 <= rsv <= 255) /\ (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333498016 <= SPV) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  Ltac lside := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- forall _, _ => idtac
    | |- SINVA _ _ _ => first [assumption | unfold SINVA in *; lia]
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia]
    | |- @eq word _ _ => first [eassumption | reflexivity | idtac]
    | |- _ /\ _ => first [lia | kx_lia | idtac]
    | |- _ \/ _ => try lia
    | |- Z.le _ _ => lia
    | |- Z.lt _ _ => lia
    | |- _ => eassumption
    end.
  Ltac cside := first [apply munch_refl | apply wmono_refl | lside].

  (* [comment removed for export] *)
  Definition X41PA (mm : amem) (rest : list byte) : Prop :=
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    rw_cells bsegs mm (SPV + -336) [CB 112 rest].

  Lemma x41pa_transport : forall mm mm' rest W, X41PA mm rest -> munch W mm mm' -> wmono bsegs mm mm' ->
    disjoint_from W (SPV + -104) 104 -> disjoint_from W (SPV + -336) 112 -> X41PA mm' rest.
  Proof using CTX.
    intros mm mm' rest W (SV & RS) MU WM D1 D3. split.
    - eapply (rw_cells_transport bsegs _ mm mm' _ _ SV MU WM). exact D1.
    - eapply (rw_cells_transport bsegs _ mm mm' _ _ RS MU WM). exact D3.
  Qed.

  Lemma x41_einvA : forall mm rest (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : word)
      (c1 b1 p1 st1 lm1 c2 b2 p2 st2 lm2 c3 b3 p3 st3 lm3 c4 b4 p4 st4 lm4 : word) pad1 pad2 pad3 pad4,
    X41PA mm rest -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> munch W0 m0 mm -> wmono bsegs m0 mm -> stk bsegs mm lo (SPV + -480) ->
    FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ->
    BD1 mm c1 b1 pad1 p1 st1 lm1 -> BD2 mm c2 b2 pad2 p2 st2 lm2 -> BD3 mm c3 b3 pad3 p3 st3 lm3 -> BD4 mm c4 b4 pad4 p4 st4 lm4 -> EINVA mm.
  Proof using CTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'.
    intros until pad4. intros (SV & RS) MI OUT MU0 WM0 STK FR B1 B2 B3 B4.
    pose proof (stk_of_rw_cells bsegs mm _ _ FR) as H1.
    pose proof (stk_of_rw_cells bsegs mm _ _ B1) as H2.
    pose proof (stk_of_rw_cells bsegs mm _ _ RS) as H3.
    pose proof (stk_of_rw_cells bsegs mm _ _ B4) as H4.
    pose proof (stk_of_rw_cells bsegs mm _ _ B3) as H5.
    pose proof (stk_of_rw_cells bsegs mm _ _ B2) as H6.
    cbn [cells_size csize Nat.add] in H1, H2, H3, H4, H5, H6.
    change (Z.of_nat 104) with 104 in H1. change (Z.of_nat 40) with 40 in H2, H4, H5, H6. change (Z.of_nat 112) with 112 in H3.
    replace (SPV + -480 + 104) with (SPV + -376) in H1 by lia.
    replace (SPV + -376 + 40) with (SPV + -336) in H2 by lia.
    replace (SPV + -336 + 112) with (SPV + -224) in H3 by lia.
    replace (SPV + -224 + 40) with (SPV + -184) in H4 by lia.
    replace (SPV + -184 + 40) with (SPV + -144) in H5 by lia.
    replace (SPV + -144 + 40) with (SPV + -104) in H6 by lia.
    unfold AZ_huf_dx41.EINVA. split; [exact OUT|]. split; [exact SV|]. split; [|split; [exact MU0|split; [exact WM0|exact MI]]].
    eapply (stk_merge bsegs mm lo (SPV + -144)); [|exact H6|lia].
    eapply (stk_merge bsegs mm lo (SPV + -184)); [|exact H5|lia].
    eapply (stk_merge bsegs mm lo (SPV + -224)); [|exact H4|lia].
    eapply (stk_merge bsegs mm lo (SPV + -336)); [|exact H3|lia].
    eapply (stk_merge bsegs mm lo (SPV + -376)); [|exact H2|lia].
    eapply (stk_merge bsegs mm lo (SPV + -480)); [exact STK|exact H1|lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x41_c0 : forall mm rest j pe1 pe2 pe3 dl P1 P2 P3 P4 S1 n1 bs1 o1 bc1 S2 n2 bs2 o2 bc2 S3 n3 bs3 o3 bc3 S4 n4 bs4 o4 bc4 (c1 c2 c3 c4 : word) pad1 pad2 pad3 pad4
      (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31 : word)
      (w0 w1 w2 w5 w6 w7 : word),
    X41PA mm rest -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    stk bsegs mm lo (SPV + -480) ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (pe1)) w5 w6 w7 (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (DST + pe2)) OEND) ->
    BD1 mm c1 (Z_to_bv 64 bc1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    BD2 mm c2 (Z_to_bv 64 bc2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    BD3 mm c3 (Z_to_bv 64 bc3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    BD4 mm c4 (Z_to_bv 64 bc4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    bytes_at bsegs mm S1 bs1 -> zlen bs1 = n1 -> SRC <= S1 -> S1 + n1 <= SRC + n -> 1 <= n1 -> SINVA o1 n1 bc1 -> 0 <= bc1 < 2147483648 ->
    bytes_at bsegs mm S2 bs2 -> zlen bs2 = n2 -> SRC <= S2 -> S2 + n2 <= SRC + n -> 1 <= n2 -> SINVA o2 n2 bc2 -> 0 <= bc2 < 2147483648 ->
    bytes_at bsegs mm S3 bs3 -> zlen bs3 = n3 -> SRC <= S3 -> S3 + n3 <= SRC + n -> 1 <= n3 -> SINVA o3 n3 bc3 -> 0 <= bc3 < 2147483648 ->
    bytes_at bsegs mm S4 bs4 -> zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 1 <= n4 -> SINVA o4 n4 bc4 -> 0 <= bc4 < 2147483648 ->
    0 <= j -> 0 <= pe1 -> pe1 <= pe2 -> pe2 <= pe3 -> pe3 + j <= dcap -> dl = tl + 256 * rsv ->
    P1 = DST + j -> P2 = DST + (pe1 + j) -> P3 = DST + (pe2 + j) -> P4 = DST + (pe3 + j) ->
    evtF bsegs RNG POST (ST 0xa224c mm (Z_to_bv 64 (DST + pe3)) x5 x6 x7 (Z_to_bv 64 (P2)) x9 (Z_to_bv 64 18446744073709551596) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (P1)) (Z_to_bv 64 (dl)) (Z_to_bv 64 (P4)) x21 (Z_to_bv 64 (P3)) (Z_to_bv 64 (DST + pe1)) SB x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (pe1)) x28 x29 x30 x31).
  Proof using CTX ACTX HRL DHI.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros mm rest j pe1 pe2 pe3 dl P1 P2 P3 P4 S1 n1 bs1 o1 bc1 S2 n2 bs2 o2 bc2 S3 n3 bs3 o3 bc3 S4 n4 bs4 o4 bc4 c1 c2 c3 c4 pad1 pad2 pad3 pad4
      x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31
      w0 w1 w2 w5 w6 w7
      PV MU0 WM0 MI OUT DTB STK FR B1 B2 B3 B4
      SB1 BL1 SS1 SE1 LN1 HS1 HB1 SB2 BL2 SS2 SE2 LN2 HS2 HB2 SB3 BL3 SS3 SE3 LN3 HS3 HB3 SB4 BL4 SS4 SE4 LN4 HS4 HB4
      HJ HP1 HP12 HP23 HP3 HDL HQ1 HQ2 HQ3 HQ4.
    subst P1 P2 P3 P4. facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (RFR : rng RNG (SPV - 480) 480) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (KF : 0 <= j <= 4294967296 /\ 0 <= pe1 <= 4294967296 /\ 0 <= pe2 <= 4294967296 /\ 0 <= pe3 <= 4294967296 /\
                 0 <= pe1 + j <= 4294967296 /\ 0 <= pe2 + j <= 4294967296 /\ 0 <= pe3 + j <= 4294967296 /\
                 4096 <= DST + pe1 <= 140737488355328 /\ 4096 <= DST + pe2 <= 140737488355328 /\ 4096 <= DST + pe3 <= 140737488355328 /\
                 4096 <= DST + j <= 140737488355328 /\ 4096 <= DST + (pe1 + j) <= 140737488355328 /\ 4096 <= DST + (pe2 + j) <= 140737488355328 /\
                 4096 <= DST + (pe3 + j) <= 140737488355328)
      by (clear - HJ HP1 HP12 HP23 HP3 R1; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9 & KF10 & KF11 & KF12 & KF13 & KF14).
    kx_autoFLA FR (@nil kza) [0xa2268; 0xa3c30] 24%nat
      [KZRange j 0 4294967296; KZRange pe1 0 4294967296; KZRange pe2 0 4294967296; KZRange pe3 0 4294967296;
       KZRange (pe1 + j) 0 4294967296; KZRange (pe2 + j) 0 4294967296; KZRange (pe3 + j) 0 4294967296;
       KZRange (DST + pe1) 4096 140737488355328; KZRange (DST + pe2) 4096 140737488355328; KZRange (DST + pe3) 4096 140737488355328;
       KZRange (DST + j) 4096 140737488355328; KZRange (DST + (pe1 + j)) 4096 140737488355328; KZRange (DST + (pe2 + j)) 4096 140737488355328;
       KZRange (DST + (pe3 + j)) 4096 140737488355328;
       KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange SPV 17594333498016 140737488355328]
      [(SPV + -480, 104)] [(SPV - 480, 480)].
    all: [> aside ..].
    all: try clear GF8 GF9 GF10 GF11 GF12 GF13.
    (* [comment removed for export] *)
    all: [> lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa3c30) _ _ ?m _) =>
             try (replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply bv64_eqm_k; reflexivity));
             try (replace (Z_to_bv 64 18446744073709551596) with (Z_to_bv 64 (2^64 - 20)) by (apply bv64_eqm_k; reflexivity));
             eapply x41_ret; [eapply (x41_einvA _ rest); [exact PV | eassumption..] | right; split; [vm_compute; reflexivity | lia]]
         | _ => idtac
         end ..].
    (* [comment removed for export] *)
    assert (PE1 : 0 <= pe1 <= dcap) by (clear - HJ HP1 HP12 HP23 HP3; lia).
    assert (PE2 : 0 <= pe2 <= dcap) by (clear - HJ HP1 HP12 HP23 HP3; lia).
    assert (PE3 : 0 <= pe3 <= dcap) by (clear - HJ HP1 HP12 HP23 HP3; lia).
    eapply (x41_d1 pe1 PE1 mm mm j o1 S1 n1 bs1 dl bc1 c1 pad1); cside.
    intros mm1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? c1' b1' p1' pad1' MU1 WM1 MU01 WM01 MI1 OUT1 DTB1 STK1 FR1 B1'.
    (* [comment removed for export] *)
    assert (B2_1 : BD2 mm1 c2 (Z_to_bv 64 bc2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm mm1); [exact B2 | exact MU1 | exact WM1 |];
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - R1 LO OS1; lia).
    assert (B3_1 : BD3 mm1 c3 (Z_to_bv 64 bc3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm mm1); [exact B3 | exact MU1 | exact WM1 |];
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - R1 LO OS1; lia).
    assert (B4_1 : BD4 mm1 c4 (Z_to_bv 64 bc4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm mm1); [exact B4 | exact MU1 | exact WM1 |];
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - R1 LO OS1; lia).
    assert (SB2_1 : bytes_at bsegs mm1 S2 bs2)
      by (eapply (bytes_at_transport bsegs _ mm mm1 S2 bs2); [exact SB2 | exact MU1 | cbn [disjoint_from]; clear - SS2 SE2 BL2 R2 DJ1 OS2 LO; lia]).
    assert (SB3_1 : bytes_at bsegs mm1 S3 bs3)
      by (eapply (bytes_at_transport bsegs _ mm mm1 S3 bs3); [exact SB3 | exact MU1 | cbn [disjoint_from]; clear - SS3 SE3 BL3 R2 DJ1 OS2 LO; lia]).
    assert (SB4_1 : bytes_at bsegs mm1 S4 bs4)
      by (eapply (bytes_at_transport bsegs _ mm mm1 S4 bs4); [exact SB4 | exact MU1 | cbn [disjoint_from]; clear - SS4 SE4 BL4 R2 DJ1 OS2 LO; lia]).
    assert (PV1 : X41PA mm1 rest)
      by (eapply (x41pa_transport mm mm1 rest _ PV MU1 WM1); cbn [disjoint_from]; clear - R1 LO OS1; lia).
    eapply (x41_d2 pe2 PE2 mm1 mm1 (pe1 + j) o2 S2 n2 bs2 dl bc2 c2 pad2); cside.
    intros mm2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? c2' b2' p2' pad2' MU2 WM2 MU02 WM02 MI2 OUT2 DTB2 STK2 FR2 B2'.
    (* [comment removed for export] *)
    assert (B1_2 : BD1 mm2 c1' b1' pad1' p1' (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm1 mm2); [exact B1' | exact MU2 | exact WM2 |];
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - R1 LO OS1; lia).
    assert (B3_2 : BD3 mm2 c3 (Z_to_bv 64 bc3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm1 mm2); [exact B3_1 | exact MU2 | exact WM2 |];
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - R1 LO OS1; lia).
    assert (B4_2 : BD4 mm2 c4 (Z_to_bv 64 bc4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm1 mm2); [exact B4_1 | exact MU2 | exact WM2 |];
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - R1 LO OS1; lia).
    assert (SB3_2 : bytes_at bsegs mm2 S3 bs3)
      by (eapply (bytes_at_transport bsegs _ mm1 mm2 S3 bs3); [exact SB3_1 | exact MU2 | cbn [disjoint_from]; clear - SS3 SE3 BL3 R2 DJ1 OS2 LO; lia]).
    assert (SB4_2 : bytes_at bsegs mm2 S4 bs4)
      by (eapply (bytes_at_transport bsegs _ mm1 mm2 S4 bs4); [exact SB4_1 | exact MU2 | cbn [disjoint_from]; clear - SS4 SE4 BL4 R2 DJ1 OS2 LO; lia]).
    assert (PV2 : X41PA mm2 rest)
      by (eapply (x41pa_transport mm1 mm2 rest _ PV1 MU2 WM2); cbn [disjoint_from]; clear - R1 LO OS1; lia).
    eapply (x41_d3 pe3 PE3 mm2 mm2 (pe2 + j) o3 S3 n3 bs3 dl bc3 c3 pad3); cside.
    intros mm3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? c3' b3' p3' pad3' MU3 WM3 MU03 WM03 MI3 OUT3 DTB3 STK3 FR3 B3'.
    (* [comment removed for export] *)
    assert (B1_3 : BD1 mm3 c1' b1' pad1' p1' (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm2 mm3); [exact B1_2 | exact MU3 | exact WM3 |];
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - R1 LO OS1; lia).
    assert (B2_3 : BD2 mm3 c2' b2' pad2' p2' (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm2 mm3); [exact B2' | exact MU3 | exact WM3 |];
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - R1 LO OS1; lia).
    assert (B4_3 : BD4 mm3 c4 (Z_to_bv 64 bc4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm2 mm3); [exact B4_2 | exact MU3 | exact WM3 |];
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - R1 LO OS1; lia).
    assert (SB4_3 : bytes_at bsegs mm3 S4 bs4)
      by (eapply (bytes_at_transport bsegs _ mm2 mm3 S4 bs4); [exact SB4_2 | exact MU3 | cbn [disjoint_from]; clear - SS4 SE4 BL4 R2 DJ1 OS2 LO; lia]).
    assert (PV3 : X41PA mm3 rest)
      by (eapply (x41pa_transport mm2 mm3 rest _ PV2 MU3 WM3); cbn [disjoint_from]; clear - R1 LO OS1; lia).
    eapply (x41_d4 mm3 mm3 (pe3 + j) o4 S4 n4 bs4 dl bc4 c4 pad4); cside.
    intros mm4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? c4' b4' p4' pad4' MU4 WM4 MU04 WM04 MI4 OUT4 DTB4 STK4 FR4 B4'.
    (* [comment removed for export] *)
    assert (B1_4 : BD1 mm4 c1' b1' pad1' p1' (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm3 mm4); [exact B1_3 | exact MU4 | exact WM4 |];
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - R1 LO OS1; lia).
    assert (B2_4 : BD2 mm4 c2' b2' pad2' p2' (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm3 mm4); [exact B2_3 | exact MU4 | exact WM4 |];
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - R1 LO OS1; lia).
    assert (B3_4 : BD3 mm4 c3' b3' pad3' p3' (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)))
      by (eapply (rw_cells_transport bsegs _ mm3 mm4); [exact B3' | exact MU4 | exact WM4 |];
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - R1 LO OS1; lia).
    assert (PV4 : X41PA mm4 rest)
      by (eapply (x41pa_transport mm3 mm4 rest _ PV3 MU4 WM4); cbn [disjoint_from]; clear - R1 LO OS1; lia).
    eapply x41_end; [| exact FR4 | exact B1_4 | exact B2_4 | exact B3_4 | exact B4'].
    eapply (x41_einvA mm4 rest); [exact PV4 | exact MI4 | exact OUT4 | exact MU04 | exact WM04 | exact STK4 | exact FR4 | exact B1_4 | exact B2_4 | exact B3_4 | exact B4'].
  Qed.
End DX41AC0.
End CANSEC1.
