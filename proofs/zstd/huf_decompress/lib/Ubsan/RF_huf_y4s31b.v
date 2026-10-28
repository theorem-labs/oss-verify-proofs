(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s
  RF_huf_y4s_iface RF_huf_y4_kit_reload RF_huf_y4s31_kit RF_huf_y4s31.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Section CANSEC1. Context {rc : runConstT}.
Section Y4S31B.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 4 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 4 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation YB l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).
  Notation Y4F' mm spl b4 b3 b2 b1 := (Y4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl b4 b3 b2 b1).

  (* [comment removed for export] *)
  Variables (Q1 L1 v16 v24 v32 v40 v48 v64 v72 v80 v88 v104 : Z) (j0 : list byte) (b2 b3 b4 : list cell) (y18 y20 y27 : word).
  Hypothesis HL1 : 1 <= L1 /\ 6 + L1 <= n.
  Hypothesis HQ1 : 2 <= Q1 <= dcap.
  Notation SPL v112 := (SPLB (tl + 256 * mtl) v16 v24 v32 v40 v48 (DST + dcap - 7) v64 v72 v80 v88 (DST + Q1) v104 v112
                          (DST + dcap) (DT + 4) j0).
  Notation T2S pc mm xra t0 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 t3 t4 t5 :=
    (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp t0 (Z_to_bv 64 (DT + 4)) t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
             y18 (Z_to_bv 64 (2^61)) y20 x21 x22 x23 x24 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 dcap) y27
             t3 t4 t5 (Z_to_bv 64 (DST + dcap)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Hypothesis CONT : forall mm c1 bc1 p1 st1 j1 (xra t0 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 t3 t4 t5 : word),
    Y4F' mm (SPL tl) b4 b3 b2 (BD4 c1 bc1 p1 st1 j1) ->
    evt usegs POST (T2S 0x1be98 mm xra t0 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 t3 t4 t5).

  Ltac y4open H :=
    destruct H as (OUTX & SRC & TB & STK & FL & FLS & F4 & F4S & F3 & F3S & F2 & F2S & F1 & F1S & SAV & JL & FR & MI & MU & WM);
    destruct OUTX as (buf & OUT & LB); change (zlen buf) with (Z.of_nat (length buf)) in LB;
    destruct SAV as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & SAV); destruct JL as (jl & JL);
    pose proof TOK as (TL1 & TLN & TCK); cbv [HUF_TABLELOG_MAX] in TL1; cbv [FseNCount.Zlength] in TLN;
    pose proof (DP ltac:(lia)) as D8; pose proof (length_map (Z_to_bv 8) src) as LMS; unfold SPLB, BD4 in *.
  Ltac y4pack H := ubdnorm H; unfold Y4F, SPLB, BD4; upack.
  Notation NDT := (Z_to_bv 64 (Z.lxor (DT + 4) 18446744073709551615)).

  Ltac y4norm := try (rewrite u_shamt by lia);
    repeat (match goal with |- context [sx32 (Z_to_bv 64 ?z)] => rewrite (sx32_small z) by lia end).

  Ltac y31rl c bc pt j1 :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a794) _ _ ?mx _) =>
        eapply evt_cut;
        [ eapply y4_reload_proof with (BD := SP + -656) (S := SS + 6) (n := zlen src - 6) (c := c) (bc := bc)
            (p := SS + 6 + pt) (pad := j1) (sqb := skipn 6 (map (Z_to_bv 8) src));
          first [ assumption
                | unfold y4_bd; assumption
                | apply u_bytes_skipn; [rewrite length_map; lia | assumption]
                | rewrite length_skipn, length_map; lia
                | lia ]
        | post_call usegs mx;
          lazymatch goal with H : rw_cells _ _ (SP + -656) _ |- _ => unfold y4_bd in H; rename H into F1 end ]
    | |- _ => idtac
    end.

  Notation Y31 l := (YB l Q1 L1 v16 v24 v32 v40 v48 v64 v72 v80 v88 v104 j0 b2 b3 b4 y18 y20 y27 HL1 HQ1 CONT)
    (only parsing).

  (* [comment removed for export] *)
  Lemma y31_dec5 : forall q mm cx bx pt j1 (xra t0 t2 x8 a3 a4 a5 a6 a7 x21 t3 t4 t5 : word),
    Y4F' mm (SPL tl) b4 b3 b2 (BD4 cx bx (SS + 6 + pt) (SS + 6) j1) -> 0 <= q -> q + 10 <= Q1 ->
    0 <= pt -> (pt = 0 \/ pt + 8 <= L1) -> 0 <= bx <= 7 -> tl <= 11 ->
    (forall q' mm' c' bc' (xra' t0' t2' x8' a2' a3' a4' a5' a6' a7' x21' t3' t4' t5' : word),
       Y4F' mm' (SPL tl) b4 b3 b2 (BD4 c' bc' (SS + 6 + pt) (SS + 6) j1) -> q < q' <= Q1 -> 0 <= bc' <= 64 ->
       evt usegs POST (T2S 0x1b494 mm' xra' t0' t2' x8' (Z_to_bv 64 64) (Z_to_bv 64 bc') (Z_to_bv 64 (DST + q')) a2' a3' a4' a5' a6' a7'
                           x21' (Z_to_bv 64 (DST + Q1 + -9)) (Z_to_bv 64 (64 - tl)) NDT t3' t4' t5')) ->
    evt usegs POST (T2S 0x1b5b0 mm xra t0 t2 x8 (Z_to_bv 64 64) (zx32 (Z_to_bv 64 bx)) (Z_to_bv 64 (DST + q))
                        (Z_to_bv 64 (cx ≪ (bv_unsigned (zx32 (Z_to_bv 64 bx)) mod 64))) a3 a4 a5 a6 a7 x21
                        (Z_to_bv 64 (DST + Q1 + -9)) (Z_to_bv 64 (64 - tl)) NDT t3 t4 t5).
  Proof using All.
    intros until t5. intros FR0 Q0 QL P0 PT BX T11 K. y4open FR0.
    zstep. uwalk [0x1b494; 0x1a794; 0x1bbe4; 0x1bdfc; 0x1bc0c; 0x1bd90; 0x1dc54; 0x1dc90; 0x1dd14; 0x1dd70; 0x1dd84] tl DT cells cbs ECB TCK OUT LB SRC.
    all: unum; rassoc DST Q1.
    all: first [ solve [exfalso; llia]
               | eapply K; [y4pack F1 | lia | lia]
               | eapply (Y31 y31_pre2r); [y4pack F1 | lia | lia | intros; eexists; split; [reflexivity | lia]]
               | eapply (Y31 y31_last); [y4pack F1 | lia] ].
  Qed.

  (* [comment removed for export] *)
  Lemma y31_loop5 : forall (fuel : nat) q mm c bc pt j1 (xra t0 t2 x8 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 : word),
    Y4F' mm (SPL tl) b4 b3 b2 (BD4 c bc (SS + 6 + pt) (SS + 6) j1) -> 0 <= q <= Q1 -> Q1 - q < Z.of_nat fuel ->
    0 <= pt -> (pt = 0 \/ pt + 8 <= L1) -> 0 <= bc <= 64 -> tl <= 11 ->
    evt usegs POST (T2S 0x1b494 mm xra t0 t2 x8 (Z_to_bv 64 64) (Z_to_bv 64 bc) (Z_to_bv 64 (DST + q)) a2 a3 a4 a5 a6 a7 x21
                        (Z_to_bv 64 (DST + Q1 + -9)) (Z_to_bv 64 (64 - tl)) NDT t3 t4 t5).
  Proof using All.
    induction fuel as [|fuel IH]; intros until t5; intros FR0 QR FU P0 PT BC T11; [lia|]. y4open FR0.
    zstep. uwalk [0x1b494; 0x1b5b0; 0x1a794; 0x1bbe4; 0x1bdfc; 0x1bc0c; 0x1bd90; 0x1dc54; 0x1dc90; 0x1dd14; 0x1dd70; 0x1dd84] tl DT cells cbs ECB TCK OUT LB SRC.
    all: y31rl c bc pt j1.
    all: uwalk [0x1b494; 0x1b5b0; 0x1a794; 0x1bbe4; 0x1bdfc; 0x1bc0c; 0x1bd90; 0x1dc54; 0x1dc90; 0x1dd14; 0x1dd70; 0x1dd84] tl DT cells cbs ECB TCK OUT LB SRC.
    all: try (rewrite (u_bcmod bc) in * by lia).
    all: ucgen (SP + -656); ptnorm (SP + -656) (SS + 6).
    all: first [ eapply y31_dec5; [y4pack F1 | lia | lia | lia | lia | lia | lia |
                   intros q' mm' c' bc' xra' t0' t2' x8' a2' a3' a4' a5' a6' a7' x21' t3' t4' t5' FR' QQ BB;
                   eapply IH; [exact FR' | lia | lia | lia | lia | lia | lia]]
               | unum; rassoc DST Q1;
                 first [ solve [exfalso; llia]
                       | eapply (Y31 y31_pre2r); [y4pack F1 | lia | lia | intros; eexists; split; [reflexivity | lia]]
                       | eapply (Y31 y31_last); [y4pack F1 | lia] ] ].
  Qed.

End Y4S31B.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
