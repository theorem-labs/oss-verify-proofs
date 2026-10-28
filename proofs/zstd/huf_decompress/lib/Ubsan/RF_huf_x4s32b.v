(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_x4s RF_huf_y4s31_kit RF_huf_x4s31_kit RF_huf_y4_kit_reload RF_huf_x4s32.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Section CANSEC1. Context {rc : runConstT}.
Section X4S32.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 2 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 2 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation XB l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).
  Notation X4F' mm spl b1 b2 b3 b4 := (X4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl b1 b2 b3 b4).


  (* [comment removed for export] *)
  Variables (O2 L2 Q2 SEG v8 v16 v24 v32 v40 v48 v56 v80 v104 v128 : Z) (j0 j96 j120 : list byte) (bd1 bd3 bd4 : list cell).
  Variables (y5 y6 y8 : word).
  Hypothesis HL2 : 6 <= O2 /\ 1 <= L2 /\ O2 + L2 <= n.
  Hypothesis HQ2 : 0 < SEG <= Q2 /\ Q2 <= dcap.
  Notation SPL := (SPL3 v8 v16 v24 v32 v40 v48 v56 (DST + dcap) (DST + SEG) v80 (DST + Q2) v104 DST v128 j0 j96 j120).

  Notation ST pc mm xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x23 x26 t3 t4 t5 t6 :=
    (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (2^62)) y5 y6 x23 y8 (Z_to_bv 64 (DT + 4)) x26
             (Z_to_bv 64 (DST + dcap)) t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Hypothesis CONT : forall mm c2 b2 p2 jp2 (xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x23 x26 t3 t4 t5 t6 : word),
    X4F' mm SPL bd1 (BD4 c2 b2 p2 (SS + O2) jp2) bd3 bd4 ->
    evt usegs POST (ST 103732 mm xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x23 x26 t3 t4 t5 t6).

  Ltac x4open H :=
    destruct H as ((buf & OUT & LB) & SRC & CBS & STK & SPC & L0 & BDa & LBa & (jj & JJ) & BDd & LDd & BDc & LDc & BDb & LDb
                   & FR & MI & MU & WM);
    change (zlen buf) with (Z.of_nat (length buf)) in LB;
    pose proof TOK as (TL1 & TLN & TCK); cbv [HUF_TABLELOG_MAX] in TL1; cbv [FseNCount.Zlength] in TLN;
    pose proof (DP ltac:(lia)) as D8; pose proof (length_map (Z_to_bv 8) src) as LMS; unfold SPL3, BD4 in *;
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  Ltac x4pack H := ubdnorm H; unfold X4F, SPL3, BD4; upack.
  Ltac xgen := repeat match goal with |- context [Z_to_bv 64 ?E] =>
    lazymatch E with context [Znth _ src] =>
      let w := fresh "w" in let EW := fresh "EW" in remember (Z_to_bv 64 E) as w eqn:EW; clear EW end end.
  Ltac xwalkg stops TCK OUT LB SRC := repeat (xwalk1 stops tl DT cells cbs ECB TCK OUT LB SRC; try xgen).

  Notation X32 l := (XB l O2 L2 Q2 SEG v8 v16 v24 v32 v40 v48 v56 v80 v104 v128 j0 j96 j120 bd1 bd3 bd4 y5 y6 y8 HL2 HQ2 CONT) (only parsing).

  (* [comment removed for export] *)
  Lemma x32_entry : forall q2 pt2 c2 b2 jp2 mm (xra t0 t1 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x26 t3 t4 t5 t6 : word),
    X4F' mm SPL bd1 (BD4 c2 b2 (SS + O2 + pt2) (SS + O2) jp2) bd3 bd4 ->
    0 <= q2 <= Q2 -> 0 <= pt2 -> (pt2 = 0 \/ pt2 + 8 <= L2) -> 0 <= b2 < 2^31 ->
    evt usegs POST (ST 102756 mm xra t0 t1 (Z_to_bv 64 DST) x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 (DST + q2)) x26
                       t3 t4 t5 t6).
  Proof using All.
    intros until t6. intros XF Q2R P0 PL BR. x4open XF.
    xwalkg [102820; 103616; 103652; 103732] TCK OUT LB SRC.
    all: first [ solve [eapply CONT; x4pack BDa]
               | solve [eapply (X32 x32_tail (Z.to_nat (Q2 - q2)) q2); [x4pack BDa | lia ..]]
               | solve [eapply (X32 x32_rl q2 pt2); [x4pack BDa | lia ..]]
               | solve [eapply (X32 x32_loop (Z.to_nat (Q2 - q2 + 1)) q2);
                          [ lia | lia | lia | | | reflexivity | reflexivity | x4pack BDa | reflexivity ];
                        unfold PINV; lia] ].
  Qed.

End X4S32.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
