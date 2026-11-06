(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac MemRange ZdCellKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import ZdFrame ZdDCtx.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memmove RZ_seq_iface RZ_seq_safecopy RZ_seq_execend_a RZ_seq_execend_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac rdl_to_bytes RDL LB :=
  lazymatch type of RDL with rdbl ?segs ?m1 ?r0 ?r1 =>
    let lbs := fresh "lbs" in let LLEN := fresh "LLEN" in
    destruct (rdbl_bytes segs m1 r0 r1 RDL ltac:(lia)) as (lbs & LLEN & LB); clear RDL end.
Ltac bytes_to_rdl LB RDL :=
  lazymatch type of LB with bytes_at ?segs ?m1 ?r0 ?lbs =>
    pose proof (rdbl_of_bytes_at segs m1 r0 lbs LB) as RDL;
    lazymatch goal with LLEN : length lbs = Z.to_nat (?r1 - r0) |- _ =>
      rewrite LLEN in RDL; replace (r0 + Z.of_nat (Z.to_nat (r1 - r0))) with r1 in RDL by lia end;
    clear LB end.
(* [comment removed for export] *)
Tactic Notation "useI" uconstr(L) :=
  eapply L; try eassumption;
  try (lazymatch goal with |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [ reflexivity | f_equal; lia ] end); try lia.

Section C.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z).
  Hypothesis HY : xe_hyps SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX B0 B1.
  Hypothesis HSZ : LL + ML <= OEND - OP.
  Hypothesis HLIT : LL <= LLIM - LP.
  Notation POST := (zd_execend_post 192 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP OEND SQP LPP LP LLIM LL ML OFS B0 B1 lo m).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation XIm := (XI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo OP OEND SQP LPP LL ML OFS B0 B1).
  (* [comment removed for export] *)
  Notation STL pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 x28 x29 x30 x31 :=
    (ST pc mm xra x5 x6 x7 (Z_to_bv 64 (OP + LL)) (Z_to_bv 64 (OEND + -32)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        xs2 xs3 xs4 (Z_to_bv 64 (ML + LL)) (Z_to_bv 64 SQP) (Z_to_bv 64 PFX) (Z_to_bv 64 OFS) (Z_to_bv 64 (LP + LL)) (Z_to_bv 64 PFX) (Z_to_bv 64 LPP)
        x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma xe_w2_loop : forall (q : nat) m1 w16 (d sr : Z) xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 x28 x29 x30 x31,
    XIm (Z_to_bv 64 (OEND + -32 - OP)) w16 LP m1 -> rdbl psegs m1 LP (LLIM + 32) ->
    OP <= d < OEND - 32 -> sr - LP = d - OP -> OEND - 32 < OP + LL -> OEND - 32 - d <= 32 * (Z.of_nat q + 1) ->
    xs3 = Z_to_bv 64 d -> xs4 = Z_to_bv 64 (sr + 16) ->
    evt psegs POST (STL 0x1c2b4 m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 LP) xs3 xs4 x28 x29 x30 x31).
  Proof.
    induction q as [|q IH]; intros until x31; intros I RDL HD HREL HOW HQ -> ->; open_hy HY; open_xi I.
    - zstep. zstep. zstep. zstep. mmvl REG RDL d sr. zstep. zstep. zstep. zstep. mmvl REG RDL (d + 16) (sr + 16).
      zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. zstep. zstep. useE xe_lit_tail.
    - zstep. zstep. zstep. zstep. mmvl REG RDL d sr. zstep. zstep. zstep. zstep. mmvl REG RDL (d + 16) (sr + 16).
      zstep. zstep. zstep. if_cases K; zify_cond K.
      + use (IH _ w16 (d + 32) (sr + 32)).
      + zstep. zstep. zstep. useE xe_lit_tail.
  Qed.

  (* [comment removed for export] *)
  Lemma xe_w2 : forall m1 w8 w16 xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 x28 x29 x30 x31,
    XIm w8 w16 LP m1 -> rdbl psegs m1 LP (LLIM + 32) -> 7 < LL -> OEND - 32 < OP + LL -> OP <= OEND - 32 ->
    evt psegs POST (STL 0x1c28c m1 xra x5 x6 x7 (Z_to_bv 64 OP) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 LP) xs3 (Z_to_bv 64 LL) x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RDL HLL HOW HOP. open_hy HY. open_xi I.
    zstep. zstep. zstep. zstep. zstep. mmvl REG RDL OP LP.
    zstep. rdl_to_bytes RDL LB. zstep. bytes_to_rdl LB RDL.
    zstep. if_cases K; zify_cond K.
    - zstep. zstep. zstep. useE xe_lit_tail.
    - zstep. zstep. useE (xe_w2_loop (Z.to_nat (OEND - OP)) _ _ (OP + 16) (LP + 16)).
  Qed.

  (* [comment removed for export] *)
  Lemma xe_lit : forall m1 w8 w16 xra x5 x6 x7 xa1 xa2 xa3 xa5 xa6 xa7 xs3 x28 x29 x30 x31,
    XIm w8 w16 LP m1 -> rdbl psegs m1 LP (LLIM + 32) ->
    evt psegs POST (STL 0x1c260 m1 xra x5 x6 x7 (Z_to_bv 64 OP) xa1 xa2 xa3 (Z_to_bv 64 7) xa5 xa6 xa7 (Z_to_bv 64 LP) xs3 (Z_to_bv 64 LL) x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RDL. open_hy HY.
    zstep. if_cases K; zify_cond K.
    - zstep. if_cases K1; zify_cond K1.
      + useI xe_w1.
      + zstep. if_cases K2; zify_cond K2.
        * useI xe_lit_tail.
        * useI xe_w2.
    - zstep. if_cases K1; zify_cond K1.
      + useI xe_match.
      + useI (xe_lit_short_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY HSZ HLIT (Z.to_nat (LL - 1))).
  Qed.
End C.

Section D.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z).
  Hypothesis HY : xe_hyps SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX B0 B1.
  Notation POST := (zd_execend_post 192 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP OEND SQP LPP LP LLIM LL ML OFS B0 B1 lo m).

  (* [comment removed for export] *)
  Lemma xe_main : forall (t0 t1 t2 t3 t4 t5 t6 : word),
    stk psegs m B0 B1 -> stk psegs m lo SPV -> mem_inv psegs m ->
    rw_cells psegs m SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)] ->
    rw_cells psegs m LPP [C8 (Z_to_bv 64 LP)] -> rdbl psegs m LP (LLIM + 32) ->
    evt psegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OP) (Z_to_bv 64 OEND) (Z_to_bv 64 SQP) (Z_to_bv 64 LPP) (Z_to_bv 64 LLIM)
               (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 DEND) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1c1d4) fc None m (seg_rom psegs)).
  Proof.
    intros until t6. intros REG STK MI SQC LPC RDL. open_hy HY.
    assert (MU : munch [(OP, OEND); (LPP, LPP + 8); (SPV - 192, SPV)] m m) by apply munch_refl.
    assert (WM : wmono psegs m m) by apply wmono_refl.
    rdl_to_bytes RDL LB.
    zstep. carve_frame 128%nat STK.
    do 13 zstep.
    lazymatch type of FR with rw_cells _ _ _ (CB 24 ?j :: ?post) =>
      apply (rw_cells_split_CB psegs _ _ [] 24 j post [8; 8; 8]%nat) in FR; [| reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [c0] j post FR) as [w8 FR1] end. cbn [app] in FR1. clear FR.
    lazymatch type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [c0; c1] j post FR1) as [w16 FR] end. cbn [app] in FR. clear FR1.
    zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        eapply (xe_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX B0 B1 HY _ (2^64 - 20) LP w8 w16);
          [ close_xi | lia | left; reflexivity | apply bv_eq; reflexivity ].
      + zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        bytes_to_rdl LB RDL.
        eapply (xe_lit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX B0 B1 HY ltac:(lia) ltac:(lia) _ w8 (Z_to_bv 64 DEND));
          [ close_xi | exact RDL ].
    - (* [comment removed for export] *)
      zstep. zstep.
      eapply (xe_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX B0 B1 HY _ (2^64 - 70) LP w8 w16);
          [ close_xi | lia | left; reflexivity | apply bv_eq; reflexivity ].
  Qed.
End D.

Theorem zd_execend_proof : zd_execend_stmt.
Proof.
  unfold zd_execend_stmt, PZD_EXECEND, apart, off_stack. intros until B1.
  intros REG B0L B1H PFXR OENDR SQC LPC LLR MLR OFSR LPR LLIMH RDL LITPOS SQPL SQPH LPPL LPPH SQPB LPPB SQPLPP LITLPP STK LOS SPR OFFB OFFSQ OFFLPP OFFLIT MI
         -> -> -> -> -> -> -> ->.
  pose proof STK as (LO0 & _ & _).
  eapply (xe_main ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1); try eassumption.
  unfold xe_hyps. repeat split; try eassumption; try lia.
Qed.
