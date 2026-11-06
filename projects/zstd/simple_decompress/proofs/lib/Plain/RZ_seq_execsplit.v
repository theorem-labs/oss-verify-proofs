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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memmove RZ_seq_iface RZ_seq_safecopy RZ_seq_execend_a RZ_seq_execsplit_a.
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

Tactic Notation "useX" uconstr(L) :=
  eapply L; [ first [ eassumption | close_xs | idtac ] | first [ eassumption | close_xs | idtac ] | .. ];
  try eassumption; try (f_equal; lia); try lia.

Section B.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z).
  Hypothesis HY : xs_hyps SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1.
  Hypothesis HSZ : LL + ML <= OEND - OP.
  Hypothesis HLIT : LL <= LLIM - LP.
  Notation POST := (zd_execend_post 208 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP OEND SQP LPP LP LLIM LL ML OFS B0 B1 lo m).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -144)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation XSm := (XS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo OP OEND SQP LPP LL ML OFS B0 B1).
  Notation STL pc mm xra x5 x6 x7 xs1 xa0 xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (ST pc mm xra x5 x6 x7 (Z_to_bv 64 (OP + LL)) xs1 xa0 xa1 (Z_to_bv 64 OENDW) (Z_to_bv 64 SQP) (Z_to_bv 64 LPP) xa5 (Z_to_bv 64 PFX) (Z_to_bv 64 PFX)
        xs2 xs3 (Z_to_bv 64 (ML + LL)) (Z_to_bv 64 OFS) (Z_to_bv 64 (LP + LL)) (Z_to_bv 64 LL) xs8 xs9 xs10 xs11 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma xs_short_loop : forall (k : nat) m1 w0 w8 w16 w24 w32 (op lp : Z) xra x5 x6 x7 xs1 xa0 xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    XSm w0 w8 w16 w24 w32 LP m1 -> rdbl psegs m1 LP LLIM -> OP <= op -> LP <= lp -> lp - LP = op - OP -> op + Z.of_nat k + 1 = OP + LL ->
    xa0 = Z_to_bv 64 op -> xs1 = Z_to_bv 64 lp ->
    evt psegs POST (STL 0x1c824 m1 xra x5 x6 x7 xs1 xa0 xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I RDL HOP HLP HREL HK -> ->; open_hs HY; open_xs I.
    - ldl RDL lp 1%nat. zstep. zstep. strx REG RDL op 1%nat. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. useX xs_match.
    - ldl RDL lp 1%nat. zstep. zstep. strx REG RDL op 1%nat. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      useX (IH _ w0 w8 w16 w24 w32 (op + 1) (lp + 1)).
  Qed.

  (* [comment removed for export] *)
  Lemma xs_tail_loop : forall (k : nat) m1 w0 w8 w16 w24 w32 (op lp : Z) xra x5 x6 x7 xs1 xa0 xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    XSm w0 w8 w16 w24 w32 LP m1 -> rdbl psegs m1 LP LLIM -> OP <= op -> LP <= lp -> lp - LP = op - OP -> op + Z.of_nat k + 1 = OP + LL ->
    xs8 = Z_to_bv 64 op -> xs1 = Z_to_bv 64 lp -> xa0 = Z_to_bv 64 (Z.of_nat k + 1) ->
    evt psegs POST (STL 0x1c84c m1 xra x5 x6 x7 xs1 xa0 xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I RDL HOP HLP HREL HK -> -> ->; open_hs HY; open_xs I.
    - ldl RDL lp 1%nat. zstep. zstep. zstep. strx REG RDL op 1%nat. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      useX xs_match.
    - ldl RDL lp 1%nat. zstep. zstep. zstep. strx REG RDL op 1%nat. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      useX (IH _ w0 w8 w16 w24 w32 (op + 1) (lp + 1)).
  Qed.

  (* [comment removed for export] *)
  Lemma xs_tail : forall m1 w0 w8 w16 w24 w32 (op lp : Z) xra x5 x6 x7 xs1 xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    XSm w0 w8 w16 w24 w32 LP m1 -> rdbl psegs m1 LP LLIM -> OP <= op < OP + LL -> LP <= lp -> lp - LP = op - OP ->
    xs8 = Z_to_bv 64 op -> xs1 = Z_to_bv 64 lp ->
    evt psegs POST (STL 0x1c844 m1 xra x5 x6 x7 xs1 (Z_to_bv 64 OP) xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RDL HOP HLP HREL -> ->. open_hs HY.
    zstep. zstep.
    useX (xs_tail_loop (Z.to_nat (OP + LL - op - 1)) _ w0 w8 w16 w24 w32 op lp).
  Qed.

  (* [comment removed for export] *)
  Notation STW pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs8 xs10 x28 x29 x30 x31 :=
    (ST pc mm xra x5 x6 x7 (Z_to_bv 64 (OP + LL)) (Z_to_bv 64 LP) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        xs2 xs3 (Z_to_bv 64 (ML + LL)) (Z_to_bv 64 OFS) (Z_to_bv 64 (LP + LL)) (Z_to_bv 64 LL) xs8 (Z_to_bv 64 OP) xs10 (Z_to_bv 64 OENDW) x28 x29 x30 x31).
  Notation XSW w16 := (XSm (Z_to_bv 64 PFX) (Z_to_bv 64 SQP) w16 (Z_to_bv 64 PFX) (Z_to_bv 64 LPP) LP).

  (* [comment removed for export] *)
  Lemma xs_w_exit : forall m1 w16 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs8 xs10 x28 x29 x30 x31,
    XSW w16 m1 -> rdbl psegs m1 LP LLIM -> 32 <= LL ->
    xs8 = Z_to_bv 64 (OP + LL - 32) -> xs10 = Z_to_bv 64 (LL - 32) ->
    evt psegs POST (STW 0x1c7fc m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs8 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RDL HLL -> ->. open_hs HY. open_xs I.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    useX (xs_tail _ _ _ _ _ _ (OP + LL - 32) (LP + LL - 32)).
  Qed.

  (* [comment removed for export] *)
  Lemma xs_w_loop : forall (q : nat) m1 w16 (d sr : Z) xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs8 xs10 x28 x29 x30 x31,
    XSW w16 m1 -> rdbl psegs m1 LP LLIM -> OP <= d < OP + LL - 32 -> sr - LP = d - OP ->
    OP + LL - 32 - d <= 32 * (Z.of_nat q + 1) ->
    xs2 = Z_to_bv 64 d -> xs3 = Z_to_bv 64 (sr + 16) -> xs8 = Z_to_bv 64 (OP + LL - 32) -> xs10 = Z_to_bv 64 (LL - 32) ->
    evt psegs POST (STW 0x1c7d0 m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs8 xs10 x28 x29 x30 x31).
  Proof.
    induction q as [|q IH]; intros until x31; intros I RDL HD HREL HQ -> -> -> ->; open_hs HY; open_xs I.
    - zstep. zstep. zstep. zstep. mmvl REG RDL d sr. zstep. zstep. zstep. zstep. mmvl REG RDL (d + 16) (sr + 16).
      zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|]. useX xs_w_exit.
    - zstep. zstep. zstep. zstep. mmvl REG RDL d sr. zstep. zstep. zstep. zstep. mmvl REG RDL (d + 16) (sr + 16).
      zstep. zstep. zstep. if_cases K; zify_cond K.
      + useX (IH _ w16 (d + 32) (sr + 32)).
      + useX xs_w_exit.
  Qed.

  (* [comment removed for export] *)
  Lemma xs_w : forall m1 w0 w8 w16 w24 w32 xra x5 x6 x7 xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    XSm w0 w8 w16 w24 w32 LP m1 -> rdbl psegs m1 LP LLIM -> 32 <= LL -> xs8 = Z_to_bv 64 (OP + LL - 32) ->
    evt psegs POST (STL 0x1c794 m1 xra x5 x6 x7 (Z_to_bv 64 LP) (Z_to_bv 64 OP) xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RDL HLL ->. open_hs HY. open_xs I.
    rdl_to_bytes RDL LB. zstep. zstep. zstep. zstep. zstep. bytes_to_rdl LB RDL.
    zstep. zstep. zstep. zstep. zstep. zstep. mmvl REG RDL OP LP.
    zstep. zstep. if_cases K; zify_cond K.
    - useX xs_w_exit.
    - zstep. zstep. useX (xs_w_loop (Z.to_nat LL) _ _ (OP + 16) (LP + 16)).
  Qed.
End B.

Tactic Notation "useD" uconstr(L) :=
  eapply L; try eassumption; try close_xs;
  try (lazymatch goal with |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [ reflexivity | f_equal; lia ] end); try lia.

Section D.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z).
  Hypothesis HY : xs_hyps SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1.
  Notation POST := (zd_execend_post 208 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP OEND SQP LPP LP LLIM LL ML OFS B0 B1 lo m).

  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -144)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation XSm := (XS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo OP OEND SQP LPP LL ML OFS B0 B1).


  (* [comment removed for export] *)
  Lemma xs_short : forall m1 w0 w8 w16 w24 w32 xra x5 x6 x7 xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    XSm w0 w8 w16 w24 w32 LP m1 -> rdbl psegs m1 LP LLIM -> LL + ML <= OEND - OP -> LL <= LLIM - LP ->
    evt psegs POST (ST 0x1c820 m1 xra x5 x6 x7 (Z_to_bv 64 (OP + LL)) (Z_to_bv 64 LP) (Z_to_bv 64 OP) xa1 (Z_to_bv 64 OENDW) (Z_to_bv 64 SQP) (Z_to_bv 64 LPP) xa5
                       (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) xs2 xs3 (Z_to_bv 64 (ML + LL)) (Z_to_bv 64 OFS) (Z_to_bv 64 (LP + LL)) (Z_to_bv 64 LL)
                       xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RDL HSZ HLIT. open_hs HY.
    zstep. if_cases K; zify_cond K.
    - useD xs_match.
    - useD (xs_short_loop ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1 HY HSZ HLIT (Z.to_nat (LL - 1))).
  Qed.

  (* [comment removed for export] *)
  Lemma xs_disp : forall m1 w0 w8 w16 w24 w32 xra x5 x6 x7 xs0 xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    XSm w0 w8 w16 w24 w32 LP m1 -> rdbl psegs m1 LP LLIM -> LL + ML <= OEND - OP -> LL <= LLIM - LP ->
    evt psegs POST (ST 0x1c76c m1 xra x5 x6 x7 xs0 (Z_to_bv 64 LP) (Z_to_bv 64 OP) xa1 (Z_to_bv 64 OENDW) (Z_to_bv 64 SQP) (Z_to_bv 64 LPP) xa5
                       (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) xs2 xs3 (Z_to_bv 64 (ML + LL)) (Z_to_bv 64 OFS) (Z_to_bv 64 (LP + LL)) (Z_to_bv 64 LL)
                       xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RDL HSZ HLIT. open_hs HY.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - useD xs_short.
    - zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + useD xs_short.
      + zstep. zstep. if_cases K2; zify_cond K2.
        * zstep.
          useD (xs_tail ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1 HY HSZ HLIT _ _ _ _ _ _ OP LP).
        * zstep. zstep. if_cases K3; zify_cond K3.
          -- zstep.
             useD (xs_tail ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1 HY HSZ HLIT _ _ _ _ _ _ OP LP).
          -- useD xs_w.
  Qed.

  (* [comment removed for export] *)
  Lemma xs_main : forall (t0 t1 t2 t4 t5 t6 : word),
    stk psegs m B0 B1 -> stk psegs m lo SPV -> mem_inv psegs m ->
    rw_cells psegs m SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)] ->
    rw_cells psegs m LPP [C8 (Z_to_bv 64 LP)] -> rdbl psegs m LP LLIM ->
    evt psegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OP) (Z_to_bv 64 OEND) (Z_to_bv 64 OENDW) (Z_to_bv 64 SQP) (Z_to_bv 64 LPP)
               (Z_to_bv 64 LLIM) (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 DEND) t4 t5 t6)
          F (Z_to_bv 64 0x1c6f8) fc None m (seg_rom psegs)).
  Proof.
    intros until t6. intros REG STK MI SQC LPC RDL. open_hs HY.
    assert (MU : munch [(OP, OEND); (LPP, LPP + 8); (SPV - 208, SPV)] m m) by apply munch_refl.
    assert (WM : wmono psegs m m) by apply wmono_refl.
    rdl_to_bytes RDL LB.
    zstep. carve_frame 144%nat STK.
    do 13 zstep.
    bytes_to_rdl LB RDL.
    lazymatch type of FR with rw_cells _ _ _ (CB 40 ?j :: ?post) =>
      apply (rw_cells_split_CB psegs _ _ [] 40 j post [8; 8; 8; 8; 8]%nat) in FR; [| reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [] j post FR) as [w0 FR0] end. cbn [app] in FR0. clear FR.
    lazymatch type of FR0 with rw_cells _ _ _ (?c0 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [c0] j post FR0) as [w8 FR1] end. cbn [app] in FR1. clear FR0.
    lazymatch type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [c0; c1] j post FR1) as [w16 FR2] end. cbn [app] in FR2. clear FR1.
    lazymatch type of FR2 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [c0; c1; c2] j post FR2) as [w24 FR3] end. cbn [app] in FR3. clear FR2.
    lazymatch type of FR3 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [c0; c1; c2; c3] j post FR3) as [w32 FR] end. cbn [app] in FR. clear FR3.
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      useD (xs_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1 HY _ (2^64 - 70) LP w0 w8 w16 w24 w32);
        [ left; reflexivity | apply bv_eq; reflexivity ].
    - zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + zstep. zstep. zstep. if_cases K2; zify_cond K2.
        * useD xs_disp.
        * zstep. if_cases K3; zify_cond K3.
          -- (* [comment removed for export] *)
             useD (xs_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1 HY _ (2^64 - 70) LP w0 w8 w16 w24 w32);
               [ left; reflexivity | apply bv_eq; reflexivity ].
          -- useD xs_disp.
      + (* [comment removed for export] *)
        zstep. zstep.
        useD (xs_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1 HY _ (2^64 - 20) LP w0 w8 w16 w24 w32);
          [ left; reflexivity | apply bv_eq; reflexivity ].
  Qed.
End D.

Theorem zd_execend_split_proof : zd_execend_split_stmt.
Proof.
  unfold zd_execend_split_stmt, PZD_EXECEND_SPLIT, apart, off_stack. intros until B1.
  intros REG B0L B1H PFXR OENDR OW0 OWH SQC LPC LLR MLR OFSR LPR LLIMH RDL LITPOS SQPL SQPH LPPL LPPH SQPB LPPB SQPLPP LITLPP STK LOS SPR OFFB OFFSQ OFFLPP OFFLIT MI
         -> -> -> -> -> -> -> -> ->.
  pose proof STK as (LO0 & _ & _).
  eapply (xs_main ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1); try eassumption.
  unfold xs_hyps. repeat split; try eassumption; try lia.
Qed.
