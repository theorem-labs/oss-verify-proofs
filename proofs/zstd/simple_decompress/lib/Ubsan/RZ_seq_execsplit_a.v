(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac MemRange ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import ZdFrame ZdDCtx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memmove RZ_seq_iface RZ_seq_safecopy seqL3_kit_dbs RZ_seq_execend_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition xs_hyps (SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1 : Z) : Prop :=
  4096 <= B0 /\ B1 < 2^47 /\ B0 <= PFX <= OP /\ OP <= OEND <= B1 /\ 0 <= OENDW /\ OENDW + 32 <= OEND
  /\ 0 <= LL < 2^32 /\ 0 <= ML < 2^32 /\ 0 <= OFS < 2^64
  /\ 4096 <= LP <= LLIM /\ LLIM < 2^47
  /\ (4096 <= SQP /\ SQP + 24 < 2^47) /\ (4096 <= LPP /\ LPP + 8 < 2^47)
  /\ (SQP + 24 <= B0 \/ B0 + (B1 - B0) <= SQP) /\ (LPP + 8 <= B0 \/ B0 + (B1 - B0) <= LPP)
  /\ (SQP + 24 <= LPP \/ LPP + 8 <= SQP) /\ (LP + (LLIM - LP) <= LPP \/ LPP + 8 <= LP)
  /\ lo <= SPV - 208 /\ 0 <= lo /\ 0 <= SPV < 2^47
  /\ (B0 + (B1 - B0) <= lo \/ SPV <= B0) /\ (SQP + 24 <= lo \/ SPV <= SQP) /\ (LPP + 8 <= lo \/ SPV <= LPP)
  /\ (LP + (LLIM - LP) <= lo \/ SPV <= LP).
Ltac open_hs HY := pose proof HY as (B0L & B1H & PFXR & OENDR & OW0 & OWH & LLR & MLR & OFSR & LPR & LLIMH & SQPR & LPPR & SQPB & LPPB & SQPLPP
                                     & LITLPP & LOS & LO0 & SPR & OFFB & OFFSQ & OFFLPP & OFFLIT).

(* [comment removed for export] *)
Definition XS (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : fmem) (SPV lo OP OEND SQP LPP LL ML OFS B0 B1 : Z)
    (lpv : Z) (m1 : fmem) : Prop :=
  stk usegs m1 B0 B1 /\ stk usegs m1 lo (SPV + -96)
  /\ (exists j0, rw_cells usegs m1 (SPV + -96)
        [CB 8 j0; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
  /\ rw_cells usegs m1 SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)]
  /\ rw_cells usegs m1 LPP [C8 (Z_to_bv 64 lpv)]
  /\ mem_inv usegs m1 /\ munch [(OP, OEND); (LPP, LPP + 8); (SPV - 208, SPV)] m m1 /\ wmono usegs m m1.
Ltac open_xs I := destruct I as (REG & STK & (j0 & FR) & SQC & LPC & MI & MU & WM).
Ltac close_xs := split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|];
                 split; [eassumption|]; split; [eassumption|]; split; eassumption.

Tactic Notation "useS" uconstr(L) :=
  eapply L;
  try (lazymatch goal with
       | |- xs_hyps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eassumption
       | |- rdbl _ _ _ _ => eassumption
       | |- XS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => first [ eassumption | close_xs ]
       end);
  try (lazymatch goal with |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [ reflexivity | f_equal; lia ] end); try lia.

Section A.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z).
  Hypothesis HY : xs_hyps SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1.
  Notation POST := (zd_execend_post 208 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP OEND SQP LPP LP LLIM LL ML OFS B0 B1 lo m).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -96)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation XSm := (XS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo OP OEND SQP LPP LL ML OFS B0 B1).
  (* [comment removed for export] *)
  Notation STL pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 x28 x29 x30 x31 :=
    (ST pc mm xra x5 x6 x7 (Z_to_bv 64 (OP + LL)) (Z_to_bv 64 OENDW) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        xs2 (Z_to_bv 64 (ML + LL)) (Z_to_bv 64 (LP + LL)) xs5 (Z_to_bv 64 PFX) (Z_to_bv 64 PFX)
        (Z_to_bv 64 SQP) (Z_to_bv 64 LPP) s10 s11 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma xs_ret : forall m1 (r lpv : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    XSm lpv m1 -> 0 <= r < 2^64 ->
    (zd_is_error r = true \/ (r = LL + ML /\ OP + r <= OEND /\ lpv = LP + LL /\ LP + LL <= LLIM)) ->
    x6 = Z_to_bv 64 r ->
    evt usegs POST (ST 0x1e6f4 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 s10 s11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I HR HRES ->. open_hs HY. open_xs I.
    zstep. do 11 zstep. zstep.
    release_frame FR STK SPV.
    zstep. finish2. all: first [ exact LPC | lia | exact HRES ].
  Qed.

  (* [comment removed for export] *)
  Lemma xs_match : forall m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 x28 x29 x30 x31,
    XSm LP m1 -> LL + ML <= OEND - OP -> LL <= LLIM - LP -> xs2 = Z_to_bv 64 (OP + LL - OFS) ->
    evt usegs POST (STL 0x1e674 m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I HSZ HLIT ->. open_hs HY. open_xs I.
    zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      pose proof (rdbl_of_stk usegs _ _ _ REG) as RB.
      pose proof zd_safecopy_proof as SC. unfold zd_safecopy_stmt, PZD_SAFECOPY in SC.
      eapply evt_cut; [ eapply SC with (SPV := SPV + -96) (lo := lo) (OP := OP + LL) (OENDW := OENDW) (IP := OP + LL - OFS) (LEN := ML) (OV := 1)
                                       (B0 := B0) (B1 := B1) (R0 := B0) (R1 := B1);
        [ exact REG | lia | lia | lia | lia | lia | lia | lia | exact RB | lia | lia | lia | left; repeat split; lia
        | exact STK | lia | lia | unfold off_stack; lia | unfold off_stack; lia | exact MI
        | first [ reflexivity | apply bv_eq; reflexivity | f_equal; lia ] .. ]
        | clear SC REG STK RB; post_call usegs m0 ].
      lazymatch goal with H : stk usegs _ B0 B1 |- _ => rename H into REG end.
      lazymatch goal with H : stk usegs _ lo (SPV + -96) |- _ => rename H into STK end.
      zstep.
      eapply (xs_ret _ (LL + ML) (LP + LL)); [ close_xs | lia | right; lia | f_equal; lia ].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      eapply (xs_ret _ (2^64 - 20) (LP + LL)); [ close_xs | lia | left; reflexivity | apply bv_eq; reflexivity ].
  Qed.

  Lemma xs_lit : forall m1 xra x6 x7 xs0 xs1 xs2 xs5 xs6 xs7 xs8 xs9 x29 x30 x31,
    XSm LP m1 -> rdbl usegs m1 LP LLIM -> LL + ML <= OEND - OP -> LL <= LLIM - LP ->
    evt usegs POST (ST 0x1e64c m1 xra (Z_to_bv 64 LL) x6 x7 xs0 xs1 (Z_to_bv 64 OP) (Z_to_bv 64 LP) (Z_to_bv 64 OENDW) (Z_to_bv 64 SQP)
                       (Z_to_bv 64 LPP) (Z_to_bv 64 OFS) (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) xs2 (Z_to_bv 64 (ML + LL)) (Z_to_bv 64 (LP + LL))
                       xs5 xs6 xs7 xs8 xs9 s10 s11 (Z_to_bv 64 DEND) x29 x30 x31).
  Proof.
    intros until x31. intros I RDL HSZ HLIT. open_hs HY. open_xs I.
    do 10 zstep.
    pose proof zd_safecopy_dbs_proof as SC. unfold zd_safecopy_dbs_stmt, PZD_SAFECOPY_DBS in SC.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply SC with (SPV := SPV + -96) (lo := lo) (OP := OP) (IP := LP) (LEN := LL)
                                       (B0 := B0) (B1 := B1) (R0 := LP) (R1 := LLIM);
        [ exact REG | lia | lia | lia | lia | lia | exact RDL | lia | lia | lia | lia
        | exact STK | lia | lia | unfold off_stack; lia | unfold off_stack; lia | exact MI
        | first [ reflexivity | apply bv_eq; reflexivity | f_equal; lia ] .. ]
        | clear SC REG STK RDL; post_call usegs mm ] end.
    lazymatch goal with H : stk usegs _ B0 B1 |- _ => rename H into REG end.
    lazymatch goal with H : stk usegs _ lo (SPV + -96) |- _ => rename H into STK end.
    eapply xs_match; [ close_xs | lia | lia | first [ reflexivity | f_equal; lia ] ].
  Qed.
End A.
