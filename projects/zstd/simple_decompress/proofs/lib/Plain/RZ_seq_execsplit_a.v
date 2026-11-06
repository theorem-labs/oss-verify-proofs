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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memmove RZ_seq_iface RZ_seq_safecopy RZ_seq_execend_a.
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
    (w0 w8 w16 w24 w32 : word) (lpv : Z) (m1 : fmem) : Prop :=
  stk psegs m1 B0 B1 /\ stk psegs m1 lo (SPV + -144)
  /\ rw_cells psegs m1 (SPV + -144)
        [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ rw_cells psegs m1 SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)]
  /\ rw_cells psegs m1 LPP [C8 (Z_to_bv 64 lpv)]
  /\ mem_inv psegs m1 /\ munch [(OP, OEND); (LPP, LPP + 8); (SPV - 208, SPV)] m m1 /\ wmono psegs m m1.
Ltac open_xs I := destruct I as (REG & STK & FR & SQC & LPC & MI & MU & WM).
Ltac close_xs := split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                 split; [eassumption|]; split; [eassumption|]; split; eassumption.

Tactic Notation "useS" uconstr(L) :=
  eapply L;
  try (lazymatch goal with
       | |- xs_hyps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eassumption
       | |- rdbl _ _ _ _ => eassumption
       | |- XS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => first [ eassumption | close_xs ]
       end);
  try (lazymatch goal with |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [ reflexivity | f_equal; lia ] end); try lia.

Section A.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z).
  Hypothesis HY : xs_hyps SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1.
  Notation POST := (zd_execend_post 208 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP OEND SQP LPP LP LLIM LL ML OFS B0 B1 lo m).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -144)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation XSm := (XS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo OP OEND SQP LPP LL ML OFS B0 B1).
  (* [comment removed for export] *)
  Notation STL pc mm xra x5 x6 x7 xs1 xa0 xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (ST pc mm xra x5 x6 x7 (Z_to_bv 64 (OP + LL)) xs1 xa0 xa1 (Z_to_bv 64 OENDW) (Z_to_bv 64 SQP) (Z_to_bv 64 LPP) xa5 (Z_to_bv 64 PFX) (Z_to_bv 64 PFX)
        xs2 xs3 (Z_to_bv 64 (ML + LL)) (Z_to_bv 64 OFS) (Z_to_bv 64 (LP + LL)) (Z_to_bv 64 LL) xs8 xs9 xs10 xs11 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma xs_ret : forall m1 (r lpv : Z) w0 w8 w16 w24 w32 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    XSm w0 w8 w16 w24 w32 lpv m1 -> 0 <= r < 2^64 ->
    (zd_is_error r = true \/ (r = LL + ML /\ OP + r <= OEND /\ lpv = LP + LL /\ LP + LL <= LLIM)) ->
    xa1 = Z_to_bv 64 r ->
    evt psegs POST (ST 0x1c8f0 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I HR HRES ->. open_hs HY. open_xs I.
    zstep. do 13 zstep. zstep.
    release_frame FR STK SPV.
    zstep. finish2. all: first [ exact LPC | lia | exact HRES ].
  Qed.

  (* [comment removed for export] *)
  Lemma xs_match : forall m1 w0 w8 w16 w24 w32 xra x5 x6 x7 xs1 xa0 xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    XSm w0 w8 w16 w24 w32 LP m1 -> LL + ML <= OEND - OP -> LL <= LLIM - LP ->
    evt psegs POST (STL 0x1c868 m1 xra x5 x6 x7 xs1 xa0 xa1 xa5 xs2 xs3 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I HSZ HLIT. open_hs HY. open_xs I.
    zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      destruct (stk_split psegs m0 B0 OEND B1 REG ltac:(lia)) as [REGa REGb]. clear REG.
      pose proof zd_safecopy_proof as SC. unfold zd_safecopy_stmt, PZD_SAFECOPY in SC.
      eapply evt_cut; [ eapply SC with (SPV := SPV + -144) (lo := lo) (OP := OP + LL) (OENDW := OENDW) (IP := OP + LL - OFS) (LEN := ML) (B0 := B0) (B1 := OEND);
        [ exact REGa | lia | lia | lia | lia | lia | lia | lia | exact STK | lia | lia | unfold off_stack; lia | exact MI
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]
        | clear SC; post_call psegs m0 ].
      lazymatch goal with H : stk psegs _ B0 OEND |- _ => rename H into REGa' end.
      lazymatch goal with H : stk psegs _ lo (SPV + -144) |- _ => rename H into STK end.
      pose proof (stk_merge psegs _ B0 OEND B1 REGa' REGb ltac:(lia)) as REG. clear REGa' REGb.
      zstep.
      eapply (xs_ret _ (LL + ML) (LP + LL)); [ close_xs | lia | right; lia | f_equal; lia ].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      eapply (xs_ret _ (2^64 - 20) (LP + LL)); [ close_xs | lia | left; reflexivity | apply bv_eq; reflexivity ].
  Qed.
End A.
