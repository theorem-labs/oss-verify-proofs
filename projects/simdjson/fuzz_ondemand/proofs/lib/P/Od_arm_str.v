(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_defs Od_pstr_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section ArmStr.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis HPSTR : pstr_stmt_g psegs OD_PSTR OD_GTOP.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Theorem od_arm_string : arm_stmt E 0x27870.
  Proof using OK HPSTR.
    unfold arm_stmt. intros Q st xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1 HLAST HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    pose proof (tokB_read m1 E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2.
    fold (tokT bs idxs (o_pos st)) in RD2.
    pose proof (tokT_string bs idxs S1 (o_pos st) ltac:(lia)) as TS.
    destruct HB as [SB0 SB1]. rewrite Z.min_l in SB1 by lia.
    set (c := tokT bs idxs (o_pos st)) in *. set (off := tokI bs idxs (o_pos st)) in *.
    zstep. if_false.
    zstep. zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.
    zstep. zstep. odnorm. zstep. zstep. odnorm. zstep. zstep.
    if_cases K; zify_cond K.
    - apply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    - destruct (TS ltac:(unfold C_QUOTE; lia)) as (j & CLO & JR & JN).
      zstep. zstep. zstep. zstep.
      rewrite HA in *. rewrite VPT in DPI.
      zstep. zstep. zstep. zstep.
      zstep. zstep. zstep.
      zstep.
      replace (ret_pc (Z_to_bv 64 OD_PSTR)) with (Z_to_bv 64 OD_PSTR) by (symmetry; apply ret_pc_even; [unfold OD_PSTR; lia| reflexivity]).
      pose proof HPSTR as HS. unfold pstr_stmt_g in HS.
      eapply evt_cut.
      { eapply HS with (BUF := o_BUF E) (SB := o_SB E) (CAP := o_CAP E) (i := off) (j := j) (sbo := o_sbo st) (lo := o_lo E) (bs := bs);
          rewrite ?unsigned_lit by lia; unfold PSTR_FRAME, OD_GTOP;
          [ eassumption | eassumption | lia | lia | exact BOK | eassumption | lia | exact CLO | eassumption | lia | lia | lia | lia ]. }
      cbv beta. intros ms' P. unfold pstr_post_g in P.
      destruct P as (q5 & q6 & q7 & rr & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & -> & RES & MUc & WMc & MIc & SBWc & STc).
      rewrite !unsigned_lit in MUc, STc by lia. unfold PSTR_FRAME in MUc.
      transport_after_call psegs m0 m3 MUc WMc.
      clear MUc WMc HS. clear MI. clear RD1 RD2.
      replace (ret_pc (Z_to_bv 64 163716)) with (Z_to_bv 64 163716) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zstep. zstep. zstep.
      if_cases K3; zify_cond K3.
      +
        apply (HK (consume 1 st)); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar.
      + destruct RES as [R0|(sbo' & Rr & RB)]; [exfalso; subst rr; unfold wz in K3; rewrite unsigned_lit in K3 by lia; lia|].
        subst rr. unfold wz.
        zstep. zstep.
        apply (HK (mkO (o_pos st + 1) 1 (o_err st) (o_alive st) sbo')); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH).
        apply (acc_string bs idxs 1 st j sbo'); [unfold C_QUOTE; fold c; lia| exact CLO| fold off; lia].
  Qed.
End ArmStr.
