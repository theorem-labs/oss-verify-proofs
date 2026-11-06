(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB Od_arm_dbl_defsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_image | solve_load_base ].

Section ArmDblSlowB.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma dbl_slow : forall (Q : machine_state -> Prop) st neg q0 v4
      xra xt0 xt1 xt2 xa1 xa2 xa3 xa6 xa7 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 -> od_slow_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 ->
    evt bsegs Q (DBLST E 0x9b130 xra xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E + q0)) xa1 xa2 xa3 v4 (Z_to_bv 64 neg) xa6 xa7
                       (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros until m1; intros HH FRM INV HS PS SG.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0]. unfold dbl_sgn in SG.
    od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (bv_unsigned_in_range 64 v4) as RV4. unfold bv_modulus in RV4. cbn in RV4.
    set (off := tokI bs idxs (o_pos st)) in *.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    destruct (Z.eq_dec neg 0) as [N0|N1].
    - subst neg. specialize (SG eq_refl).
      ostep. ostep. ostep. dgok. ostep. ostep. ostep. ostep.
      if_cases KG; [| exfalso; zify_cond KG; apply Z.lor_eq_0_iff in KG; destruct KG as [K1 K2];
                      first [ match type of K2 with Z.b2z (?a <? ?b)%Z = _ => destruct (Z.ltb_spec a b); cbn in K2; lia end
                            | match type of K1 with Z.b2z (?a <? ?b)%Z = _ => destruct (Z.ltb_spec a b); cbn in K1; lia end ]]. clear KG.
      ostep. ostep.
      eapply evt_eq; [| eapply (HS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV)]. unfold OD_FROMCH. od_st_eq.
    - assert (neg = 1%Z) by lia. subst neg. clear SG.
      ostep. ostep. ostep. dgok. ostep. ostep. ostep. ostep.
      if_cases KG; [| exfalso; zify_cond KG; apply Z.lor_eq_0_iff in KG; destruct KG as [K1 K2];
                      first [ match type of K2 with Z.b2z (?a <? ?b)%Z = _ => destruct (Z.ltb_spec a b); cbn in K2; lia end
                            | match type of K1 with Z.b2z (?a <? ?b)%Z = _ => destruct (Z.ltb_spec a b); cbn in K1; lia end ]]. clear KG.
      ostep. ostep.
      eapply evt_eq; [| eapply (HS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV)]. unfold OD_FROMCH. od_st_eq.
  Qed.
End ArmDblSlowB.
