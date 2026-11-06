(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_defs Od_tables.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma snez_lxor_eq : forall c, Z.b2z (0 <? Z.lxor c c) = 0%Z.
Proof. intros c. rewrite Z.lxor_nilpotent. reflexivity. Qed.
Lemma snez_lxor_ne : forall x c, (0 <= x)%Z -> (0 <= c)%Z -> x <> c -> Z.b2z (0 <? Z.lxor x c) = 1%Z.
Proof.
  intros x c Hx Hc Hne.
  assert (H0 : (0 <= Z.lxor x c)%Z) by (apply Z.lxor_nonneg; split; intros; assumption).
  assert (H1 : Z.lxor x c <> 0%Z) by (intros H; apply Z.lxor_eq in H; contradiction).
  destruct (Z.ltb_spec 0 (Z.lxor x c)); [reflexivity| lia].
Qed.

Section ArmLit.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Theorem od_arm_bool : arm_stmt E 0x27898.
  Proof using OK.
    unfold arm_stmt. intros Q st xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1 HLAST HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0. pose proof (od_B_range E BOK (off + 1)) as R1.
    pose proof (od_B_range E BOK (off + 2)) as R2. pose proof (od_B_range E BOK (off + 3)) as R3.
    pose proof (od_B_range E BOK (off + 4)) as R4. pose proof (od_B_range E BOK (off + 5)) as R5.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    pose proof (tokB_read m1 E (off + 1) BUFRO ltac:(lia)) as RB1.
    pose proof (tokB_read m1 E (off + 2) BUFRO ltac:(lia)) as RB2.
    pose proof (tokB_read m1 E (off + 3) BUFRO ltac:(lia)) as RB3.
    pose proof (tokB_read m1 E (off + 4) BUFRO ltac:(lia)) as RB4.
    pose proof (tokB_read m1 E (off + 5) BUFRO ltac:(lia)) as RB5.
    set (b0 := B bs off) in *. set (b1 := B bs (off + 1)) in *. set (b2 := B bs (off + 2)) in *.
    set (b3 := B bs (off + 3)) in *. set (b4 := B bs (off + 4)) in *. set (b5 := B bs (off + 5)) in *.
    zstep. if_false.
    zstep. odnorm. zstep. zstep. zstep. zstep. odnorm. zstep. odnorm. zstep. odnorm. zstep. odnorm.
    zstep. zstep. zstep. zstep. zstep. zstep.
    repeat match goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let w := fresh "w" in set (w := Z_to_bv 64 (Z.lor x y)) in *; clearbody w end.
    repeat match goal with |- context [Z_to_bv 64 (Z.shiftl ?x ?y)] => let w := fresh "v" in set (w := Z_to_bv 64 (Z.shiftl x y)) in *; clearbody w end.
    pose proof (bv_unsigned_in_range 64 w) as WR. unfold bv_modulus in WR. cbn in WR.
    pose proof (osown_read m1 b4 MI ltac:(lia)) as RT4. pose proof (osown_read m1 b5 MI ltac:(lia)) as RT5.
    pose proof (osown_range b4) as RS4. pose proof (osown_range b5) as RS5.
    unfold OT_SOWN in RT4, RT5.
    zstep. zstep.
    if_cases K; zify_cond K.
    -
      zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.
      zstep. zstep. zstep. rewrite K, snez_lxor_eq.
      zstep. zstep. zstep. odnorm. zstep. zstep. zstep. odnorm. zstep.
      if_cases K3; zify_cond K3.
      + zstep. zstep. zstep. zstep.
        apply (HK (consume 1 st)); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar.
      + zstep.
        apply (HK st); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    -
      zstep. odnorm. zstep. zstep. zstep. zstep. zstep.
      if_cases K2; zify_cond K2.
      + apply (HK st); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
      + zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.
        zstep. zstep. zstep. rewrite (snez_lxor_ne (bv_unsigned w) 1702195828 ltac:(lia) ltac:(lia) K).
        zstep. zstep. zstep. odnorm. zstep. zstep. zstep. odnorm. zstep.
        if_cases K3; zify_cond K3.
        * zstep. zstep. zstep. zstep.
          apply (HK (consume 1 st)); [| exact FRM| od_close_inv].
          apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar.
        * zstep.
          apply (HK st); [| exact FRM| od_close_inv].
          apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
  Qed.

  Lemma od_null_join : forall (Q : machine_state -> Prop) st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    evt psegs Q (ODST E 0x27ae4 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).
  Proof using OK.
    intros Q st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1 HLAST HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.
    zstep. zstep.
    if_cases K; zify_cond K.
    - apply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    - zstep. zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.
      zstep. zstep.
      if_cases K2; zify_cond K2.
      + apply (HK st); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
      + zstep. zstep. zstep. zstep. zstep.
        apply (HK (consume 1 st)); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar.
  Qed.

  Lemma od_null_tail : forall (Q : machine_state -> Prop) st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    evt psegs Q (ODST E 0x27acc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).
  Proof using OK.
    intros Q st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1 HLAST HH FRM INV HK.
    assert (INV2 := INV). od_open_inv INV. od_env OK.
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply evt_eq; [| eapply (od_null_join Q st); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK]].
    od_st_eq.
  Qed.

  Theorem od_arm_null : arm_stmt E 0x27a04.
  Proof using OK.
    unfold arm_stmt. intros Q st xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1 HLAST HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (INV2 := INV). od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0. pose proof (od_B_range E BOK (off + 1)) as R1.
    pose proof (od_B_range E BOK (off + 2)) as R2. pose proof (od_B_range E BOK (off + 3)) as R3.
    pose proof (od_B_range E BOK (off + 4)) as R4.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    pose proof (tokB_read m1 E (off + 1) BUFRO ltac:(lia)) as RB1.
    pose proof (tokB_read m1 E (off + 2) BUFRO ltac:(lia)) as RB2.
    pose proof (tokB_read m1 E (off + 3) BUFRO ltac:(lia)) as RB3.
    pose proof (tokB_read m1 E (off + 4) BUFRO ltac:(lia)) as RB4.
    set (b0 := B bs off) in *. set (b1 := B bs (off + 1)) in *. set (b2 := B bs (off + 2)) in *.
    set (b3 := B bs (off + 3)) in *. set (b4 := B bs (off + 4)) in *.
    pose proof (osow_read m1 b4 MI ltac:(lia)) as RT4. unfold OT_SOW in RT4.
    zstep. if_false.
    zstep. zstep. odnorm. zstep. zstep. odnorm. zstep. odnorm. zstep. odnorm. zstep. odnorm.
    zstep. zstep. zstep. zstep. zstep. zstep.
    repeat match goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let w := fresh "w" in set (w := Z_to_bv 64 (Z.lor x y)) in *; clearbody w end.
    repeat match goal with |- context [Z_to_bv 64 (Z.shiftl ?x ?y)] => let w := fresh "v" in set (w := Z_to_bv 64 (Z.shiftl x y)) in *; clearbody w end.
    zstep. zstep.
    if_cases K; zify_cond K.
    -
      eapply evt_eq; [| eapply (od_null_tail Q st); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK]].
      od_st_eq.
    - zstep. odnorm. zstep. zstep. zstep. zstep. odnorm. zstep.
      if_cases K2; zify_cond K2.
      + eapply evt_eq; [| eapply (od_null_tail Q st); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK]].
        od_st_eq.
      + zstep. zstep.
        eapply evt_eq; [| eapply (od_null_join Q st); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK]].
        od_st_eq.
  Qed.
End ArmLit.
