(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl ImgFacts U_pow5_stmt U_shl_stmt U_pow10_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac post_call segs m ::=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      let W' := eval hnf in W in change (munch W' m m') in MUc;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Section Main.
  Hypothesis pow5_spec : pow5_stmt.
  Hypothesis shl_spec : shl_stmt.

  #[using="pow5_spec shl_spec"] Lemma pow10_spec : pow10_stmt.
  Proof. LiaFast.lf_pins (fun (pow5_spec shl_spec : LiaFast.U) => LiaFast.u0).
    unfold pow10_stmt. intros until len. intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 A0p NORM He CAP SEP.
    pose proof (munch_refl (pow10_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
    cbv delta [pow10_W] in MU.
    pose proof (wmono_refl USEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a1) as Re. unfold bv_modulus in Re.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    pose proof (u64arr_outside_rodata_U m _ _ PR LIMBS ltac:(rewrite L62; lia)) as AROD. rewrite L62 in AROD.
    pose proof (rw_cells_outside_rodata_U m _ _ PR LENC ltac:(cbn; lia)) as CROD. cbn [cells_size csize Nat.add] in CROD.
    assert (HA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 498 <= 2 ^ 64)%Z) by lia.
    assert (AROD' : (bv_unsigned a0 + 498 <= 0x10000 \/ 0x22000 <= bv_unsigned a0)%Z) by lia.
    clear Bl Bc AROD CROD. rename AROD' into AROD.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    assert (CAP5 : (bval ws (Z.to_nat len) * 5 ^ bv_unsigned a1 < BIG_CAP)%Z).
    { rewrite pow10_split in CAP by lia. pose proof (Z.pow_pos_nonneg 2 (bv_unsigned a1) ltac:(lia) ltac:(lia)).
      pose proof (Z.pow_nonneg 5 (bv_unsigned a1) ltac:(lia)). nia. }
    carve_frame 32%nat ST.
    do 4 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    call pow5_spec.
    1:{ rewrite ULs. replace (bv_unsigned sp + -32 - 1296)%Z with (bv_unsigned sp - 1328)%Z by lia. exact ST. }
    1:{ rewrite ULs. Z.div_mod_to_equations. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PR. } 1:{ exact LIMBS. } 1:{ exact L62. } 1:{ exact LENC. } 1:{ exact Hlen. } 1:{ exact A8. } 1:{ exact A0p. } 1:{ exact NORM. }
    1:{ lia. } 1:{ exact CAP5. }
    1:{ rewrite ULs. lia. }
    rewrite ?ULs in *.
    match goal with H : u64arr USEGS _ (bv_unsigned a0) ?w |- _ => rename H into XA5; rename w into ws5 end.
    match goal with H : rw_cells USEGS _ (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 ?l)] |- _ => rename H into LENC5; rename l into len5 end.
    match goal with H : bval ws5 _ = _ |- _ => rename H into VAL5 end.
    match goal with H : bnorm ws5 _ |- _ => rename H into BN5 end.
    match goal with H : stk USEGS _ _ _ |- _ => rename H into ST5 end.
    step. (* [comment removed for export] *)
    if_not_taken.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite ?shl32_shr32m, ?shl32_shr32 by lia.
    try rewrite (Z.mod_small (bv_unsigned a1) 4294967296) by lia. rewrite ?(Z_to_bv_bv_unsigned a1).
    step. (* [comment removed for export] *)
    do 4 step. (* [comment removed for export] *)
    replace (bv_unsigned sp + -32 - 1296)%Z with (bv_unsigned sp - 1328)%Z in ST5 by lia.
    release_frame FR ST5 (bv_unsigned sp).
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct (stk_split USEGS _ _ (bv_unsigned sp - 144) _ ST5 ltac:(lia)) as [STlo SThi].
    clear ST5.
    name_mem m5.
    call shl_spec.
    1:{ exact SThi. } 1:{ exact AL. } 1:{ exact XA5. } 1:{ assumption. } 1:{ exact LENC5. } 1:{ lia. } 1:{ exact A8. } 1:{ exact A0p. } 1:{ lia. }
    match goal with H : bnorm ws5 _ -> _ |- _ => rename H into COND end.
    destruct (COND BN5) as (Hb & VAL' & BN').
    { rewrite VAL5. rewrite <- Z.mul_assoc, <- pow10_split by lia. exact CAP. }
    { lia. }
    subst.
    match goal with H : stk USEGS _ (bv_unsigned sp - 144) _ |- _ => rename H into SThi' end.
    pose proof (stk_merge USEGS _ _ _ _ STlo SThi' ltac:(lia)) as STall.
    unfold pow10_post. finish.
    all: try eassumption. all: try lia.
    rewrite VAL', VAL5. rewrite <- Z.mul_assoc, <- pow10_split by lia. reflexivity.
  Qed.
End Main.
