(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C5_stmt ECH_C12_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Definition ctype_at (c : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 CTYPE_MASK_alnum ->
      stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CTYPE_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (ctype_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (if is_alnumZ c then 1 else 0) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ossl_ctype_check) fc None m (seg_rom rsegs)).

  Local Ltac ctype_prologue :=
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo A0 A1 ST LO MI RAE; subst a0 a1;
    unfold P_ossl_ctype_check, CTYPE_STACK, FR_ossl_ctype_check, CTYPE_MASK_alnum in *;
    pose proof (word_range sp) as SPR; pose proof (word_range ra) as RAR;
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption);
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU; pose proof (wmono_refl rsegs m) as WM.

  (* [comment removed for export] *)
  Lemma ctype_hi : forall c, 128 <= c < 256 -> ctype_at c.
  Proof.
    intros c Hc. unfold ctype_at. ctype_prologue.
    replace (is_alnumZ c) with false by (unfold is_alnumZ; destruct (48 <=? c) eqn:?; destruct (c <=? 57) eqn:?; destruct (65 <=? c) eqn:?;
       destruct (c <=? 90) eqn:?; destruct (97 <=? c) eqn:?; destruct (c <=? 122) eqn:?; cbn; try reflexivity; exfalso; lia).
    carve_frame 16%nat ST.
    do 4 st1. step. step. if_cases K0; zify_cond K0; [| kill K0]; clear K0.
    step. do 4 step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Local Ltac ctype_one :=
    lazymatch goal with |- ctype_at ?c => let v := eval vm_compute in c in change (ctype_at c) with (ctype_at v) end;
    unfold ctype_at; ctype_prologue;
    let ST0 := match goal with H : stk _ _ _ _ |- _ => H end in
    carve_frame 16%nat ST0;
    do 4 st1; step; step; try if_false; step; step; step; step; st1; step; step; step; do 4 step;
    let FR := match goal with H : rw_cells _ _ _ [C8 _; C8 _] |- _ => H end in
    let ST1 := match goal with H : stk _ _ _ _ |- _ => H end in
    lazymatch type of FR with rw_cells _ _ (bv_unsigned ?spv + _) _ =>
      release_frame FR ST1 (bv_unsigned spv) end;
    finish.

  Lemma ctype_lo : forall n, (n < 128)%nat -> ctype_at (Z.of_nat n).
  Proof.
    intros n Hn.
    do 128 (destruct n as [|n]; [ctype_one|]).
    exfalso. lia.
  Qed.

  Lemma ctype_alnum_spec : ctype_alnum_stmt.
  Proof.
    unfold ctype_alnum_stmt. intros until lo. intros A0 A1 CR.
    destruct (Z_lt_le_dec c 128) as [L|L].
    - rewrite <- (Z2Nat.id c) in A0 |- * by lia.
      revert A0 A1. apply (ctype_lo (Z.to_nat c)). lia.
    - revert A0 A1. apply (ctype_hi c). lia.
  Qed.
End S.
