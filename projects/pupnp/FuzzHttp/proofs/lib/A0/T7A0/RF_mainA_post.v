(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS SeamA0 A0Prog AssembleA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Printf_lib F_printf_iface Stdio_iface F_printf_diag Exit RDriverA_kit RDriverA_ctx RDriverA_main RDriverA_exit RF_mainA_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import F_syscalls RDriverA_lib RDriverA_iface RF_mainA_B1 RF_mainA_B2 RF_mainA_B3 RF_mainA_B4 RF_mainA_C.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac zst := zstep; fix_lit_store.

Lemma swrap32_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32). Z.div_mod_to_equations. lia. Qed.

Section POST.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variables (sp0 : word) (S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATPA).

  Notation TST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 (-2)) S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 RSVA) (Z_to_bv 64 0) S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  #[using="VSP"] Lemma psp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0.
  Proof. destruct VSP as (A & B & C). unfold sp_window_lo, sp_window_hi in *. lia. Qed.

  #[using="Type"] Lemma post_to_emit : forall (Q : machine_state -> Prop) x1 t0 t1 t2 x8 x9 (rcw : word) a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x22 t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (v : bv 8),
    rw_cells asegs m 0x5e5f54 [C1 v] -> mem_inv asegs m ->
    (forall m', munch [(0x5e5f54, 0x5e5f55)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> rw_cells asegs m' 0x5e5f54 [C1 (Z_to_bv 8 0)] ->
       evt asegs Q (TST 0x864cc (Z_to_bv 64 0x86420) t0 t1 t2 x8 x9 rcw rcw a2 a3 a4 a5 a6 a7 x18 rcw (Z_to_bv 64 0x5e5f50) x21 x22 t3 t4 t5 t6 F fc m')) ->
    evt asegs Q (TST 0x86410 x1 t0 t1 t2 x8 x9 rcw a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 0x5e5f50) x21 x22 t3 t4 t5 t6 F fc m).
  Proof.
    intros until v. intros CB MI K.
    pose proof (munch_refl [(0x5e5f54, 0x5e5f55)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. zst. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => apply (K mx) end; assumption.
  Qed.

  #[using="Type"] Lemma emit_ret_next : forall (Q : machine_state -> Prop) (k rc : Z) (fl : bool) x1 t0 t1 t2 (x8 x9 : word) a0 a1 a2 a3 a4 a5 a6 a7 (x18 x20 : word) t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    1 <= k <= 4 -> 0 <= rc < 2^31 ->
    (1 < k -> evt asegs Q (TST 0x863fc x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 (rc - 1)) x20 (Z_to_bv 64 (k - 1))
                                (Z_to_bv 64 (Z.b2z (fl || (0 <? rc)))) t3 t4 t5 t6 F fc m)) ->
    (k = 1 -> evt asegs Q (TST 0x5862c (Z_to_bv 64 0x8643c) t0 t1 t2 x8 x9 x18 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 (rc - 1)) x20 (Z_to_bv 64 0)
                                (Z_to_bv 64 (Z.b2z (fl || (0 <? rc)))) t3 t4 t5 t6 F fc m)) ->
    evt asegs Q (TST 0x86420 x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 rc) x20 (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m).
  Proof.
    intros until m. intros Hk Hrc KN KF.
    Ltac emit_tail k KN KF K1 :=
      zstep; rewrite (swrap32_small (k + -1)) by lia; replace (k + -1) with (k - 1) by lia;
      zstep; if_cases K1; zify_cond K1;
      [ apply KN; rewrite ?unsigned_lit in K1 by lia; lia
      | replace (k - 1) with 0 by (rewrite ?unsigned_lit in K1 by lia; lia); zstep; zstep; apply KF; rewrite ?unsigned_lit in K1 by lia; lia ].
    destruct (Z.eq_dec rc 0) as [R0|RP].
    - subst rc. replace (fl || (0 <? 0)) with fl in KN, KF by (destruct fl; reflexivity).
      zstep. rewrite ?swrap32_small by lia.
      zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit_wrap in K0; try (exfalso; Z.div_mod_to_equations; lia). clear K0.
      emit_tail k KN KF K1.
    - replace (fl || (0 <? rc)) with true in KN, KF by (rewrite (proj2 (Z.ltb_lt 0 rc)) by lia; destruct fl; reflexivity).
      zstep. rewrite ?swrap32_small by lia.
      zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit_wrap in K0; try (exfalso; Z.div_mod_to_equations; lia). clear K0.
      zstep. emit_tail k KN KF K1.
  Qed.

  #[using="VSP"] Lemma epi_to_main : forall (Q : machine_state -> Prop) (st sc PL A L : Z) (pad : list byte) x1 t0 t1 t2 (x8 x9 : word) a1 a2 a3 a4 a5 a6 a7
      (x18 x19 x20 x21 x22 : word) t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    TRFRAME sp0 m pad sc PL A L -> stk asegs m lo (usp0 + -208) -> lo <= usp0 - 208 -> -128 <= sc < 128 ->
    (forall a1', stk asegs m lo (usp0 + -128) ->
       evt asegs Q (GST 0x5862c (Z_to_bv 64 0x86270) t0 t1 t2 (Z_to_bv 64 (if sc <? 0 then 0 else st)) (Z_to_bv 64 A)
                        (Z_to_bv 64 A) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) (Z_to_bv 64 sc) t3 t4 t5 t6 F fc m)) ->
    evt asegs Q (TST 0x86448 x1 t0 t1 t2 x8 x9 (Z_to_bv 64 st) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 F fc m).
  Proof.
    intros until lo. intros TFR ST HLO HSC K. pose proof psp_facts as SF. unfold TRFRAME in TFR.
    do 10 zstep. release_frame TFR ST (usp0 + -128). zstep.
    replace (ret_pc (Z_to_bv 64 0x861e8)) with (Z_to_bv 64 0x861e8) by (symmetry; rpc).
    destruct (Z.lt_ge_cases sc 0) as [SNEG|SPOS].
    -
      replace (sc <? 0) with true in K by (symmetry; apply Z.ltb_lt; lia).
      replace (Z_to_bv 64 sc) with (Z_to_bv 64 (sc + 2^64)) by (apply Z_to_bv_eqm; rewrite <- (Z.mod_add sc 1) by lia; f_equal; lia).
      zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia]. clear K2.
      zstep. zstep. zstep. replace (ret_pc (Z_to_bv 64 0x861f8)) with (Z_to_bv 64 0x861f8) by (symmetry; rpc).
      zstep. zstep. zstep. if_cases K3; zify_cond K3; [| exfalso; rewrite ?unsigned_lit in K3 by lia; lia]. clear K3.
      zstep. zstep.
      replace (Z_to_bv 64 (sc + 2^64)) with (Z_to_bv 64 sc) by (apply Z_to_bv_eqm; rewrite <- (Z.mod_add sc 1) by lia; f_equal; lia).
      apply K. exact ST.
    - replace (sc <? 0) with false in K by (symmetry; apply Z.ltb_ge; lia).
      zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. clear K2.
      zstep. zstep. zstep. zstep. apply K. exact ST.
  Qed.

  #[using="VSP"] Lemma free_ret_to_main : forall (Q : machine_state -> Prop) (fl : bool) (sc PL A L : Z) (pad : list byte) x1 t0 t1 t2 (x8 x9 : word) a0 a1 a2 a3 a4 a5 a6 a7
      (x18 x19 x20 x21 : word) t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    TRFRAME sp0 m pad sc PL A L -> stk asegs m lo (usp0 + -208) -> lo <= usp0 - 208 -> -128 <= sc < 128 ->
    (forall a1', stk asegs m lo (usp0 + -128) ->
       evt asegs Q (GST 0x5862c (Z_to_bv 64 0x86270) t0 t1 t2 (Z_to_bv 64 (if sc <? 0 then 0 else if fl then 78 else 0)) (Z_to_bv 64 A)
                        (Z_to_bv 64 A) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) (Z_to_bv 64 sc) t3 t4 t5 t6 F fc m)) ->
    evt asegs Q (TST 0x8643c x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m).
  Proof.
    intros until lo. intros TFR ST HLO HSC K.
    destruct fl; cbn [Z.b2z]; zstep; zstep; zstep.
    - eapply (epi_to_main _ 78); [exact TFR| exact ST| exact HLO| exact HSC| exact K].
    - eapply (epi_to_main _ 0); [exact TFR| exact ST| exact HLO| exact HSC| exact K].
  Qed.
End POST.
