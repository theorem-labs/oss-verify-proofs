(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr ZBridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BI_shadow BM_memcpy BI_memcpy_icp1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition memcpy_icp0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D : Z) (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma landM1 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma landM1_mod : forall x, Z.land x 18446744073709551615 = x mod 2^64.
Proof. intros x. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma rw_cells_CB0 : forall m B, 0 <= B -> B <= 2^64 -> rw_cells bsegs m B [CB 0 []].
Proof.
  intros m B H0 H1. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Section Walk.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S SB : Z) (lo : Z).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 2240.
Hypothesis HS : 0 < S < 2^47.
Hypothesis HD : 0 < D < 2^47.
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PSTK : forall a k, bv_unsigned sp - 2240 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PNUL : forall a, P (Z_to_bv 64 a, 0%nat).

Lemma SPR0 : 0 <= bv_unsigned sp < 2^64.
Proof. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Notation POST := (memcpy_icp0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D m lo).
Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -2160)).
Notation SP8 := (Z_to_bv 64 (bv_unsigned sp + -2152)).
Notation ST pc mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31 :=
  (MS (mkR x1 SP' gp tp x5 x6 x7 sp x9 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 0) x13 x14 x15 x16 x17 x18 x19 x20 SP8 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
Definition MINV0 (m0 : mem) : Prop :=
  mem_inv bsegs m0 /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp)] m m0 /\ wmono bsegs m m0 /\
  stk bsegs m0 lo (bv_unsigned sp + -80) /\
  rw_cells bsegs m0 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  icp_globals bsegs m0 SB.

(* [comment removed for export] *)
Lemma mci0_tail : forall m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31,
  MINV0 m0 ->
  evtA bsegs P POST (ST 0x53614 m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31).
Proof.
  intros until x31. intros (MI & MU & WM & SK & FR & G). pose proof SPR0 as SR.
  pose proof G as G'. icp_globals_open G.
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  assert (UD : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 0) = 0) by (apply unsigned_lit; lia).
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply evtA_cut; [ eapply (@memcpy_spec) with (src := []) (junk := []) (Pol := P) | ] end.
  1:{ intros a k H1 H2. rewrite ?US, ?UN in H1, H2. replace k with 0%nat by lia. apply PNUL. }
  1:{ intros a k H1 H2. rewrite ?UD, ?UN in H1, H2. replace k with 0%nat by lia. apply PNUL. }
  1:{ rewrite US. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. }
  1:{ rewrite UN. reflexivity. }
  1:{ rewrite UD, UN. apply rw_cells_CB0; lia. }
  1:{ rewrite US, UD, UN. lia. }
  1:{ exact MI. }
  cbv beta. intros ms' PO. unfold BM_memcpy1.memcpy_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> & MUc & WMc & MIc & _ & _).
  assert (MU0 : munch [] m0 m1). { eapply munch_weaken; [| exact MUc]. unfold sub_fp. cbn [outside]. intros; split; [lia| exact I]. }
  clear MUc.
  apply (rw_cells_transport bsegs [] m0 m1) in FR; [| exact MU0 | exact WMc | exact I].
  apply (stk_transport_disjoint bsegs [] m0 m1) in SK; [| exact MU0 | exact WMc | exact I].
  apply (icp_globals_transport bsegs [] m0 m1) in G'; [| exact MU0 | exact WMc | exact I].
  assert (MU1 : munch [(bv_unsigned sp - 2240, bv_unsigned sp)] m m1).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU0]. unfold sub_fp. cbn [outside]. intros; exact I. }
  pose proof (wmono_trans _ _ _ _ WM WMc) as WM1. clear MI MU WM.
  ret_pc_lit. rewrite ?UD, ?US, ?UN in *.
  stepA. (* [comment removed for export] *)
  do 10 stepA. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp).
  apply evtA_done. unfold memcpy_icp0_post.
  do 15 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.

(* [comment removed for export] *)
Lemma mci0_checks : forall m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x22 x23 x24 x28 x29 x30 x31,
  MINV0 m0 ->
  evtA bsegs P POST (ST 0x53580 m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 S) (Z_to_bv 64 D) x22 x23 x24 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV.
  zstepA. (* [comment removed for export] *) rewrite ?not64 by lia.
  zstepA. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?landM1, ?zb_lxor_ones, ?unsigned_lit by lia. rewrite ?landM1 by lia. lia. }
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K2; zify_cond K2.
  2:{ exfalso. revert K2. rewrite ?landM1_mod, ?unsigned_lit_wrap. clear. intros K2. cbn in K2. lia. }
  zstepA. if_cases K3; zify_cond K3. { exfalso. revert K3. rewrite ?landM1, ?unsigned_lit by lia. lia. }
  stepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) rewrite ?not64 by lia.
  zstepA. if_cases K4; zify_cond K4. { exfalso. revert K4. rewrite ?landM1, ?zb_lxor_ones, ?unsigned_lit by lia. rewrite ?landM1 by lia. lia. }
  zstepA. zstepA. (* [comment removed for export] *)
  if_cases K5; zify_cond K5.
  2:{ exfalso. revert K5. rewrite ?landM1_mod, ?unsigned_lit_wrap. clear. intros K5. cbn in K5. lia. }
  zstepA. if_cases K6; zify_cond K6. { exfalso. revert K6. rewrite ?landM1, ?unsigned_lit by lia. lia. }
  stepA. (* [comment removed for export] *)
  eapply mci0_tail; exact IV.
Qed.

Lemma memcpy_icp0_body : forall (t0' : word) x10 x11 x12 a3' a4' a5' a6' a7',
  stk bsegs m lo (bv_unsigned sp) -> mem_inv bsegs m ->
  x10 = Z_to_bv 64 D -> x11 = Z_to_bv 64 S -> x12 = Z_to_bv 64 0 -> t0' = t0 ->
  icp_globals bsegs m SB ->
  evtA bsegs P POST
    (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 x10 x11 x12 a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memcpy_icp_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until a7'. intros SK MI -> -> -> -> G. unfold memcpy_icp_entry. pose proof SPR0 as SR.
  assert (MU : munch [(bv_unsigned sp - 2240, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 80%nat SK.
  do 13 stepA.   (* [comment removed for export] *)
  lazymatch goal with MUx : munch _ m ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (icp_globals_transport bsegs) in G; [ | exact MUx | eassumption | cbn; lia ] end.
  pose proof G as G'. icp_globals_open G.
  stepA. stepA. stepA. (* [comment removed for export] *)
  cbv beta. stepA. if_false.  (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  rewrite ?Z.add_0_r.
  clear GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => assert (IV : MINV0 mx) end.
  { split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| exact G']. }
  zstepA. (* [comment removed for export] *) if_cases KE; zify_cond KE. { eapply mci0_checks; exact IV. }
  zstepA. (* [comment removed for export] *) if_cases KO1; zify_cond KO1. { eapply mci0_checks; exact IV. }
  zstepA. (* [comment removed for export] *) if_cases KO2; zify_cond KO2. { exfalso. revert KO1 KO2. rewrite ?landM1, ?unsigned_lit by lia. lia. }
  eapply mci0_checks; exact IV.
Qed.
End Walk.

Lemma memcpy_icp_zero_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S SB lo : Z) (P : acc -> Prop),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 2240 -> mem_inv bsegs m ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 0 -> 0 < S < 2^47 -> 0 < D < 2^47 ->
  icp_globals bsegs m SB ->
  (forall a k, bv_unsigned sp - 2240 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a, P (Z_to_bv 64 a, 0%nat)) ->
  evtA bsegs P (memcpy_icp0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memcpy_icp_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until P. intros SK LOC LO MI HA0 HA1 HA2 HS HD G PSTK PIMG PNUL.
  unfold alloc_ceiling, sp_window_lo, stack_max_size in LOC.
  subst a0 a1 a2. eapply (@memcpy_icp0_body P) with (D := D) (S := S) (SB := SB) (lo := lo); try eassumption; try reflexivity; lia.
Qed.

End RC__1.
