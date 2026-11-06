(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From OSSVerify.Proofs.openssl.ct.lib.CtP Require Import Layout Lib_kit F_memset F_vsnprintf.
From OSSVerify.Proofs.openssl.ct.lib.CtBnP Require Import BnKit.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Import ApWalkTac.
From OSSVerify.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure TimeToTmDefs.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

(* [comment removed for export] *)
Definition TM_CELLS (sec mi hr md mo yr wd yd : Z) : list cell :=
  [C4 (Z_to_bv 64 sec); C4 (Z_to_bv 64 mi); C4 (Z_to_bv 64 hr); C4 (Z_to_bv 64 md); C4 (Z_to_bv 64 mo); C4 (Z_to_bv 64 yr);
   C4 (Z_to_bv 64 wd); C4 (Z_to_bv 64 yd); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Definition T2T_SAVED (x27 x26 x25 x24 x23 x22 x21 x20 x19 x18 x9 x8 x1 : word) : list cell :=
  [C8 x27; C8 x26; C8 x25; C8 x24; C8 x23; C8 x22; C8 x21; C8 x20; C8 x19; C8 x18; C8 x9; C8 x8; C8 x1].

Definition TIME_TO_TM_STACK : Z := 272 + 16.      (* [comment removed for export] *)

Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
Definition t2t_head0_post (sp gp tp : word) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) (l DA GS tm : Z) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -272)) gp tp x5 x6 x7 sp (Z_to_bv 64 (l - 1)) x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17
                  (Z_to_bv 64 DA) (Z_to_bv 64 24) (Z_to_bv 64 tm) (Z_to_bv 64 7) (Z_to_bv 64 l) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                  (Z_to_bv 64 12) (Z_to_bv 64 (GS + 1)) x28 x29 x30 x31)
             F (Z_to_bv 64 0x11d480) fc None m' (seg_rom ctpsegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono ctpsegs m m' /\ mem_inv ctpsegs m' /\ stk ctpsegs m' lo (bv_unsigned sp + -272)
    /\ rw_cells ctpsegs m' (bv_unsigned sp + -272)
         (T2T_CONSTS l l GS tm ++ TM_CELLS 0 0 0 0 0 0 0 0 ++ T2T_SAVED s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra).

Lemma t2t_front : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo l DA GS tm : Z),
  stk ctpsegs m lo (bv_unsigned sp) -> mem_inv ctpsegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  ro_cells ctpsegs m DA [C4 (Z_to_bv 64 l); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> (DA + 24 <= lo \/ bv_unsigned sp <= DA) -> DA + 24 <= 2^64 ->
  15 <= l < 2^31 -> 0 <= GS -> GS + l <= 2^63 -> 0 <= tm < 2^64 ->
  a0 = Z_to_bv 64 tm -> a1 = Z_to_bv 64 DA ->
  evt ctpsegs (t2t_head0_post sp gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m l DA GS tm)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OSSL_ASN1_TIME_TO_TM) fc None m (seg_rom ctpsegs)).
Proof.
  intros until tm. intros ST MI GLO LO SP63 HD SEPD DHI Hl GS0 GSHI TMR -> ->.
  unfold TIME_TO_TM_STACK, OSSL_ASN1_TIME_TO_TM, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 272 \/ bv_unsigned sp - 272 + 272 <= DA) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  (* [comment removed for export] *)
  carve_frame 272%nat ST. do 15 step.
  (* [comment removed for export] *)
  step. step. rewrite (sx32_small 24) by lia. step. step.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. try clear K0.
  step. step. if_cases K1; zify_cond K1; [exfalso; apply K1; reflexivity|]. try clear K1.
  do 4 step.
  (* [comment removed for export] *)
  step. rewrite (sx32_small l) by lia. step. step. step. step. step. step.
  name_mem m1.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB ctpsegs m1 _ [] 168 _ _ [112; 56]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
    pose proof (proj1 (rw_cells_app m1 _ [c0] (c1 :: rest)) FR) as [FRC FR1]; clear FR;
    pose proof (proj1 (rw_cells_app m1 _ [c1] rest) FR1) as [FRT FRS]; clear FR1 end.
  cbn [cells_size csize Nat.add] in FRT, FRS.
  replace (bv_unsigned sp + -272 + Z.of_nat 112) with (bv_unsigned sp + -160) in FRT by lia.
  replace (bv_unsigned sp + -272 + Z.of_nat 112 + Z.of_nat 56) with (bv_unsigned sp + -104) in FRS by lia.
  eapply evt_cut; [eapply memset_callZ; [exact FRT| exact MI| lia| lia| lia| lia]|]. post_call ctpsegs m1.
  name_mem m2. match goal with H : rw_cells ctpsegs m2 (bv_unsigned sp + -160) _ |- _ => rename H into FRT end.
  change (0 mod 256) with 0 in FRT. change (Z.to_nat 56) with 56%nat in FRT.
  (* [comment removed for export] *)
  step. brT ltsz.
  (* [comment removed for export] *)
  do 43 zstep.
  rewrite (land32 l), (Z.mod_small l (2^32)) in * by lia.
  name_mem m3. apply evt_done. unfold t2t_head0_post.
  do 15 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold T2T_CONSTS, TM_CELLS, T2T_SAVED, A_MINTAB, MASK47.
  apply (proj2 (rw_cells_app m3 _ _ _)). split; [exact FRC|].
  apply (proj2 (rw_cells_app m3 _ _ _)). cbn [cells_size csize Nat.add app].
  replace (bv_unsigned sp + -272 + Z.of_nat 112) with (bv_unsigned sp + -160) by lia.
  replace (bv_unsigned sp + -160 + Z.of_nat 56) with (bv_unsigned sp + -104) by lia.
  split; [| exact FRS].
  eapply rw_cells_recast; [exact FRT| cbn; tauto| reflexivity].
Qed.

(* [comment removed for export] *)
Definition t2t_leaf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctpsegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono ctpsegs m m' /\ mem_inv ctpsegs m' /\ stk ctpsegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma t2t_reject : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo l DA GS tm : Z),
  stk ctpsegs m lo (bv_unsigned sp) -> mem_inv ctpsegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  ro_cells ctpsegs m DA [C4 (Z_to_bv 64 l); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> (DA + 24 <= lo \/ bv_unsigned sp <= DA) -> DA + 24 <= 2^64 ->
  0 <= l < 15 -> 0 <= tm < 2^64 ->
  a0 = Z_to_bv 64 tm -> a1 = Z_to_bv 64 DA ->
  evt ctpsegs (t2t_leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OSSL_ASN1_TIME_TO_TM) fc None m (seg_rom ctpsegs)).
Proof.
  intros until tm. intros ST MI GLO LO SP63 HD SEPD DHI Hl TMR -> ->.
  unfold TIME_TO_TM_STACK, OSSL_ASN1_TIME_TO_TM, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 272 \/ bv_unsigned sp - 272 + 272 <= DA) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  carve_frame 272%nat ST. do 15 step.
  step. step. rewrite (sx32_small 24) by lia. step. step.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. try clear K0.
  step. step. if_cases K1; zify_cond K1; [exfalso; apply K1; reflexivity|]. try clear K1.
  do 4 step.
  step. rewrite (sx32_small l) by lia. step. step. step. step. step. step.
  name_mem m1.
  apply (rw_cells_split_CB ctpsegs m1 _ [] 168 _ _ [112; 56]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
    pose proof (proj1 (rw_cells_app m1 _ [c0] (c1 :: rest)) FR) as [FRC FR1]; clear FR;
    pose proof (proj1 (rw_cells_app m1 _ [c1] rest) FR1) as [FRT FRS]; clear FR1 end.
  cbn [cells_size csize Nat.add] in FRT, FRS.
  replace (bv_unsigned sp + -272 + Z.of_nat 112) with (bv_unsigned sp + -160) in FRT by lia.
  replace (bv_unsigned sp + -272 + Z.of_nat 112 + Z.of_nat 56) with (bv_unsigned sp + -104) in FRS by lia.
  eapply evt_cut; [eapply memset_callZ; [exact FRT| exact MI| lia| lia| lia| lia]|]. post_call ctpsegs m1.
  name_mem m2. match goal with H : rw_cells ctpsegs m2 (bv_unsigned sp + -160) _ |- _ => rename H into FRT end.
  change (0 mod 256) with 0 in FRT. change (Z.to_nat 56) with 56%nat in FRT.
  (* [comment removed for export] *)
  step. brF ltsz. step. step.
  (* [comment removed for export] *)
  replace (bv_unsigned sp + -160) with (bv_unsigned sp + -272 + Z.of_nat (cells_size [CB 112 (firstn 112 (firstn 168 junk))])) in FRT by (cbn; lia).
  lazymatch type of FRC with rw_cells _ _ _ ?cc =>
    pose proof (proj2 (rw_cells_app m2 _ cc _) (conj FRC FRT)) as FR1 end.
  lazymatch type of FR1 with rw_cells _ _ _ ?cc =>
    replace (bv_unsigned sp + -104) with (bv_unsigned sp + -272 + Z.of_nat (cells_size cc)) in FRS by (cbn; lia);
    pose proof (proj2 (rw_cells_app m2 _ cc _) (conj FR1 FRS)) as FR end.
  clear FRC FRT FR1 FRS. cbn [app] in FR.
  do 13 step. step. release_frame FR ST (bv_unsigned sp). step.
  name_mem m3. apply evt_done. unfold t2t_leaf_post.
  do 14 eexists. exists m3. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

End WithCeiling.
