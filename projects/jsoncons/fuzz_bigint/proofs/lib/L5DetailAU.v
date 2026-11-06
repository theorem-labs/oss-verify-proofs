(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue BigLinkInlBaseU BigModel BigFactsRun BigFactsDigits L5Defs L5KnP L5ParseArith.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5DetailAU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5DAU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).

(* [comment removed for export] *)
Ltac zc_eval ZA Hag :=
  lazymatch goal with |- bv_unsigned (edenot ?E2 ?e) = _ =>
    lazymatch type of Hag with env_agree ?b ?E1 _ =>
      rewrite (BG.edenot_kept b E1 E2 e Hag eq_refl);
      let t := eval vm_compute in (BL.zc e) in rewrite (BL.zcomp_sound E1 e t eq_refl); cbn [BL.zden]; unfold BL.uv end end;
  rewrite ?ZA.
(* [comment removed for export] *)
Ltac zc_eval0 ZA :=
  lazymatch goal with |- bv_unsigned (edenot ?E1 ?e) = _ =>
      let t := eval vm_compute in (BL.zc e) in rewrite (BL.zcomp_sound E1 e t eq_refl); cbn [BL.zden]; unfold BL.uv end;
  rewrite ?ZA.
Ltac kn1x ZA := first [ L5KP.kn1 ZA
  | lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5KP.kentry_KRange; [zc_eval0 ZA; reflexivity | lia] end ].
Ltac kn_allx ZA := repeat (apply Forall_cons; [kn1x ZA|]); try apply Forall_nil.

(* [comment removed for export] *)
Lemma not_eval (x : Z) : 0 <= x < 2 ^ 64 -> ((18446744073709551615 * x) mod BL.MM + 18446744073709551615) mod BL.MM = 2 ^ 64 - 1 - x.
Proof.
  intros Hx. unfold BL.MM. rewrite Z.add_mod_idemp_l by lia.
  replace (18446744073709551615 * x + 18446744073709551615) with ((2 ^ 64 - 1 - x) + x * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.


(* [comment removed for export] *)
Module PA0 := LibSegZ_pa0u.
Definition KS_A0 : list nat := Eval vm_compute in (BG.kept_list 48 PA0.regs0 PA0.regs_out).
Lemma KS_A0_ok : BG.kept_ok 48 PA0.regs0 PA0.regs_out KS_A0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A0_1 : nth 1 PA0.regs_out (ELit 0) = EVar 1. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A0_2 : nth 2 PA0.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A0_10 : nth 10 PA0.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A0_11 : nth 11 PA0.regs_out (ELit 0) = ELit 22. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A0 : SR.ps_cells PA0.ps0 = PA0.cells. Proof. reflexivity. Qed.
Definition VAL_A0 (R : bvmap 5 word) (sp : Z) (p : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 10%nat => Z_to_bv 64 p | 11%nat => Z_to_bv 64 0 | _ => getr R (reg k) end.
Definition VZ_A0 (R : bvmap 5 word) (sp : Z) (p : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 10%nat => p | 11%nat => 0 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A0 R sp p : 0 <= sp < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A0 R sp p) (fun _ => [])) k) = VZ_A0 R sp p k.
Proof.
  intros. cbn [ev]. unfold VAL_A0, VZ_A0.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa0u_conc fx R M sp p :
  getr R (reg 2) = Z_to_bv 64 sp ->
  getr R (reg 10) = Z_to_bv 64 p ->
  getr R (reg 11) = Z_to_bv 64 (0) ->
  0 <= sp < 2 ^ 64 ->
  0 <= p < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 112) (112) ->
  exists fx' R' M', msteps RSEGS (st fx R 134820 M) (st fx' R' 135296 M')
    /\ (forall i, In i KS_A0 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = getr R (reg 1)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp)
    /\ getr R' (reg 10) = Z_to_bv 64 (p)
    /\ getr R' (reg 11) = Z_to_bv 64 (22)
    /\ L5.u64_at RSEGS M' ((sp) - 80) (bv_unsigned (getr R (reg 24)))
    /\ L5.u64_at RSEGS M' ((sp) - 72) (bv_unsigned (getr R (reg 23)))
    /\ L5.u64_at RSEGS M' ((sp) - 64) (bv_unsigned (getr R (reg 22)))
    /\ L5.u64_at RSEGS M' ((sp) - 56) (bv_unsigned (getr R (reg 21)))
    /\ L5.u64_at RSEGS M' ((sp) - 48) (bv_unsigned (getr R (reg 20)))
    /\ L5.u64_at RSEGS M' ((sp) - 40) (bv_unsigned (getr R (reg 19)))
    /\ L5.u64_at RSEGS M' ((sp) - 32) (bv_unsigned (getr R (reg 18)))
    /\ L5.u64_at RSEGS M' ((sp) - 24) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' ((sp) - 16) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' ((sp) - 8) (bv_unsigned (getr R (reg 1)))
    /\ (forall x : word, ~ ((sp) + -112 <= bv_unsigned x < (sp) + -112 + (112)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H10 H11 G2 G10 K1 K2 K3.
  set (Vf := VAL_A0 R sp p). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A0 R sp p k) by (apply VAL_VZ_A0; lia). unfold VZ_A0 in ZA.
  assert (HR: regs_ok E PA0.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA0.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA0.kn0). { unfold know_ok, PA0.kn0. kn_allx ZA. }
  destruct (PA0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA0.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA0.regs0 PA0.regs_out 48 KS_A0 KS_A0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA0.regs_out E' R' 1 Hregs) by lia. rewrite ro_A0_1. cbn [edenot]. rewrite <- (proj1 Hag 1%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PA0.regs_out E' R' 2 Hregs) by lia. rewrite ro_A0_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA0.regs_out E' R' 10 Hregs) by lia. rewrite ro_A0_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA0.regs_out E' R' 11 Hregs) by lia. rewrite ro_A0_11. L5KP.wordE' ZA Hag. }
  rewrite cells_A0 in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA0.cells, PA0.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA0.cells, PA0.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA0.cells, PA0.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA0.cells, PA0.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA0.cells, PA0.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA0.cells, PA0.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA0.cells, PA0.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA0.cells, PA0.cells0. right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA0.cells, PA0.cells0. right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA0.cells, PA0.cells0. right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0. apply Hfr. unfold PA0.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA1 := LibSegZ_pa1u.
Definition KS_A1 : list nat := Eval vm_compute in (BG.kept_list 48 PA1.regs0 PA1.regs_out).
Lemma KS_A1_ok : BG.kept_ok 48 PA1.regs0 PA1.regs_out KS_A1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_2 : nth 2 PA1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_8 : nth 8 PA1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (EVar 11). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_9 : nth 9 PA1.regs_out (ELit 0) = EVar 13. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_10 : nth 10 PA1.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_11 : nth 11 PA1.regs_out (ELit 0) = ELit 48. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_12 : nth 12 PA1.regs_out (ELit 0) = ELit 18446744073709551615. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_18 : nth 18 PA1.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_19 : nth 19 PA1.regs_out (ELit 0) = EVar 12. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_20 : nth 20 PA1.regs_out (ELit 0) = EVar 11. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A1 : SR.ps_cells PA1.ps0 = PA1.cells. Proof. reflexivity. Qed.
Definition VAL_A1 (R : bvmap 5 word) (sp : Z) (p : Z) (m : Z) (ng : Z) (o : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 10%nat => Z_to_bv 64 p | 11%nat => Z_to_bv 64 m | 12%nat => Z_to_bv 64 ng | 13%nat => Z_to_bv 64 o | _ => getr R (reg k) end.
Definition VZ_A1 (R : bvmap 5 word) (sp : Z) (p : Z) (m : Z) (ng : Z) (o : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 10%nat => p | 11%nat => m | 12%nat => ng | 13%nat => o | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A1 R sp p m ng o : 0 <= sp < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= m < 2 ^ 64 -> 0 <= ng < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A1 R sp p m ng o) (fun _ => [])) k) = VZ_A1 R sp p m ng o k.
Proof.
  intros. cbn [ev]. unfold VAL_A1, VZ_A1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa1u_conc fx R M sp p m ng o :
  getr R (reg 2) = Z_to_bv 64 sp ->
  getr R (reg 10) = Z_to_bv 64 p ->
  getr R (reg 11) = Z_to_bv 64 m ->
  getr R (reg 12) = Z_to_bv 64 ng ->
  getr R (reg 13) = Z_to_bv 64 o ->
  0 <= sp < 2 ^ 64 ->
  0 <= p < 2 ^ 64 ->
  0 <= m < 2 ^ 64 ->
  0 <= ng < 2 ^ 64 ->
  0 <= o < 2 ^ 64 ->
  p + m <= 2 ^ 47 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 112) (112) ->
  1 <= m <= 4999 ->
  4096 <= p <= 140737488355328 ->
  exists fx' R' M', msteps RSEGS (st fx R 134820 M) (st fx' R' 134912 M')
    /\ (forall i, In i KS_A1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 8) = Z_to_bv 64 (p + m)
    /\ getr R' (reg 9) = Z_to_bv 64 (o)
    /\ getr R' (reg 10) = Z_to_bv 64 (p)
    /\ getr R' (reg 11) = Z_to_bv 64 (48)
    /\ getr R' (reg 12) = Z_to_bv 64 (18446744073709551615)
    /\ getr R' (reg 18) = Z_to_bv 64 (p)
    /\ getr R' (reg 19) = Z_to_bv 64 (ng)
    /\ getr R' (reg 20) = Z_to_bv 64 (m)
    /\ L5.u64_at RSEGS M' ((sp) - 80) (bv_unsigned (getr R (reg 24)))
    /\ L5.u64_at RSEGS M' ((sp) - 72) (bv_unsigned (getr R (reg 23)))
    /\ L5.u64_at RSEGS M' ((sp) - 64) (bv_unsigned (getr R (reg 22)))
    /\ L5.u64_at RSEGS M' ((sp) - 56) (bv_unsigned (getr R (reg 21)))
    /\ L5.u64_at RSEGS M' ((sp) - 48) (bv_unsigned (getr R (reg 20)))
    /\ L5.u64_at RSEGS M' ((sp) - 40) (bv_unsigned (getr R (reg 19)))
    /\ L5.u64_at RSEGS M' ((sp) - 32) (bv_unsigned (getr R (reg 18)))
    /\ L5.u64_at RSEGS M' ((sp) - 24) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' ((sp) - 16) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' ((sp) - 8) (bv_unsigned (getr R (reg 1)))
    /\ (forall x : word, ~ ((sp) + -112 <= bv_unsigned x < (sp) + -112 + (112)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H10 H11 H12 H13 G2 G10 G11 G12 G13 X0 K1 K2 K3 K4 K5.
  set (Vf := VAL_A1 R sp p m ng o). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A1 R sp p m ng o k) by (apply VAL_VZ_A1; lia). unfold VZ_A1 in ZA.
  assert (HR: regs_ok E PA1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA1.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA1.kn0). { unfold know_ok, PA1.kn0. kn_allx ZA. }
  destruct (PA1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA1.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA1.regs0 PA1.regs_out 48 KS_A1 KS_A1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 2 Hregs) by lia. rewrite ro_A1_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 8 Hregs) by lia. rewrite ro_A1_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 9 Hregs) by lia. rewrite ro_A1_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 10 Hregs) by lia. rewrite ro_A1_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 11 Hregs) by lia. rewrite ro_A1_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 12 Hregs) by lia. rewrite ro_A1_12. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 18 Hregs) by lia. rewrite ro_A1_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 19 Hregs) by lia. rewrite ro_A1_19. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 20 Hregs) by lia. rewrite ro_A1_20. L5KP.wordE' ZA Hag. }
  rewrite cells_A1 in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0. apply Hfr. unfold PA1.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA2 := LibSegZ_pa2u.
Definition KS_A2 : list nat := Eval vm_compute in (BG.kept_list 48 PA2.regs0 PA2.regs_out).
Lemma KS_A2_ok : BG.kept_ok 48 PA2.regs0 PA2.regs_out KS_A2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_1 : nth 1 PA2.regs_out (ELit 0) = ELit 134988. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_2 : nth 2 PA2.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_10 : nth 10 PA2.regs_out (ELit 0) = EVar 9. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_11 : nth 11 PA2.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma cells_A2 : SR.ps_cells PA2.ps0 = PA2.cells. Proof. reflexivity. Qed.
Definition VAL_A2 (R : bvmap 5 word) (sp : Z) (o : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 9%nat => Z_to_bv 64 o | _ => getr R (reg k) end.
Definition VZ_A2 (R : bvmap 5 word) (sp : Z) (o : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 9%nat => o | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A2 R sp o : 0 <= sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A2 R sp o) (fun _ => [])) k) = VZ_A2 R sp o k.
Proof.
  intros. cbn [ev]. unfold VAL_A2, VZ_A2.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa2u_conc fx R M sp o :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 9) = Z_to_bv 64 o ->
  0 <= sp < 2 ^ 64 ->
  0 <= o < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 112) (112) ->
  exists fx' R' M', msteps RSEGS (st fx R 134952 M) (st fx' R' 136232 M')
    /\ (forall i, In i KS_A2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (134988)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 10) = Z_to_bv 64 (o)
    /\ getr R' (reg 11) = Z_to_bv 64 (sp - 112)
    /\ L5.u64_at RSEGS M' ((sp) - 88) (0)
    /\ L5.u64_at RSEGS M' ((sp) - 96) (0)
    /\ L5.u64_at RSEGS M' ((sp) - 104) (0)
    /\ L5.u8_at RSEGS M' ((sp) - 112) (0)
    /\ (forall x : word, ~ ((sp) + -112 <= bv_unsigned x < (sp) + -112 + (32)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H9 G2 G9 K1 K2 K3.
  set (Vf := VAL_A2 R sp o). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A2 R sp o k) by (apply VAL_VZ_A2; lia). unfold VZ_A2 in ZA.
  assert (HR: regs_ok E PA2.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA2.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA2.kn0). { unfold know_ok, PA2.kn0. kn_allx ZA. }
  destruct (PA2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA2.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA2.regs0 PA2.regs_out 48 KS_A2 KS_A2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA2.regs_out E' R' 1 Hregs) by lia. rewrite ro_A2_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA2.regs_out E' R' 2 Hregs) by lia. rewrite ro_A2_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA2.regs_out E' R' 10 Hregs) by lia. rewrite ro_A2_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA2.regs_out E' R' 11 Hregs) by lia. rewrite ro_A2_11. L5KP.wordE' ZA Hag. }
  rewrite cells_A2 in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA2.cells, PA2.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA2.cells, PA2.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA2.cells, PA2.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PA2.cells, PA2.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { intros x Hy0. apply Hfr. unfold PA2.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA3 := LibSegZ_pa3u.
Definition KS_A3 : list nat := Eval vm_compute in (BG.kept_list 56 PA3.regs0 PA3.regs_out).
Lemma KS_A3_ok : BG.kept_ok 56 PA3.regs0 PA3.regs_out KS_A3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A3_1 : nth 1 PA3.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A3_2 : nth 2 PA3.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A3_8 : nth 8 PA3.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A3_9 : nth 9 PA3.regs_out (ELit 0) = EVar 43. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A3_10 : nth 10 PA3.regs_out (ELit 0) = EVar 8. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A3_11 : nth 11 PA3.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A3_18 : nth 18 PA3.regs_out (ELit 0) = EVar 44. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A3_19 : nth 19 PA3.regs_out (ELit 0) = EVar 45. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A3_20 : nth 20 PA3.regs_out (ELit 0) = EVar 46. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A3_21 : nth 21 PA3.regs_out (ELit 0) = EVar 47. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A3_22 : nth 22 PA3.regs_out (ELit 0) = EVar 48. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A3_23 : nth 23 PA3.regs_out (ELit 0) = EVar 49. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A3_24 : nth 24 PA3.regs_out (ELit 0) = EVar 50. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A3 : SR.ps_cells PA3.ps0 = PA3.cells. Proof. reflexivity. Qed.
Definition VAL_A3 (R : bvmap 5 word) (sp : Z) (pe : Z) (c1 : Z) (c2 : Z) (c3 : Z) (c4 : Z) (c5 : Z) (c6 : Z) (c7 : Z) (c8 : Z) (c9 : Z) (c10 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 8%nat => Z_to_bv 64 pe | 41%nat => Z_to_bv 64 c1 | 42%nat => Z_to_bv 64 c2 | 43%nat => Z_to_bv 64 c3 | 44%nat => Z_to_bv 64 c4 | 45%nat => Z_to_bv 64 c5 | 46%nat => Z_to_bv 64 c6 | 47%nat => Z_to_bv 64 c7 | 48%nat => Z_to_bv 64 c8 | 49%nat => Z_to_bv 64 c9 | 50%nat => Z_to_bv 64 c10 | _ => getr R (reg k) end.
Definition VZ_A3 (R : bvmap 5 word) (sp : Z) (pe : Z) (c1 : Z) (c2 : Z) (c3 : Z) (c4 : Z) (c5 : Z) (c6 : Z) (c7 : Z) (c8 : Z) (c9 : Z) (c10 : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 8%nat => pe | 41%nat => c1 | 42%nat => c2 | 43%nat => c3 | 44%nat => c4 | 45%nat => c5 | 46%nat => c6 | 47%nat => c7 | 48%nat => c8 | 49%nat => c9 | 50%nat => c10 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A3 R sp pe c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : 0 <= sp < 2 ^ 64 -> 0 <= pe < 2 ^ 64 -> 0 <= c1 < 2 ^ 64 -> 0 <= c2 < 2 ^ 64 -> 0 <= c3 < 2 ^ 64 -> 0 <= c4 < 2 ^ 64 -> 0 <= c5 < 2 ^ 64 -> 0 <= c6 < 2 ^ 64 -> 0 <= c7 < 2 ^ 64 -> 0 <= c8 < 2 ^ 64 -> 0 <= c9 < 2 ^ 64 -> 0 <= c10 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A3 R sp pe c1 c2 c3 c4 c5 c6 c7 c8 c9 c10) (fun _ => [])) k) = VZ_A3 R sp pe c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 k.
Proof.
  intros. cbn [ev]. unfold VAL_A3, VZ_A3.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa3u_conc fx R M sp pe c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 8) = Z_to_bv 64 pe ->
  0 <= sp < 2 ^ 64 ->
  0 <= pe < 2 ^ 64 ->
  0 <= c1 < 2 ^ 64 ->
  0 <= c2 < 2 ^ 64 ->
  0 <= c3 < 2 ^ 64 ->
  0 <= c4 < 2 ^ 64 ->
  0 <= c5 < 2 ^ 64 ->
  0 <= c6 < 2 ^ 64 ->
  0 <= c7 < 2 ^ 64 ->
  0 <= c8 < 2 ^ 64 ->
  0 <= c9 < 2 ^ 64 ->
  0 <= c10 < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.u8_at RSEGS M ((sp) - 112) (0) ->
  L5.u64_at RSEGS M ((sp) - 8) (c1) ->
  L5.u64_at RSEGS M ((sp) - 16) (c2) ->
  L5.u64_at RSEGS M ((sp) - 24) (c3) ->
  L5.u64_at RSEGS M ((sp) - 32) (c4) ->
  L5.u64_at RSEGS M ((sp) - 40) (c5) ->
  L5.u64_at RSEGS M ((sp) - 48) (c6) ->
  L5.u64_at RSEGS M ((sp) - 56) (c7) ->
  L5.u64_at RSEGS M ((sp) - 64) (c8) ->
  L5.u64_at RSEGS M ((sp) - 72) (c9) ->
  L5.u64_at RSEGS M ((sp) - 80) (c10) ->
  exists fx' R' M', msteps RSEGS (st fx R 134988 M) (st fx' R' 135296 M')
    /\ (forall i, In i KS_A3 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (c1)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp)
    /\ getr R' (reg 8) = Z_to_bv 64 (c2)
    /\ getr R' (reg 9) = Z_to_bv 64 (c3)
    /\ getr R' (reg 10) = Z_to_bv 64 (pe)
    /\ getr R' (reg 11) = Z_to_bv 64 (0)
    /\ getr R' (reg 18) = Z_to_bv 64 (c4)
    /\ getr R' (reg 19) = Z_to_bv 64 (c5)
    /\ getr R' (reg 20) = Z_to_bv 64 (c6)
    /\ getr R' (reg 21) = Z_to_bv 64 (c7)
    /\ getr R' (reg 22) = Z_to_bv 64 (c8)
    /\ getr R' (reg 23) = Z_to_bv 64 (c9)
    /\ getr R' (reg 24) = Z_to_bv 64 (c10)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H8 G2 G8 G41 G42 G43 G44 G45 G46 G47 G48 G49 G50 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13.
  set (Vf := VAL_A3 R sp pe c1 c2 c3 c4 c5 c6 c7 c8 c9 c10). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A3 R sp pe c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 k) by (apply VAL_VZ_A3; lia). unfold VZ_A3 in ZA.
  assert (HR: regs_ok E PA3.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA3.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA3.kn0). { unfold know_ok, PA3.kn0. kn_allx ZA. }
  destruct (PA3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA3.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA3.regs0 PA3.regs_out 56 KS_A3 KS_A3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA3.regs_out E' R' 1 Hregs) by lia. rewrite ro_A3_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA3.regs_out E' R' 2 Hregs) by lia. rewrite ro_A3_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA3.regs_out E' R' 8 Hregs) by lia. rewrite ro_A3_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA3.regs_out E' R' 9 Hregs) by lia. rewrite ro_A3_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA3.regs_out E' R' 10 Hregs) by lia. rewrite ro_A3_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA3.regs_out E' R' 11 Hregs) by lia. rewrite ro_A3_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA3.regs_out E' R' 18 Hregs) by lia. rewrite ro_A3_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA3.regs_out E' R' 19 Hregs) by lia. rewrite ro_A3_19. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA3.regs_out E' R' 20 Hregs) by lia. rewrite ro_A3_20. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA3.regs_out E' R' 21 Hregs) by lia. rewrite ro_A3_21. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA3.regs_out E' R' 22 Hregs) by lia. rewrite ro_A3_22. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA3.regs_out E' R' 23 Hregs) by lia. rewrite ro_A3_23. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA3.regs_out E' R' 24 Hregs) by lia. rewrite ro_A3_24. L5KP.wordE' ZA Hag. }
  rewrite cells_A3 in Hcells.
  split. { intros x. apply Hfr. unfold PA3.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA4S := LibSegZ_pa4su.
Definition KS_A4S : list nat := Eval vm_compute in (BG.kept_list 48 PA4S.regs0 PA4S.regs_out).
Lemma KS_A4S_ok : BG.kept_ok 48 PA4S.regs0 PA4S.regs_out KS_A4S = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A4S_1 : nth 1 PA4S.regs_out (ELit 0) = ELit 135104. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A4S_2 : nth 2 PA4S.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A4S_10 : nth 10 PA4S.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A4S_11 : nth 11 PA4S.regs_out (ELit 0) = ELit 1. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A4S : SR.ps_cells PA4S.ps0 = PA4S.cells. Proof. reflexivity. Qed.
Definition VAL_A4S (R : bvmap 5 word) (sp : Z) (m : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 20%nat => Z_to_bv 64 m | _ => getr R (reg k) end.
Definition VZ_A4S (R : bvmap 5 word) (sp : Z) (m : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 20%nat => m | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A4S R sp m : 0 <= sp < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A4S R sp m) (fun _ => [])) k) = VZ_A4S R sp m k.
Proof.
  intros. cbn [ev]. unfold VAL_A4S, VZ_A4S.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa4su_conc fx R M sp m :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 20) = Z_to_bv 64 m ->
  0 <= sp < 2 ^ 64 ->
  0 <= m < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 112) (112) ->
  1 <= m <= 9 ->
  exists fx' R' M', msteps RSEGS (st fx R 134936 M) (st fx' R' 136772 M')
    /\ (forall i, In i KS_A4S -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (135104)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 10) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 11) = Z_to_bv 64 (1)
    /\ L5.u64_at RSEGS M' ((sp) - 88) (0)
    /\ L5.u64_at RSEGS M' ((sp) - 96) (0)
    /\ L5.u64_at RSEGS M' ((sp) - 104) (0)
    /\ L5.u8_at RSEGS M' ((sp) - 112) (0)
    /\ (forall x : word, ~ ((sp) + -112 <= bv_unsigned x < (sp) + -112 + (32)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H20 G2 G20 K1 K2 K3 K4.
  set (Vf := VAL_A4S R sp m). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A4S R sp m k) by (apply VAL_VZ_A4S; lia). unfold VZ_A4S in ZA.
  assert (HR: regs_ok E PA4S.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA4S.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA4S.kn0). { unfold know_ok, PA4S.kn0. kn_allx ZA. }
  destruct (PA4S.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA4S.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA4S.regs0 PA4S.regs_out 48 KS_A4S KS_A4S_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA4S.regs_out E' R' 1 Hregs) by lia. rewrite ro_A4S_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA4S.regs_out E' R' 2 Hregs) by lia. rewrite ro_A4S_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA4S.regs_out E' R' 10 Hregs) by lia. rewrite ro_A4S_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA4S.regs_out E' R' 11 Hregs) by lia. rewrite ro_A4S_11. L5KP.wordE' ZA Hag. }
  rewrite cells_A4S in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA4S.cells, PA4S.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA4S.cells, PA4S.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA4S.cells, PA4S.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PA4S.cells, PA4S.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { intros x Hy0. apply Hfr. unfold PA4S.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA4L := LibSegZ_pa4lu.
Definition KS_A4L : list nat := Eval vm_compute in (BG.kept_list 48 PA4L.regs0 PA4L.regs_out).
Lemma KS_A4L_ok : BG.kept_ok 48 PA4L.regs0 PA4L.regs_out KS_A4L = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A4L_1 : nth 1 PA4L.regs_out (ELit 0) = ELit 135104. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A4L_2 : nth 2 PA4L.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A4L_10 : nth 10 PA4L.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A4L_11 : nth 11 PA4L.regs_out (ELit 0) = EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 3402) (EVar 20)) (ELit 10)) (ELit 64)) (ELit 6). Proof. vm_compute. reflexivity. Qed.
Lemma cells_A4L : SR.ps_cells PA4L.ps0 = PA4L.cells. Proof. reflexivity. Qed.
Definition VAL_A4L (R : bvmap 5 word) (sp : Z) (m : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 20%nat => Z_to_bv 64 m | _ => getr R (reg k) end.
Definition VZ_A4L (R : bvmap 5 word) (sp : Z) (m : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 20%nat => m | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A4L R sp m : 0 <= sp < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A4L R sp m) (fun _ => [])) k) = VZ_A4L R sp m k.
Proof.
  intros. cbn [ev]. unfold VAL_A4L, VZ_A4L.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa4lu_conc fx R M sp m :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 20) = Z_to_bv 64 m ->
  0 <= sp < 2 ^ 64 ->
  0 <= m < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 112) (112) ->
  10 <= m <= 4999 ->
  exists fx' R' M', msteps RSEGS (st fx R 134936 M) (st fx' R' 136772 M')
    /\ (forall i, In i KS_A4L -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (135104)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 10) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 11) = Z_to_bv 64 (Z.of_nat (num_words_est (Z.to_nat m)))
    /\ L5.u64_at RSEGS M' ((sp) - 88) (0)
    /\ L5.u64_at RSEGS M' ((sp) - 96) (0)
    /\ L5.u64_at RSEGS M' ((sp) - 104) (0)
    /\ L5.u8_at RSEGS M' ((sp) - 112) (0)
    /\ (forall x : word, ~ ((sp) + -112 <= bv_unsigned x < (sp) + -112 + (32)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H20 G2 G20 K1 K2 K3 K4.
  set (Vf := VAL_A4L R sp m). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A4L R sp m k) by (apply VAL_VZ_A4L; lia). unfold VZ_A4L in ZA.
  assert (HR: regs_ok E PA4L.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA4L.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA4L.kn0). { unfold know_ok, PA4L.kn0. kn_allx ZA. }
  destruct (PA4L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA4L.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA4L.regs0 PA4L.regs_out 48 KS_A4L KS_A4L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA4L.regs_out E' R' 1 Hregs) by lia. rewrite ro_A4L_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA4L.regs_out E' R' 2 Hregs) by lia. rewrite ro_A4L_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA4L.regs_out E' R' 10 Hregs) by lia. rewrite ro_A4L_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA4L.regs_out E' R' 11 Hregs) by lia. rewrite ro_A4L_11. apply BG.word_of_unsigned. zc_eval ZA Hag. apply L5PA.nwe_eval. lia. }
  rewrite cells_A4L in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA4L.cells, PA4L.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA4L.cells, PA4L.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA4L.cells, PA4L.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PA4L.cells, PA4L.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { intros x Hy0. apply Hfr. unfold PA4L.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA5 := LibSegZ_pa5u.
Definition KS_A5 : list nat := Eval vm_compute in (BG.kept_list 48 PA5.regs0 PA5.regs_out).
Lemma KS_A5_ok : BG.kept_ok 48 PA5.regs0 PA5.regs_out KS_A5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A5_2 : nth 2 PA5.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A5_10 : nth 10 PA5.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A5_18 : nth 18 PA5.regs_out (ELit 0) = EVar 18. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A5_20 : nth 20 PA5.regs_out (ELit 0) = EVar 20. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A5_21 : nth 21 PA5.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A5_22 : nth 22 PA5.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 18)) (ELit (-1)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A5_23 : nth 23 PA5.regs_out (ELit 0) = ELit 9. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A5 : SR.ps_cells PA5.ps0 = PA5.cells. Proof. reflexivity. Qed.
Definition VAL_A5 (R : bvmap 5 word) (sp : Z) (p : Z) (m : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 18%nat => Z_to_bv 64 p | 20%nat => Z_to_bv 64 m | _ => getr R (reg k) end.
Definition VZ_A5 (R : bvmap 5 word) (sp : Z) (p : Z) (m : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 18%nat => p | 20%nat => m | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A5 R sp p m : 0 <= sp < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A5 R sp p m) (fun _ => [])) k) = VZ_A5 R sp p m k.
Proof.
  intros. cbn [ev]. unfold VAL_A5, VZ_A5.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa5u_conc fx R M sp p m :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 18) = Z_to_bv 64 p ->
  getr R (reg 20) = Z_to_bv 64 m ->
  0 <= sp < 2 ^ 64 ->
  0 <= p < 2 ^ 64 ->
  0 <= m < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  1 <= m <= 4999 ->
  4096 <= p <= 140737488355327 ->
  exists fx' R' M', msteps RSEGS (st fx R 135104 M) (st fx' R' 135124 M')
    /\ (forall i, In i KS_A5 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 10) = Z_to_bv 64 (0)
    /\ getr R' (reg 18) = Z_to_bv 64 (p)
    /\ getr R' (reg 20) = Z_to_bv 64 (m)
    /\ getr R' (reg 21) = Z_to_bv 64 (0)
    /\ getr R' (reg 22) = Z_to_bv 64 (2 ^ 64 - 1 - p)
    /\ getr R' (reg 23) = Z_to_bv 64 (9)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H18 H20 G2 G18 G20 K1 K2 K3 K4.
  set (Vf := VAL_A5 R sp p m). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A5 R sp p m k) by (apply VAL_VZ_A5; lia). unfold VZ_A5 in ZA.
  assert (HR: regs_ok E PA5.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA5.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA5.kn0). { unfold know_ok, PA5.kn0. kn_allx ZA. }
  destruct (PA5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA5.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA5.regs0 PA5.regs_out 48 KS_A5 KS_A5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA5.regs_out E' R' 2 Hregs) by lia. rewrite ro_A5_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA5.regs_out E' R' 10 Hregs) by lia. rewrite ro_A5_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA5.regs_out E' R' 18 Hregs) by lia. rewrite ro_A5_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA5.regs_out E' R' 20 Hregs) by lia. rewrite ro_A5_20. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA5.regs_out E' R' 21 Hregs) by lia. rewrite ro_A5_21. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA5.regs_out E' R' 22 Hregs) by lia. rewrite ro_A5_22. apply BG.word_of_unsigned. zc_eval ZA Hag. apply not_eval. lia. }
  split. { rewrite (BG.out_reg PA5.regs_out E' R' 23 Hregs) by lia. rewrite ro_A5_23. L5KP.wordE' ZA Hag. }
  rewrite cells_A5 in Hcells.
  split. { intros x. apply Hfr. unfold PA5.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA6 := LibSegZ_pa6u.
Definition KS_A6 : list nat := Eval vm_compute in (BG.kept_list 48 PA6.regs0 PA6.regs_out).
Lemma KS_A6_ok : BG.kept_ok 48 PA6.regs0 PA6.regs_out KS_A6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A6_1 : nth 1 PA6.regs_out (ELit 0) = ELit 135152. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A6_2 : nth 2 PA6.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A6_10 : nth 10 PA6.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A6_11 : nth 11 PA6.regs_out (ELit 0) = ELit 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A6_21 : nth 21 PA6.regs_out (ELit 0) = EVar 21. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A6_22 : nth 22 PA6.regs_out (ELit 0) = EVar 22. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A6_24 : nth 24 PA6.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A6 : SR.ps_cells PA6.ps0 = PA6.cells. Proof. reflexivity. Qed.
Definition VAL_A6 (R : bvmap 5 word) (sp : Z) (pj : Z) (jd : Z) (np : Z) (c : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 18%nat => Z_to_bv 64 pj | 21%nat => Z_to_bv 64 jd | 22%nat => Z_to_bv 64 np | 40%nat => Z_to_bv 64 c | 23%nat => Z_to_bv 64 9 | _ => getr R (reg k) end.
Definition VZ_A6 (R : bvmap 5 word) (sp : Z) (pj : Z) (jd : Z) (np : Z) (c : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 18%nat => pj | 21%nat => jd | 22%nat => np | 40%nat => c | 23%nat => 9 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A6 R sp pj jd np c : 0 <= sp < 2 ^ 64 -> 0 <= pj < 2 ^ 64 -> 0 <= jd < 2 ^ 64 -> 0 <= np < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A6 R sp pj jd np c) (fun _ => [])) k) = VZ_A6 R sp pj jd np c k.
Proof.
  intros. cbn [ev]. unfold VAL_A6, VZ_A6.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa6u_conc fx R M sp pj jd np c :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 18) = Z_to_bv 64 pj ->
  getr R (reg 21) = Z_to_bv 64 jd ->
  getr R (reg 22) = Z_to_bv 64 np ->
  getr R (reg 23) = Z_to_bv 64 (9) ->
  0 <= sp < 2 ^ 64 ->
  0 <= pj <= 281474976710656 ->
  0 <= jd <= 4999 ->
  18446603336221196288 <= np <= 18446744073709551615 ->
  0 <= c < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  4096 <= pj <= 140737488355327 ->
  L5.u8_at RSEGS M (pj) (c) ->
  48 <= c <= 57 ->
  0 <= jd <= 4999 ->
  18446603336221196288 <= np <= 18446744073709551615 ->
  exists fx' R' M', msteps RSEGS (st fx R 135124 M) (st fx' R' 135396 M')
    /\ (forall i, In i KS_A6 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (135152)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 10) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 11) = Z_to_bv 64 (10)
    /\ getr R' (reg 21) = Z_to_bv 64 (jd)
    /\ getr R' (reg 22) = Z_to_bv 64 (np)
    /\ getr R' (reg 24) = Z_to_bv 64 (c)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H18 H21 H22 H23 G2 G18 G21 G22 G40 K1 K2 K3 K4 K5 K6 K7.
  set (Vf := VAL_A6 R sp pj jd np c). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A6 R sp pj jd np c k) by (apply VAL_VZ_A6; lia). unfold VZ_A6 in ZA.
  assert (HR: regs_ok E PA6.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA6.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA6.kn0). { unfold know_ok, PA6.kn0. kn_allx ZA. }
  destruct (PA6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA6.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA6.regs0 PA6.regs_out 48 KS_A6 KS_A6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA6.regs_out E' R' 1 Hregs) by lia. rewrite ro_A6_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA6.regs_out E' R' 2 Hregs) by lia. rewrite ro_A6_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA6.regs_out E' R' 10 Hregs) by lia. rewrite ro_A6_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA6.regs_out E' R' 11 Hregs) by lia. rewrite ro_A6_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA6.regs_out E' R' 21 Hregs) by lia. rewrite ro_A6_21. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA6.regs_out E' R' 22 Hregs) by lia. rewrite ro_A6_22. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA6.regs_out E' R' 24 Hregs) by lia. rewrite ro_A6_24. L5KP.wordE' ZA Hag. }
  rewrite cells_A6 in Hcells.
  split. { intros x. apply Hfr. unfold PA6.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA7 := LibSegZ_pa7u.
Definition KS_A7 : list nat := Eval vm_compute in (BG.kept_list 48 PA7.regs0 PA7.regs_out).
Lemma KS_A7_ok : BG.kept_ok 48 PA7.regs0 PA7.regs_out KS_A7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A7_1 : nth 1 PA7.regs_out (ELit 0) = ELit 135164. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A7_2 : nth 2 PA7.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A7_10 : nth 10 PA7.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A7_11 : nth 11 PA7.regs_out (ELit 0) = EAlu Instr.ALU_AND (EVar 24) (ELit 15). Proof. vm_compute. reflexivity. Qed.
Lemma cells_A7 : SR.ps_cells PA7.ps0 = PA7.cells. Proof. reflexivity. Qed.
Definition VAL_A7 (R : bvmap 5 word) (sp : Z) (c : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 24%nat => Z_to_bv 64 c | _ => getr R (reg k) end.
Definition VZ_A7 (R : bvmap 5 word) (sp : Z) (c : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 24%nat => c | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A7 R sp c : 0 <= sp < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A7 R sp c) (fun _ => [])) k) = VZ_A7 R sp c k.
Proof.
  intros. cbn [ev]. unfold VAL_A7, VZ_A7.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa7u_conc fx R M sp c :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 24) = Z_to_bv 64 c ->
  0 <= sp < 2 ^ 64 ->
  0 <= c < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  48 <= c <= 57 ->
  exists fx' R' M', msteps RSEGS (st fx R 135152 M) (st fx' R' 135760 M')
    /\ (forall i, In i KS_A7 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (135164)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 10) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 11) = Z_to_bv 64 (c - 48)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H24 G2 G24 K1 K2 K3.
  set (Vf := VAL_A7 R sp c). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A7 R sp c k) by (apply VAL_VZ_A7; lia). unfold VZ_A7 in ZA.
  assert (HR: regs_ok E PA7.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA7.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA7.kn0). { unfold know_ok, PA7.kn0. kn_allx ZA. }
  destruct (PA7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA7.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA7.regs0 PA7.regs_out 48 KS_A7 KS_A7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA7.regs_out E' R' 1 Hregs) by lia. rewrite ro_A7_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA7.regs_out E' R' 2 Hregs) by lia. rewrite ro_A7_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA7.regs_out E' R' 10 Hregs) by lia. rewrite ro_A7_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA7.regs_out E' R' 11 Hregs) by lia. rewrite ro_A7_11. apply BG.word_of_unsigned. zc_eval ZA Hag. apply L5PA.land15_digit. lia. }
  rewrite cells_A7 in Hcells.
  split. { intros x. apply Hfr. unfold PA7.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA8H := LibSegZ_pa8hu.
Definition KS_A8H : list nat := Eval vm_compute in (BG.kept_list 48 PA8H.regs0 PA8H.regs_out).
Lemma KS_A8H_ok : BG.kept_ok 48 PA8H.regs0 PA8H.regs_out KS_A8H = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A8H_2 : nth 2 PA8H.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A8H_18 : nth 18 PA8H.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 18) (ELit 1). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A8H_20 : nth 20 PA8H.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 20) (ELit (-1)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A8H_21 : nth 21 PA8H.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 21) (ELit 1). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A8H_22 : nth 22 PA8H.regs_out (ELit 0) = EVar 22. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A8H : SR.ps_cells PA8H.ps0 = PA8H.cells. Proof. reflexivity. Qed.
Definition VAL_A8H (R : bvmap 5 word) (sp : Z) (pj : Z) (rj : Z) (jd : Z) (np : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 18%nat => Z_to_bv 64 pj | 20%nat => Z_to_bv 64 rj | 21%nat => Z_to_bv 64 jd | 22%nat => Z_to_bv 64 np | _ => getr R (reg k) end.
Definition VZ_A8H (R : bvmap 5 word) (sp : Z) (pj : Z) (rj : Z) (jd : Z) (np : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 18%nat => pj | 20%nat => rj | 21%nat => jd | 22%nat => np | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A8H R sp pj rj jd np : 0 <= sp < 2 ^ 64 -> 0 <= pj < 2 ^ 64 -> 0 <= rj < 2 ^ 64 -> 0 <= jd < 2 ^ 64 -> 0 <= np < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A8H R sp pj rj jd np) (fun _ => [])) k) = VZ_A8H R sp pj rj jd np k.
Proof.
  intros. cbn [ev]. unfold VAL_A8H, VZ_A8H.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa8hu_conc fx R M sp pj rj jd np :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 18) = Z_to_bv 64 pj ->
  getr R (reg 20) = Z_to_bv 64 rj ->
  getr R (reg 21) = Z_to_bv 64 jd ->
  getr R (reg 22) = Z_to_bv 64 np ->
  0 <= sp < 2 ^ 64 ->
  0 <= pj <= 281474976710656 ->
  0 <= rj < 2 ^ 64 ->
  0 <= jd <= 4999 ->
  18446603336221196288 <= np <= 18446744073709551615 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  2 <= rj <= 5000 ->
  0 <= jd <= 4999 ->
  18446603336221196288 <= np <= 18446744073709551615 ->
  exists fx' R' M', msteps RSEGS (st fx R 135164 M) (st fx' R' 135124 M')
    /\ (forall i, In i KS_A8H -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 18) = Z_to_bv 64 (pj + 1)
    /\ getr R' (reg 20) = Z_to_bv 64 (rj - 1)
    /\ getr R' (reg 21) = Z_to_bv 64 (jd + 1)
    /\ getr R' (reg 22) = Z_to_bv 64 (np)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H18 H20 H21 H22 G2 G18 G20 G21 G22 K1 K2 K3 K4 K5.
  set (Vf := VAL_A8H R sp pj rj jd np). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A8H R sp pj rj jd np k) by (apply VAL_VZ_A8H; lia). unfold VZ_A8H in ZA.
  assert (HR: regs_ok E PA8H.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA8H.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA8H.kn0). { unfold know_ok, PA8H.kn0. kn_allx ZA. }
  destruct (PA8H.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA8H.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA8H.regs0 PA8H.regs_out 48 KS_A8H KS_A8H_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA8H.regs_out E' R' 2 Hregs) by lia. rewrite ro_A8H_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA8H.regs_out E' R' 18 Hregs) by lia. rewrite ro_A8H_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA8H.regs_out E' R' 20 Hregs) by lia. rewrite ro_A8H_20. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA8H.regs_out E' R' 21 Hregs) by lia. rewrite ro_A8H_21. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA8H.regs_out E' R' 22 Hregs) by lia. rewrite ro_A8H_22. L5KP.wordE' ZA Hag. }
  rewrite cells_A8H in Hcells.
  split. { intros x. apply Hfr. unfold PA8H.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA8X := LibSegZ_pa8xu.
Definition KS_A8X : list nat := Eval vm_compute in (BG.kept_list 48 PA8X.regs0 PA8X.regs_out).
Lemma KS_A8X_ok : BG.kept_ok 48 PA8X.regs0 PA8X.regs_out KS_A8X = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A8X_2 : nth 2 PA8X.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A8X_18 : nth 18 PA8X.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 18) (ELit 1). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A8X_20 : nth 20 PA8X.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A8X_21 : nth 21 PA8X.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 21) (ELit 1). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A8X_22 : nth 22 PA8X.regs_out (ELit 0) = EVar 22. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A8X : SR.ps_cells PA8X.ps0 = PA8X.cells. Proof. reflexivity. Qed.
Definition VAL_A8X (R : bvmap 5 word) (sp : Z) (pj : Z) (jd : Z) (np : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 18%nat => Z_to_bv 64 pj | 21%nat => Z_to_bv 64 jd | 22%nat => Z_to_bv 64 np | 20%nat => Z_to_bv 64 1 | _ => getr R (reg k) end.
Definition VZ_A8X (R : bvmap 5 word) (sp : Z) (pj : Z) (jd : Z) (np : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 18%nat => pj | 21%nat => jd | 22%nat => np | 20%nat => 1 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A8X R sp pj jd np : 0 <= sp < 2 ^ 64 -> 0 <= pj < 2 ^ 64 -> 0 <= jd < 2 ^ 64 -> 0 <= np < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A8X R sp pj jd np) (fun _ => [])) k) = VZ_A8X R sp pj jd np k.
Proof.
  intros. cbn [ev]. unfold VAL_A8X, VZ_A8X.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa8xu_conc fx R M sp pj jd np :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 18) = Z_to_bv 64 pj ->
  getr R (reg 20) = Z_to_bv 64 (1) ->
  getr R (reg 21) = Z_to_bv 64 jd ->
  getr R (reg 22) = Z_to_bv 64 np ->
  0 <= sp < 2 ^ 64 ->
  0 <= pj <= 281474976710656 ->
  0 <= jd <= 4999 ->
  18446603336221196288 <= np <= 18446744073709551615 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  0 <= jd <= 4999 ->
  18446603336221196288 <= np <= 18446744073709551615 ->
  exists fx' R' M', msteps RSEGS (st fx R 135164 M) (st fx' R' 135180 M')
    /\ (forall i, In i KS_A8X -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 18) = Z_to_bv 64 (pj + 1)
    /\ getr R' (reg 20) = Z_to_bv 64 (0)
    /\ getr R' (reg 21) = Z_to_bv 64 (jd + 1)
    /\ getr R' (reg 22) = Z_to_bv 64 (np)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H18 H20 H21 H22 G2 G18 G21 G22 K1 K2 K3 K4.
  set (Vf := VAL_A8X R sp pj jd np). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A8X R sp pj jd np k) by (apply VAL_VZ_A8X; lia). unfold VZ_A8X in ZA.
  assert (HR: regs_ok E PA8X.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA8X.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA8X.kn0). { unfold know_ok, PA8X.kn0. kn_allx ZA. }
  destruct (PA8X.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA8X.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA8X.regs0 PA8X.regs_out 48 KS_A8X KS_A8X_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA8X.regs_out E' R' 2 Hregs) by lia. rewrite ro_A8X_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA8X.regs_out E' R' 18 Hregs) by lia. rewrite ro_A8X_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA8X.regs_out E' R' 20 Hregs) by lia. rewrite ro_A8X_20. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA8X.regs_out E' R' 21 Hregs) by lia. rewrite ro_A8X_21. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA8X.regs_out E' R' 22 Hregs) by lia. rewrite ro_A8X_22. L5KP.wordE' ZA Hag. }
  rewrite cells_A8X in Hcells.
  split. { intros x. apply Hfr. unfold PA8X.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA9P := LibSegZ_pa9pu.
Definition KS_A9P : list nat := Eval vm_compute in (BG.kept_list 48 PA9P.regs0 PA9P.regs_out).
Lemma KS_A9P_ok : BG.kept_ok 48 PA9P.regs0 PA9P.regs_out KS_A9P = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A9P_1 : nth 1 PA9P.regs_out (ELit 0) = ELit 135208. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A9P_2 : nth 2 PA9P.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A9P_10 : nth 10 PA9P.regs_out (ELit 0) = EVar 9. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A9P_11 : nth 11 PA9P.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma cells_A9P : SR.ps_cells PA9P.ps0 = PA9P.cells. Proof. reflexivity. Qed.
Definition VAL_A9P (R : bvmap 5 word) (sp : Z) (o : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 9%nat => Z_to_bv 64 o | 19%nat => Z_to_bv 64 0 | _ => getr R (reg k) end.
Definition VZ_A9P (R : bvmap 5 word) (sp : Z) (o : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 9%nat => o | 19%nat => 0 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A9P R sp o : 0 <= sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A9P R sp o) (fun _ => [])) k) = VZ_A9P R sp o k.
Proof.
  intros. cbn [ev]. unfold VAL_A9P, VZ_A9P.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa9pu_conc fx R M sp o :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 9) = Z_to_bv 64 o ->
  getr R (reg 19) = Z_to_bv 64 (0) ->
  0 <= sp < 2 ^ 64 ->
  0 <= o < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  exists fx' R' M', msteps RSEGS (st fx R 135180 M) (st fx' R' 136232 M')
    /\ (forall i, In i KS_A9P -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (135208)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 10) = Z_to_bv 64 (o)
    /\ getr R' (reg 11) = Z_to_bv 64 (sp - 112)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H9 H19 G2 G9 K1 K2.
  set (Vf := VAL_A9P R sp o). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A9P R sp o k) by (apply VAL_VZ_A9P; lia). unfold VZ_A9P in ZA.
  assert (HR: regs_ok E PA9P.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA9P.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA9P.kn0). { unfold know_ok, PA9P.kn0. kn_allx ZA. }
  destruct (PA9P.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA9P.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA9P.regs0 PA9P.regs_out 48 KS_A9P KS_A9P_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA9P.regs_out E' R' 1 Hregs) by lia. rewrite ro_A9P_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA9P.regs_out E' R' 2 Hregs) by lia. rewrite ro_A9P_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA9P.regs_out E' R' 10 Hregs) by lia. rewrite ro_A9P_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA9P.regs_out E' R' 11 Hregs) by lia. rewrite ro_A9P_11. L5KP.wordE' ZA Hag. }
  rewrite cells_A9P in Hcells.
  split. { intros x. apply Hfr. unfold PA9P.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA9N := LibSegZ_pa9nu.
Definition KS_A9N : list nat := Eval vm_compute in (BG.kept_list 48 PA9N.regs0 PA9N.regs_out).
Lemma KS_A9N_ok : BG.kept_ok 48 PA9N.regs0 PA9N.regs_out KS_A9N = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A9N_1 : nth 1 PA9N.regs_out (ELit 0) = ELit 135208. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A9N_2 : nth 2 PA9N.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A9N_10 : nth 10 PA9N.regs_out (ELit 0) = EVar 9. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A9N_11 : nth 11 PA9N.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma cells_A9N : SR.ps_cells PA9N.ps0 = PA9N.cells. Proof. reflexivity. Qed.
Definition VAL_A9N (R : bvmap 5 word) (sp : Z) (o : Z) (fbv : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 9%nat => Z_to_bv 64 o | 40%nat => Z_to_bv 64 fbv | 19%nat => Z_to_bv 64 1 | _ => getr R (reg k) end.
Definition VZ_A9N (R : bvmap 5 word) (sp : Z) (o : Z) (fbv : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 9%nat => o | 40%nat => fbv | 19%nat => 1 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A9N R sp o fbv : 0 <= sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= fbv < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A9N R sp o fbv) (fun _ => [])) k) = VZ_A9N R sp o fbv k.
Proof.
  intros. cbn [ev]. unfold VAL_A9N, VZ_A9N.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa9nu_conc fx R M sp o fbv :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 9) = Z_to_bv 64 o ->
  getr R (reg 19) = Z_to_bv 64 (1) ->
  0 <= sp < 2 ^ 64 ->
  0 <= o < 2 ^ 64 ->
  0 <= fbv < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 112) (1) ->
  L5.u8_at RSEGS M ((sp) - 112) (fbv) ->
  0 <= fbv <= 255 ->
  exists fx' R' M', msteps RSEGS (st fx R 135180 M) (st fx' R' 136232 M')
    /\ (forall i, In i KS_A9N -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (135208)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 10) = Z_to_bv 64 (o)
    /\ getr R' (reg 11) = Z_to_bv 64 (sp - 112)
    /\ L5.u8_at RSEGS M' ((sp) - 112) (Z.lor fbv 2)
    /\ (forall x : word, ~ ((sp) + -112 <= bv_unsigned x < (sp) + -112 + (1)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H9 H19 G2 G9 G40 K1 K2 K3 K4 K5.
  set (Vf := VAL_A9N R sp o fbv). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A9N R sp o fbv k) by (apply VAL_VZ_A9N; lia). unfold VZ_A9N in ZA.
  assert (HR: regs_ok E PA9N.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA9N.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA9N.kn0). { unfold know_ok, PA9N.kn0. kn_allx ZA. }
  destruct (PA9N.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA9N.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA9N.regs0 PA9N.regs_out 48 KS_A9N KS_A9N_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA9N.regs_out E' R' 1 Hregs) by lia. rewrite ro_A9N_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA9N.regs_out E' R' 2 Hregs) by lia. rewrite ro_A9N_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA9N.regs_out E' R' 10 Hregs) by lia. rewrite ro_A9N_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA9N.regs_out E' R' 11 Hregs) by lia. rewrite ro_A9N_11. L5KP.wordE' ZA Hag. }
  rewrite cells_A9N in Hcells.
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PA9N.cells, PA9N.cells0. left; reflexivity. L5KP.evalE' ZA Hag. zc_eval ZA Hag; apply L5PA.setbit1_eval; lia. apply L5PA.lor2_range; lia. }
  split. { intros x Hy0. apply Hfr. unfold PA9N.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA10I := LibSegZ_pa10iu.
Definition KS_A10I : list nat := Eval vm_compute in (BG.kept_list 48 PA10I.regs0 PA10I.regs_out).
Lemma KS_A10I_ok : BG.kept_ok 48 PA10I.regs0 PA10I.regs_out KS_A10I = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A10I_2 : nth 2 PA10I.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A10I_9 : nth 9 PA10I.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A10I : SR.ps_cells PA10I.ps0 = PA10I.cells. Proof. reflexivity. Qed.
Definition VAL_A10I (R : bvmap 5 word) (sp : Z) (fbv : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 40%nat => Z_to_bv 64 fbv | _ => getr R (reg k) end.
Definition VZ_A10I (R : bvmap 5 word) (sp : Z) (fbv : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 40%nat => fbv | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A10I R sp fbv : 0 <= sp < 2 ^ 64 -> 0 <= fbv < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A10I R sp fbv) (fun _ => [])) k) = VZ_A10I R sp fbv k.
Proof.
  intros. cbn [ev]. unfold VAL_A10I, VZ_A10I.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa10iu_conc fx R M sp fbv :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  0 <= sp < 2 ^ 64 ->
  0 <= fbv < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.u8_at RSEGS M ((sp) - 112) (fbv) ->
  0 <= fbv <= 255 ->
  0 <= (Z.land (fbv) (1)) <= 0 ->
  exists fx' R' M', msteps RSEGS (st fx R 135208 M) (st fx' R' 135244 M')
    /\ (forall i, In i KS_A10I -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 9) = Z_to_bv 64 (0)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 G2 G40 K1 K2 K3 K4 K5.
  set (Vf := VAL_A10I R sp fbv). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A10I R sp fbv k) by (apply VAL_VZ_A10I; lia). unfold VZ_A10I in ZA.
  assert (HR: regs_ok E PA10I.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA10I.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA10I.kn0). { unfold know_ok, PA10I.kn0. kn_allx ZA. }
  destruct (PA10I.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA10I.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA10I.regs0 PA10I.regs_out 48 KS_A10I KS_A10I_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA10I.regs_out E' R' 2 Hregs) by lia. rewrite ro_A10I_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA10I.regs_out E' R' 9 Hregs) by lia. rewrite ro_A10I_9. L5KP.wordE' ZA Hag. }
  rewrite cells_A10I in Hcells.
  split. { intros x. apply Hfr. unfold PA10I.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA10D := LibSegZ_pa10du.
Definition KS_A10D : list nat := Eval vm_compute in (BG.kept_list 48 PA10D.regs0 PA10D.regs_out).
Lemma KS_A10D_ok : BG.kept_ok 48 PA10D.regs0 PA10D.regs_out KS_A10D = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A10D_1 : nth 1 PA10D.regs_out (ELit 0) = ELit 135244. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A10D_2 : nth 2 PA10D.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A10D_9 : nth 9 PA10D.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A10D_10 : nth 10 PA10D.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A10D_11 : nth 11 PA10D.regs_out (ELit 0) = EMd Instr.M_MUL (ELit 8) (EVar 42). Proof. vm_compute. reflexivity. Qed.
Lemma cells_A10D : SR.ps_cells PA10D.ps0 = PA10D.cells. Proof. reflexivity. Qed.
Definition VAL_A10D (R : bvmap 5 word) (sp : Z) (fbv : Z) (q : Z) (cap : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 40%nat => Z_to_bv 64 fbv | 41%nat => Z_to_bv 64 q | 42%nat => Z_to_bv 64 cap | _ => getr R (reg k) end.
Definition VZ_A10D (R : bvmap 5 word) (sp : Z) (fbv : Z) (q : Z) (cap : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 40%nat => fbv | 41%nat => q | 42%nat => cap | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A10D R sp fbv q cap : 0 <= sp < 2 ^ 64 -> 0 <= fbv < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A10D R sp fbv q cap) (fun _ => [])) k) = VZ_A10D R sp fbv q cap k.
Proof.
  intros. cbn [ev]. unfold VAL_A10D, VZ_A10D.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa10du_conc fx R M sp fbv q cap :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  0 <= sp < 2 ^ 64 ->
  0 <= fbv < 2 ^ 64 ->
  0 <= q < 2 ^ 64 ->
  0 <= cap < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.u8_at RSEGS M ((sp) - 112) (fbv) ->
  0 <= fbv <= 255 ->
  1 <= (Z.land (fbv) (1)) <= 1 ->
  L5.u64_at RSEGS M ((sp) - 88) (q) ->
  4096 <= q <= 140737488355327 ->
  L5.u64_at RSEGS M ((sp) - 96) (cap) ->
  1 <= cap <= 134217728 ->
  exists fx' R' M', msteps RSEGS (st fx R 135208 M) (st fx' R' 259876 M')
    /\ (forall i, In i KS_A10D -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (135244)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 9) = Z_to_bv 64 (0)
    /\ getr R' (reg 10) = Z_to_bv 64 (q)
    /\ getr R' (reg 11) = Z_to_bv 64 (8 * cap)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 G2 G40 G41 G42 K1 K2 K3 K4 K5 K6 K7 K8 K9.
  set (Vf := VAL_A10D R sp fbv q cap). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A10D R sp fbv q cap k) by (apply VAL_VZ_A10D; lia). unfold VZ_A10D in ZA.
  assert (HR: regs_ok E PA10D.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA10D.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA10D.kn0). { unfold know_ok, PA10D.kn0. kn_allx ZA. }
  destruct (PA10D.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA10D.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA10D.regs0 PA10D.regs_out 48 KS_A10D KS_A10D_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA10D.regs_out E' R' 1 Hregs) by lia. rewrite ro_A10D_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA10D.regs_out E' R' 2 Hregs) by lia. rewrite ro_A10D_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA10D.regs_out E' R' 9 Hregs) by lia. rewrite ro_A10D_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA10D.regs_out E' R' 10 Hregs) by lia. rewrite ro_A10D_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA10D.regs_out E' R' 11 Hregs) by lia. rewrite ro_A10D_11. apply BG.word_of_unsigned. zc_eval ZA Hag. first [apply L5PA.shl3_eval | apply L5PA.shl3_eval']. lia. }
  rewrite cells_A10D in Hcells.
  split. { intros x. apply Hfr. unfold PA10D.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA11 := LibSegZ_pa11u.
Definition KS_A11 : list nat := Eval vm_compute in (BG.kept_list 56 PA11.regs0 PA11.regs_out).
Lemma KS_A11_ok : BG.kept_ok 56 PA11.regs0 PA11.regs_out KS_A11 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A11_1 : nth 1 PA11.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A11_2 : nth 2 PA11.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A11_8 : nth 8 PA11.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A11_9 : nth 9 PA11.regs_out (ELit 0) = EVar 43. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A11_10 : nth 10 PA11.regs_out (ELit 0) = EVar 8. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A11_11 : nth 11 PA11.regs_out (ELit 0) = EVar 9. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A11_18 : nth 18 PA11.regs_out (ELit 0) = EVar 44. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A11_19 : nth 19 PA11.regs_out (ELit 0) = EVar 45. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A11_20 : nth 20 PA11.regs_out (ELit 0) = EVar 46. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A11_21 : nth 21 PA11.regs_out (ELit 0) = EVar 47. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A11_22 : nth 22 PA11.regs_out (ELit 0) = EVar 48. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A11_23 : nth 23 PA11.regs_out (ELit 0) = EVar 49. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A11_24 : nth 24 PA11.regs_out (ELit 0) = EVar 50. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A11 : SR.ps_cells PA11.ps0 = PA11.cells. Proof. reflexivity. Qed.
Definition VAL_A11 (R : bvmap 5 word) (sp : Z) (x8 : Z) (x9 : Z) (c1 : Z) (c2 : Z) (c3 : Z) (c4 : Z) (c5 : Z) (c6 : Z) (c7 : Z) (c8 : Z) (c9 : Z) (c10 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 8%nat => Z_to_bv 64 x8 | 9%nat => Z_to_bv 64 x9 | 41%nat => Z_to_bv 64 c1 | 42%nat => Z_to_bv 64 c2 | 43%nat => Z_to_bv 64 c3 | 44%nat => Z_to_bv 64 c4 | 45%nat => Z_to_bv 64 c5 | 46%nat => Z_to_bv 64 c6 | 47%nat => Z_to_bv 64 c7 | 48%nat => Z_to_bv 64 c8 | 49%nat => Z_to_bv 64 c9 | 50%nat => Z_to_bv 64 c10 | _ => getr R (reg k) end.
Definition VZ_A11 (R : bvmap 5 word) (sp : Z) (x8 : Z) (x9 : Z) (c1 : Z) (c2 : Z) (c3 : Z) (c4 : Z) (c5 : Z) (c6 : Z) (c7 : Z) (c8 : Z) (c9 : Z) (c10 : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 8%nat => x8 | 9%nat => x9 | 41%nat => c1 | 42%nat => c2 | 43%nat => c3 | 44%nat => c4 | 45%nat => c5 | 46%nat => c6 | 47%nat => c7 | 48%nat => c8 | 49%nat => c9 | 50%nat => c10 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A11 R sp x8 x9 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : 0 <= sp < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= c1 < 2 ^ 64 -> 0 <= c2 < 2 ^ 64 -> 0 <= c3 < 2 ^ 64 -> 0 <= c4 < 2 ^ 64 -> 0 <= c5 < 2 ^ 64 -> 0 <= c6 < 2 ^ 64 -> 0 <= c7 < 2 ^ 64 -> 0 <= c8 < 2 ^ 64 -> 0 <= c9 < 2 ^ 64 -> 0 <= c10 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A11 R sp x8 x9 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10) (fun _ => [])) k) = VZ_A11 R sp x8 x9 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 k.
Proof.
  intros. cbn [ev]. unfold VAL_A11, VZ_A11.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa11u_conc fx R M sp x8 x9 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 8) = Z_to_bv 64 x8 ->
  getr R (reg 9) = Z_to_bv 64 x9 ->
  0 <= sp < 2 ^ 64 ->
  0 <= x8 < 2 ^ 64 ->
  0 <= x9 < 2 ^ 64 ->
  0 <= c1 < 2 ^ 64 ->
  0 <= c2 < 2 ^ 64 ->
  0 <= c3 < 2 ^ 64 ->
  0 <= c4 < 2 ^ 64 ->
  0 <= c5 < 2 ^ 64 ->
  0 <= c6 < 2 ^ 64 ->
  0 <= c7 < 2 ^ 64 ->
  0 <= c8 < 2 ^ 64 ->
  0 <= c9 < 2 ^ 64 ->
  0 <= c10 < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.u64_at RSEGS M ((sp) - 8) (c1) ->
  L5.u64_at RSEGS M ((sp) - 16) (c2) ->
  L5.u64_at RSEGS M ((sp) - 24) (c3) ->
  L5.u64_at RSEGS M ((sp) - 32) (c4) ->
  L5.u64_at RSEGS M ((sp) - 40) (c5) ->
  L5.u64_at RSEGS M ((sp) - 48) (c6) ->
  L5.u64_at RSEGS M ((sp) - 56) (c7) ->
  L5.u64_at RSEGS M ((sp) - 64) (c8) ->
  L5.u64_at RSEGS M ((sp) - 72) (c9) ->
  L5.u64_at RSEGS M ((sp) - 80) (c10) ->
  exists fx' R' M', msteps RSEGS (st fx R 135244 M) (st fx' R' 135296 M')
    /\ (forall i, In i KS_A11 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (c1)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp)
    /\ getr R' (reg 8) = Z_to_bv 64 (c2)
    /\ getr R' (reg 9) = Z_to_bv 64 (c3)
    /\ getr R' (reg 10) = Z_to_bv 64 (x8)
    /\ getr R' (reg 11) = Z_to_bv 64 (x9)
    /\ getr R' (reg 18) = Z_to_bv 64 (c4)
    /\ getr R' (reg 19) = Z_to_bv 64 (c5)
    /\ getr R' (reg 20) = Z_to_bv 64 (c6)
    /\ getr R' (reg 21) = Z_to_bv 64 (c7)
    /\ getr R' (reg 22) = Z_to_bv 64 (c8)
    /\ getr R' (reg 23) = Z_to_bv 64 (c9)
    /\ getr R' (reg 24) = Z_to_bv 64 (c10)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H8 H9 G2 G8 G9 G41 G42 G43 G44 G45 G46 G47 G48 G49 G50 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12.
  set (Vf := VAL_A11 R sp x8 x9 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A11 R sp x8 x9 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 k) by (apply VAL_VZ_A11; lia). unfold VZ_A11 in ZA.
  assert (HR: regs_ok E PA11.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA11.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA11.kn0). { unfold know_ok, PA11.kn0. kn_allx ZA. }
  destruct (PA11.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA11.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA11.regs0 PA11.regs_out 56 KS_A11 KS_A11_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA11.regs_out E' R' 1 Hregs) by lia. rewrite ro_A11_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA11.regs_out E' R' 2 Hregs) by lia. rewrite ro_A11_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA11.regs_out E' R' 8 Hregs) by lia. rewrite ro_A11_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA11.regs_out E' R' 9 Hregs) by lia. rewrite ro_A11_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA11.regs_out E' R' 10 Hregs) by lia. rewrite ro_A11_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA11.regs_out E' R' 11 Hregs) by lia. rewrite ro_A11_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA11.regs_out E' R' 18 Hregs) by lia. rewrite ro_A11_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA11.regs_out E' R' 19 Hregs) by lia. rewrite ro_A11_19. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA11.regs_out E' R' 20 Hregs) by lia. rewrite ro_A11_20. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA11.regs_out E' R' 21 Hregs) by lia. rewrite ro_A11_21. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA11.regs_out E' R' 22 Hregs) by lia. rewrite ro_A11_22. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA11.regs_out E' R' 23 Hregs) by lia. rewrite ro_A11_23. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA11.regs_out E' R' 24 Hregs) by lia. rewrite ro_A11_24. L5KP.wordE' ZA Hag. }
  rewrite cells_A11 in Hcells.
  split. { intros x. apply Hfr. unfold PA11.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA12I := LibSegZ_pa12iu.
Definition KS_A12I : list nat := Eval vm_compute in (BG.kept_list 48 PA12I.regs0 PA12I.regs_out).
Lemma KS_A12I_ok : BG.kept_ok 48 PA12I.regs0 PA12I.regs_out KS_A12I = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A12I_2 : nth 2 PA12I.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A12I_8 : nth 8 PA12I.regs_out (ELit 0) = EVar 18. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A12I_9 : nth 9 PA12I.regs_out (ELit 0) = ELit 22. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A12I : SR.ps_cells PA12I.ps0 = PA12I.cells. Proof. reflexivity. Qed.
Definition VAL_A12I (R : bvmap 5 word) (sp : Z) (pj : Z) (fbv : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 18%nat => Z_to_bv 64 pj | 40%nat => Z_to_bv 64 fbv | _ => getr R (reg k) end.
Definition VZ_A12I (R : bvmap 5 word) (sp : Z) (pj : Z) (fbv : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 18%nat => pj | 40%nat => fbv | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A12I R sp pj fbv : 0 <= sp < 2 ^ 64 -> 0 <= pj < 2 ^ 64 -> 0 <= fbv < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A12I R sp pj fbv) (fun _ => [])) k) = VZ_A12I R sp pj fbv k.
Proof.
  intros. cbn [ev]. unfold VAL_A12I, VZ_A12I.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa12iu_conc fx R M sp pj fbv :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 18) = Z_to_bv 64 pj ->
  0 <= sp < 2 ^ 64 ->
  0 <= pj <= 281474976710656 ->
  0 <= fbv < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.u8_at RSEGS M ((sp) - 112) (fbv) ->
  0 <= fbv <= 255 ->
  0 <= (Z.land (fbv) (1)) <= 0 ->
  exists fx' R' M', msteps RSEGS (st fx R 135300 M) (st fx' R' 135244 M')
    /\ (forall i, In i KS_A12I -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 8) = Z_to_bv 64 (pj)
    /\ getr R' (reg 9) = Z_to_bv 64 (22)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H18 G2 G18 G40 K1 K2 K3 K4 K5.
  set (Vf := VAL_A12I R sp pj fbv). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A12I R sp pj fbv k) by (apply VAL_VZ_A12I; lia). unfold VZ_A12I in ZA.
  assert (HR: regs_ok E PA12I.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA12I.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA12I.kn0). { unfold know_ok, PA12I.kn0. kn_allx ZA. }
  destruct (PA12I.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA12I.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA12I.regs0 PA12I.regs_out 48 KS_A12I KS_A12I_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA12I.regs_out E' R' 2 Hregs) by lia. rewrite ro_A12I_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA12I.regs_out E' R' 8 Hregs) by lia. rewrite ro_A12I_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA12I.regs_out E' R' 9 Hregs) by lia. rewrite ro_A12I_9. L5KP.wordE' ZA Hag. }
  rewrite cells_A12I in Hcells.
  split. { intros x. apply Hfr. unfold PA12I.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA12D := LibSegZ_pa12du.
Definition KS_A12D : list nat := Eval vm_compute in (BG.kept_list 48 PA12D.regs0 PA12D.regs_out).
Lemma KS_A12D_ok : BG.kept_ok 48 PA12D.regs0 PA12D.regs_out KS_A12D = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A12D_1 : nth 1 PA12D.regs_out (ELit 0) = ELit 135244. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A12D_2 : nth 2 PA12D.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A12D_8 : nth 8 PA12D.regs_out (ELit 0) = EVar 18. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A12D_9 : nth 9 PA12D.regs_out (ELit 0) = ELit 22. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A12D_10 : nth 10 PA12D.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A12D_11 : nth 11 PA12D.regs_out (ELit 0) = EMd Instr.M_MUL (ELit 8) (EVar 42). Proof. vm_compute. reflexivity. Qed.
Lemma cells_A12D : SR.ps_cells PA12D.ps0 = PA12D.cells. Proof. reflexivity. Qed.
Definition VAL_A12D (R : bvmap 5 word) (sp : Z) (pj : Z) (fbv : Z) (q : Z) (cap : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 18%nat => Z_to_bv 64 pj | 40%nat => Z_to_bv 64 fbv | 41%nat => Z_to_bv 64 q | 42%nat => Z_to_bv 64 cap | _ => getr R (reg k) end.
Definition VZ_A12D (R : bvmap 5 word) (sp : Z) (pj : Z) (fbv : Z) (q : Z) (cap : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 18%nat => pj | 40%nat => fbv | 41%nat => q | 42%nat => cap | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A12D R sp pj fbv q cap : 0 <= sp < 2 ^ 64 -> 0 <= pj < 2 ^ 64 -> 0 <= fbv < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A12D R sp pj fbv q cap) (fun _ => [])) k) = VZ_A12D R sp pj fbv q cap k.
Proof.
  intros. cbn [ev]. unfold VAL_A12D, VZ_A12D.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa12du_conc fx R M sp pj fbv q cap :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 18) = Z_to_bv 64 pj ->
  0 <= sp < 2 ^ 64 ->
  0 <= pj <= 281474976710656 ->
  0 <= fbv < 2 ^ 64 ->
  0 <= q < 2 ^ 64 ->
  0 <= cap < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.u8_at RSEGS M ((sp) - 112) (fbv) ->
  0 <= fbv <= 255 ->
  1 <= (Z.land (fbv) (1)) <= 1 ->
  L5.u64_at RSEGS M ((sp) - 88) (q) ->
  4096 <= q <= 140737488355327 ->
  L5.u64_at RSEGS M ((sp) - 96) (cap) ->
  1 <= cap <= 134217728 ->
  exists fx' R' M', msteps RSEGS (st fx R 135300 M) (st fx' R' 259876 M')
    /\ (forall i, In i KS_A12D -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (135244)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 8) = Z_to_bv 64 (pj)
    /\ getr R' (reg 9) = Z_to_bv 64 (22)
    /\ getr R' (reg 10) = Z_to_bv 64 (q)
    /\ getr R' (reg 11) = Z_to_bv 64 (8 * cap)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H18 G2 G18 G40 G41 G42 K1 K2 K3 K4 K5 K6 K7 K8 K9.
  set (Vf := VAL_A12D R sp pj fbv q cap). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A12D R sp pj fbv q cap k) by (apply VAL_VZ_A12D; lia). unfold VZ_A12D in ZA.
  assert (HR: regs_ok E PA12D.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA12D.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA12D.kn0). { unfold know_ok, PA12D.kn0. kn_allx ZA. }
  destruct (PA12D.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA12D.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA12D.regs0 PA12D.regs_out 48 KS_A12D KS_A12D_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA12D.regs_out E' R' 1 Hregs) by lia. rewrite ro_A12D_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA12D.regs_out E' R' 2 Hregs) by lia. rewrite ro_A12D_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA12D.regs_out E' R' 8 Hregs) by lia. rewrite ro_A12D_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA12D.regs_out E' R' 9 Hregs) by lia. rewrite ro_A12D_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA12D.regs_out E' R' 10 Hregs) by lia. rewrite ro_A12D_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA12D.regs_out E' R' 11 Hregs) by lia. rewrite ro_A12D_11. apply BG.word_of_unsigned. zc_eval ZA Hag. first [apply L5PA.shl3_eval | apply L5PA.shl3_eval']. lia. }
  rewrite cells_A12D in Hcells.
  split. { intros x. apply Hfr. unfold PA12D.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA13H := LibSegZ_pa13hu.
Definition KS_A13H : list nat := Eval vm_compute in (BG.kept_list 48 PA13H.regs0 PA13H.regs_out).
Lemma KS_A13H_ok : BG.kept_ok 48 PA13H.regs0 PA13H.regs_out KS_A13H = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A13H_2 : nth 2 PA13H.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A13H_18 : nth 18 PA13H.regs_out (ELit 0) = EVar 18. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A13H_20 : nth 20 PA13H.regs_out (ELit 0) = EVar 20. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A13H_21 : nth 21 PA13H.regs_out (ELit 0) = EVar 21. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A13H_22 : nth 22 PA13H.regs_out (ELit 0) = EVar 22. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A13H_24 : nth 24 PA13H.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A13H : SR.ps_cells PA13H.ps0 = PA13H.cells. Proof. reflexivity. Qed.
Definition VAL_A13H (R : bvmap 5 word) (sp : Z) (pj : Z) (jd : Z) (np : Z) (c : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 18%nat => Z_to_bv 64 pj | 21%nat => Z_to_bv 64 jd | 22%nat => Z_to_bv 64 np | 40%nat => Z_to_bv 64 c | 23%nat => Z_to_bv 64 9 | _ => getr R (reg k) end.
Definition VZ_A13H (R : bvmap 5 word) (sp : Z) (pj : Z) (jd : Z) (np : Z) (c : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 18%nat => pj | 21%nat => jd | 22%nat => np | 40%nat => c | 23%nat => 9 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A13H R sp pj jd np c : 0 <= sp < 2 ^ 64 -> 0 <= pj < 2 ^ 64 -> 0 <= jd < 2 ^ 64 -> 0 <= np < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A13H R sp pj jd np c) (fun _ => [])) k) = VZ_A13H R sp pj jd np c k.
Proof.
  intros. cbn [ev]. unfold VAL_A13H, VZ_A13H.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa13hu_conc fx R M sp pj jd np c :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 18) = Z_to_bv 64 pj ->
  getr R (reg 21) = Z_to_bv 64 jd ->
  getr R (reg 22) = Z_to_bv 64 np ->
  getr R (reg 23) = Z_to_bv 64 (9) ->
  0 <= sp < 2 ^ 64 ->
  0 <= pj <= 281474976710656 ->
  0 <= jd <= 4999 ->
  18446603336221196288 <= np <= 18446744073709551615 ->
  0 <= c < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  4096 <= pj <= 140737488355327 ->
  L5.u8_at RSEGS M (pj) (c) ->
  58 <= c <= 255 ->
  0 <= jd <= 4999 ->
  18446603336221196288 <= np <= 18446744073709551615 ->
  exists fx' R' M', msteps RSEGS (st fx R 135124 M) (st fx' R' 135300 M')
    /\ (forall i, In i KS_A13H -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 18) = Z_to_bv 64 (pj)
    /\ getr R' (reg 20) = getr R (reg 20)
    /\ getr R' (reg 21) = Z_to_bv 64 (jd)
    /\ getr R' (reg 22) = Z_to_bv 64 (np)
    /\ getr R' (reg 24) = Z_to_bv 64 (c)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H18 H21 H22 H23 G2 G18 G21 G22 G40 K1 K2 K3 K4 K5 K6 K7.
  set (Vf := VAL_A13H R sp pj jd np c). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A13H R sp pj jd np c k) by (apply VAL_VZ_A13H; lia). unfold VZ_A13H in ZA.
  assert (HR: regs_ok E PA13H.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA13H.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA13H.kn0). { unfold know_ok, PA13H.kn0. kn_allx ZA. }
  destruct (PA13H.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA13H.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA13H.regs0 PA13H.regs_out 48 KS_A13H KS_A13H_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA13H.regs_out E' R' 2 Hregs) by lia. rewrite ro_A13H_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA13H.regs_out E' R' 18 Hregs) by lia. rewrite ro_A13H_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA13H.regs_out E' R' 20 Hregs) by lia. rewrite ro_A13H_20. cbn [edenot]. rewrite <- (proj1 Hag 20%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PA13H.regs_out E' R' 21 Hregs) by lia. rewrite ro_A13H_21. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA13H.regs_out E' R' 22 Hregs) by lia. rewrite ro_A13H_22. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA13H.regs_out E' R' 24 Hregs) by lia. rewrite ro_A13H_24. L5KP.wordE' ZA Hag. }
  rewrite cells_A13H in Hcells.
  split. { intros x. apply Hfr. unfold PA13H.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA13L := LibSegZ_pa13lu.
Definition KS_A13L : list nat := Eval vm_compute in (BG.kept_list 48 PA13L.regs0 PA13L.regs_out).
Lemma KS_A13L_ok : BG.kept_ok 48 PA13L.regs0 PA13L.regs_out KS_A13L = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A13L_2 : nth 2 PA13L.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A13L_18 : nth 18 PA13L.regs_out (ELit 0) = EVar 18. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A13L_20 : nth 20 PA13L.regs_out (ELit 0) = EVar 20. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A13L_21 : nth 21 PA13L.regs_out (ELit 0) = EVar 21. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A13L_22 : nth 22 PA13L.regs_out (ELit 0) = EVar 22. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A13L_24 : nth 24 PA13L.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A13L : SR.ps_cells PA13L.ps0 = PA13L.cells. Proof. reflexivity. Qed.
Definition VAL_A13L (R : bvmap 5 word) (sp : Z) (pj : Z) (jd : Z) (np : Z) (c : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 18%nat => Z_to_bv 64 pj | 21%nat => Z_to_bv 64 jd | 22%nat => Z_to_bv 64 np | 40%nat => Z_to_bv 64 c | 23%nat => Z_to_bv 64 9 | _ => getr R (reg k) end.
Definition VZ_A13L (R : bvmap 5 word) (sp : Z) (pj : Z) (jd : Z) (np : Z) (c : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 18%nat => pj | 21%nat => jd | 22%nat => np | 40%nat => c | 23%nat => 9 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A13L R sp pj jd np c : 0 <= sp < 2 ^ 64 -> 0 <= pj < 2 ^ 64 -> 0 <= jd < 2 ^ 64 -> 0 <= np < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A13L R sp pj jd np c) (fun _ => [])) k) = VZ_A13L R sp pj jd np c k.
Proof.
  intros. cbn [ev]. unfold VAL_A13L, VZ_A13L.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pa13lu_conc fx R M sp pj jd np c :
  getr R (reg 2) = Z_to_bv 64 (sp - 112) ->
  getr R (reg 18) = Z_to_bv 64 pj ->
  getr R (reg 21) = Z_to_bv 64 jd ->
  getr R (reg 22) = Z_to_bv 64 np ->
  getr R (reg 23) = Z_to_bv 64 (9) ->
  0 <= sp < 2 ^ 64 ->
  0 <= pj <= 281474976710656 ->
  0 <= jd <= 4999 ->
  18446603336221196288 <= np <= 18446744073709551615 ->
  0 <= c < 2 ^ 64 ->
  140735332483184 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  4096 <= pj <= 140737488355327 ->
  L5.u8_at RSEGS M (pj) (c) ->
  0 <= c <= 47 ->
  0 <= jd <= 4999 ->
  18446603336221196288 <= np <= 18446744073709551615 ->
  exists fx' R' M', msteps RSEGS (st fx R 135124 M) (st fx' R' 135300 M')
    /\ (forall i, In i KS_A13L -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 112)
    /\ getr R' (reg 18) = Z_to_bv 64 (pj)
    /\ getr R' (reg 20) = getr R (reg 20)
    /\ getr R' (reg 21) = Z_to_bv 64 (jd)
    /\ getr R' (reg 22) = Z_to_bv 64 (np)
    /\ getr R' (reg 24) = Z_to_bv 64 (c)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H18 H21 H22 H23 G2 G18 G21 G22 G40 K1 K2 K3 K4 K5 K6 K7.
  set (Vf := VAL_A13L R sp pj jd np c). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A13L R sp pj jd np c k) by (apply VAL_VZ_A13L; lia). unfold VZ_A13L in ZA.
  assert (HR: regs_ok E PA13L.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA13L.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA13L.kn0). { unfold know_ok, PA13L.kn0. kn_allx ZA. }
  destruct (PA13L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA13L.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA13L.regs0 PA13L.regs_out 48 KS_A13L KS_A13L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA13L.regs_out E' R' 2 Hregs) by lia. rewrite ro_A13L_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA13L.regs_out E' R' 18 Hregs) by lia. rewrite ro_A13L_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA13L.regs_out E' R' 20 Hregs) by lia. rewrite ro_A13L_20. cbn [edenot]. rewrite <- (proj1 Hag 20%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PA13L.regs_out E' R' 21 Hregs) by lia. rewrite ro_A13L_21. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA13L.regs_out E' R' 22 Hregs) by lia. rewrite ro_A13L_22. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA13L.regs_out E' R' 24 Hregs) by lia. rewrite ro_A13L_24. L5KP.wordE' ZA Hag. }
  rewrite cells_A13L in Hcells.
  split. { intros x. apply Hfr. unfold PA13L.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

End L5DAU.
