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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5CstrAU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5CSAU.
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
Module PC1 := LibSegZ_pc1u.
Definition KS_C1 : list nat := Eval vm_compute in (BG.kept_list 48 PC1.regs0 PC1.regs_out).
Lemma KS_C1_ok : BG.kept_ok 48 PC1.regs0 PC1.regs_out KS_C1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_1 : nth 1 PC1.regs_out (ELit 0) = ELit 134048. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_2 : nth 2 PC1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_8 : nth 8 PC1.regs_out (ELit 0) = EVar 12. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_9 : nth 9 PC1.regs_out (ELit 0) = ELit 75691. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_10 : nth 10 PC1.regs_out (ELit 0) = ELit 75691. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_11 : nth 11 PC1.regs_out (ELit 0) = ELit 38. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_12 : nth 12 PC1.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_13 : nth 13 PC1.regs_out (ELit 0) = EVar 12. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_18 : nth 18 PC1.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma cells_C1 : SR.ps_cells PC1.ps0 = PC1.cells. Proof. reflexivity. Qed.
Definition VAL_C1 (R : bvmap 5 word) (sp : Z) (o : Z) (al : Z) (fbo : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 10%nat => Z_to_bv 64 o | 12%nat => Z_to_bv 64 al | 40%nat => Z_to_bv 64 fbo | _ => getr R (reg k) end.
Definition VZ_C1 (R : bvmap 5 word) (sp : Z) (o : Z) (al : Z) (fbo : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 10%nat => o | 12%nat => al | 40%nat => fbo | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_C1 R sp o al fbo : 0 <= sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= al < 2 ^ 64 -> 0 <= fbo < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_C1 R sp o al fbo) (fun _ => [])) k) = VZ_C1 R sp o al fbo k.
Proof.
  intros. cbn [ev]. unfold VAL_C1, VZ_C1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pc1u_conc fx R M sp o al fbo :
  getr R (reg 2) = Z_to_bv 64 sp ->
  getr R (reg 10) = Z_to_bv 64 o ->
  getr R (reg 11) = Z_to_bv 64 (75691) ->
  getr R (reg 12) = Z_to_bv 64 al ->
  0 <= sp < 2 ^ 64 ->
  0 <= o < 2 ^ 64 ->
  0 <= al < 2 ^ 64 ->
  0 <= fbo < 2 ^ 64 ->
  140735332483104 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 32) (32) ->
  L5.writable RSEGS M (o) (32) ->
  L5.u8_at RSEGS M (o) (fbo) ->
  0 <= fbo <= 255 ->
  140735332483072 <= o <= 140737488355327 ->
  (o) mod 8 = 0 ->
  ((sp) + -32 + (32) <= (o) + 0 \/ (o) + 0 + (32) <= (sp) + -32) ->
  L5.img_clear M 65536 131072 ->
  exists fx' R' M', msteps RSEGS (st fx R 133964 M) (st fx' R' 134720 M')
    /\ (forall i, In i KS_C1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (134048)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 32)
    /\ getr R' (reg 8) = Z_to_bv 64 (al)
    /\ getr R' (reg 9) = Z_to_bv 64 (75691)
    /\ getr R' (reg 10) = Z_to_bv 64 (75691)
    /\ getr R' (reg 11) = Z_to_bv 64 (38)
    /\ getr R' (reg 12) = Z_to_bv 64 (o)
    /\ getr R' (reg 13) = Z_to_bv 64 (al)
    /\ getr R' (reg 18) = Z_to_bv 64 (o)
    /\ L5.u64_at RSEGS M' ((o) + 24) (0)
    /\ L5.u64_at RSEGS M' ((o) + 16) (0)
    /\ L5.u64_at RSEGS M' ((o) + 8) (0)
    /\ L5.u8_at RSEGS M' ((o) + 0) (Z.land fbo 252)
    /\ L5.u64_at RSEGS M' ((sp) - 32) (bv_unsigned (getr R (reg 18)))
    /\ L5.u64_at RSEGS M' ((sp) - 24) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' ((sp) - 16) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' ((sp) - 8) (bv_unsigned (getr R (reg 1)))
    /\ (forall x : word, ~ ((sp) + -32 <= bv_unsigned x < (sp) + -32 + (32)) -> ~ ((o) + 0 <= bv_unsigned x < (o) + 0 + (32)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H10 H11 H12 G2 G10 G12 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10.
  set (Vf := VAL_C1 R sp o al fbo). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_C1 R sp o al fbo k) by (apply VAL_VZ_C1; lia). unfold VZ_C1 in ZA.
  assert (HR: regs_ok E PC1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PC1.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PC1.kn0). { unfold know_ok, PC1.kn0. kn_allx ZA. }
  destruct (PC1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PC1.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PC1.regs0 PC1.regs_out 48 KS_C1 KS_C1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 1 Hregs) by lia. rewrite ro_C1_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 2 Hregs) by lia. rewrite ro_C1_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 8 Hregs) by lia. rewrite ro_C1_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 9 Hregs) by lia. rewrite ro_C1_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 10 Hregs) by lia. rewrite ro_C1_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 11 Hregs) by lia. rewrite ro_C1_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 12 Hregs) by lia. rewrite ro_C1_12. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 13 Hregs) by lia. rewrite ro_C1_13. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 18 Hregs) by lia. rewrite ro_C1_18. L5KP.wordE' ZA Hag. }
  rewrite cells_C1 in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. zc_eval ZA Hag. rewrite ?Z.mod_small; [symmetry; apply L5PA.land252_div4; lia | rewrite L5PA.MM_val; lia]. apply L5PA.land252_range; lia. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1. apply Hfr. unfold PC1.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PC2 := LibSegZ_pc2u.
Definition KS_C2 : list nat := Eval vm_compute in (BG.kept_list 48 PC2.regs0 PC2.regs_out).
Lemma KS_C2_ok : BG.kept_ok 48 PC2.regs0 PC2.regs_out KS_C2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_1 : nth 1 PC2.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_2 : nth 2 PC2.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_8 : nth 8 PC2.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_9 : nth 9 PC2.regs_out (ELit 0) = EVar 43. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_18 : nth 18 PC2.regs_out (ELit 0) = EVar 44. Proof. vm_compute. reflexivity. Qed.
Lemma cells_C2 : SR.ps_cells PC2.ps0 = PC2.cells. Proof. reflexivity. Qed.
Definition VAL_C2 (R : bvmap 5 word) (sp : Z) (c1 : Z) (c2 : Z) (c3 : Z) (c4 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 41%nat => Z_to_bv 64 c1 | 42%nat => Z_to_bv 64 c2 | 43%nat => Z_to_bv 64 c3 | 44%nat => Z_to_bv 64 c4 | _ => getr R (reg k) end.
Definition VZ_C2 (R : bvmap 5 word) (sp : Z) (c1 : Z) (c2 : Z) (c3 : Z) (c4 : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 41%nat => c1 | 42%nat => c2 | 43%nat => c3 | 44%nat => c4 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_C2 R sp c1 c2 c3 c4 : 0 <= sp < 2 ^ 64 -> 0 <= c1 < 2 ^ 64 -> 0 <= c2 < 2 ^ 64 -> 0 <= c3 < 2 ^ 64 -> 0 <= c4 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_C2 R sp c1 c2 c3 c4) (fun _ => [])) k) = VZ_C2 R sp c1 c2 c3 c4 k.
Proof.
  intros. cbn [ev]. unfold VAL_C2, VZ_C2.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pc2u_conc fx R M sp c1 c2 c3 c4 :
  getr R (reg 2) = Z_to_bv 64 (sp - 32) ->
  getr R (reg 11) = Z_to_bv 64 (0) ->
  0 <= sp < 2 ^ 64 ->
  0 <= c1 < 2 ^ 64 ->
  0 <= c2 < 2 ^ 64 ->
  0 <= c3 < 2 ^ 64 ->
  0 <= c4 < 2 ^ 64 ->
  140735332483104 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.u64_at RSEGS M ((sp) - 8) (c1) ->
  L5.u64_at RSEGS M ((sp) - 16) (c2) ->
  L5.u64_at RSEGS M ((sp) - 24) (c3) ->
  L5.u64_at RSEGS M ((sp) - 32) (c4) ->
  exists fx' R' M', msteps RSEGS (st fx R 134048 M) (st fx' R' 134076 M')
    /\ (forall i, In i KS_C2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (c1)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp)
    /\ getr R' (reg 8) = Z_to_bv 64 (c2)
    /\ getr R' (reg 9) = Z_to_bv 64 (c3)
    /\ getr R' (reg 18) = Z_to_bv 64 (c4)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H11 G2 G41 G42 G43 G44 K1 K2 K3 K4 K5 K6.
  set (Vf := VAL_C2 R sp c1 c2 c3 c4). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_C2 R sp c1 c2 c3 c4 k) by (apply VAL_VZ_C2; lia). unfold VZ_C2 in ZA.
  assert (HR: regs_ok E PC2.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PC2.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PC2.kn0). { unfold know_ok, PC2.kn0. kn_allx ZA. }
  destruct (PC2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PC2.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PC2.regs0 PC2.regs_out 48 KS_C2 KS_C2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 1 Hregs) by lia. rewrite ro_C2_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 2 Hregs) by lia. rewrite ro_C2_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 8 Hregs) by lia. rewrite ro_C2_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 9 Hregs) by lia. rewrite ro_C2_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 18 Hregs) by lia. rewrite ro_C2_18. L5KP.wordE' ZA Hag. }
  rewrite cells_C2 in Hcells.
  split. { intros x. apply Hfr. unfold PC2.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

End L5CSAU.
