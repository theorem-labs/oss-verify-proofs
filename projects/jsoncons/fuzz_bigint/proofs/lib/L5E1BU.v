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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5E1BU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_e1tu_v0.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5E1BU.
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
Module PC1 := LibSegZ_e1c1u.
Definition KS_C1 : list nat := Eval vm_compute in (BG.kept_list 56 PC1.regs0 PC1.regs_out).
Lemma KS_C1_ok : BG.kept_ok 56 PC1.regs0 PC1.regs_out KS_C1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_1 : nth 1 PC1.regs_out (ELit 0) = ELit 371656. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_2 : nth 2 PC1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-128)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_8 : nth 8 PC1.regs_out (ELit 0) = ELit 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_9 : nth 9 PC1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-55)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_10 : nth 10 PC1.regs_out (ELit 0) = ELit 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_18 : nth 18 PC1.regs_out (ELit 0) = ELit 16. Proof. vm_compute. reflexivity. Qed.
Lemma cells_C1 : SR.ps_cells PC1.ps0 = PC1.cells. Proof. reflexivity. Qed.
Definition VAL_C1 (R : bvmap 5 word) (csp : Z) (obj : Z) (errn : Z) (d40 : Z) (d41 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 35%nat => Z_to_bv 64 errn | 40%nat => Z_to_bv 64 d40 | 41%nat => Z_to_bv 64 d41 | _ => getr R (reg k) end.
Definition VZ_C1 (R : bvmap 5 word) (csp : Z) (obj : Z) (errn : Z) (d40 : Z) (d41 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 35%nat => errn | 40%nat => d40 | 41%nat => d41 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_C1 R csp obj errn d40 d41 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= errn < 2 ^ 64 -> 0 <= d40 < 2 ^ 64 -> 0 <= d41 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_C1 R csp obj errn d40 d41) (fun _ => [])) k) = VZ_C1 R csp obj errn d40 d41 k.
Proof.
  intros. cbn [ev]. unfold VAL_C1, VZ_C1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e1c1u_conc fx R M csp obj errn d40 d41 :
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 10) = Z_to_bv 64 obj ->
  getr R (reg 11) = Z_to_bv 64 (22) ->
  getr R (reg 12) = Z_to_bv 64 (393560) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= errn < 2 ^ 64 ->
  0 <= d40 < 2 ^ 64 ->
  0 <= d41 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 1280) (1280) ->
  L5.defined M ((csp) - 1280) (1280) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (160) ->
  L5.defined M ((obj) - 128) (160) ->
  ((csp) + -1280 + (1280) <= (obj) + -128 \/ (obj) + -128 + (160) <= (csp) + -1280) ->
  ((obj) + -128 + (160) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u32_at RSEGS M ((0) + 462484) (errn) ->
  L5.writable RSEGS M ((0) + 462484) (4) ->
  L5.u64_at RSEGS M ((0) + 462600) (594432) ->
  L5.u64_at RSEGS M ((0) + 594472) (0) ->
  L5.u64_at RSEGS M ((csp) - 1152) (d40) ->
  L5.u64_at RSEGS M ((csp) - 40) (d41) ->
  exists fx' R' M', msteps RSEGS (st fx R 134324 M) (st fx' R' 312384 M')
    /\ (forall i, In i KS_C1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (371656)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp - 128)
    /\ getr R' (reg 8) = Z_to_bv 64 (41)
    /\ getr R' (reg 9) = Z_to_bv 64 (csp - 55)
    /\ getr R' (reg 10) = Z_to_bv 64 (41)
    /\ getr R' (reg 18) = Z_to_bv 64 (16)
    /\ L5.u64_at RSEGS M' ((csp) - 128) (obj)
    /\ L5.u64_at RSEGS M' ((csp) - 120) (266272)
    /\ L5.u64_at RSEGS M' ((obj) + 0) (387952)
    /\ L5.u64_at RSEGS M' ((csp) - 104) (bv_unsigned (getr R (reg 19)))
    /\ L5.u64_at RSEGS M' ((csp) - 96) (22)
    /\ L5.u64_at RSEGS M' ((csp) - 88) (obj)
    /\ L5.u64_at RSEGS M' ((csp) - 80) (393560)
    /\ L5.u64_at RSEGS M' ((csp) - 72) (269780)
    /\ L5.u8_at RSEGS M' ((csp) - 39) (0)
    /\ L5.u64_at RSEGS M' ((csp) - 55) (2334106421097295433)
    /\ L5.u64_at RSEGS M' ((csp) - 47) (8389754676633367137)
    /\ L5.u8_at RSEGS M' ((csp) - 56) (32)
    /\ L5.u64_at RSEGS M' ((csp) - 112) (393560)
    /\ L5.u64_at RSEGS M' ((csp) - 32) (bv_unsigned (getr R (reg 18)))
    /\ L5.u64_at RSEGS M' ((csp) - 24) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' ((csp) - 16) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' ((csp) - 8) (134328)
    /\ (forall x : word, ~ ((csp) + -1280 <= bv_unsigned x < (csp) + -1280 + (1280)) -> ~ ((obj) + 0 <= bv_unsigned x < (obj) + 0 + (8)) -> ~ ((0) + 462484 <= bv_unsigned x < (0) + 462484 + (4)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 H11 H12 G2 G10 G35 G40 G41 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19.
  set (Vf := VAL_C1 R csp obj errn d40 d41). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_C1 R csp obj errn d40 d41 k) by (apply VAL_VZ_C1; lia). unfold VZ_C1 in ZA.
  assert (HR: regs_ok E PC1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PC1.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PC1.kn0). { unfold know_ok, PC1.kn0. kn_allx ZA. }
  destruct (PC1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PC1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PC1.regs0 PC1.regs_out 56 KS_C1 KS_C1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 1 Hregs) by lia. rewrite ro_C1_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 2 Hregs) by lia. rewrite ro_C1_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 8 Hregs) by lia. rewrite ro_C1_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 9 Hregs) by lia. rewrite ro_C1_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 10 Hregs) by lia. rewrite ro_C1_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC1.regs_out E' R' 18 Hregs) by lia. rewrite ro_C1_18. L5KP.wordE' ZA Hag. }
  rewrite cells_C1 in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC1.cells, PC1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1 Hy2. apply Hfr. unfold PC1.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PC2 := LibSegZ_e1c2u.
Definition KS_C2 : list nat := Eval vm_compute in (BG.kept_list 56 PC2.regs0 PC2.regs_out).
Lemma KS_C2_ok : BG.kept_ok 56 PC2.regs0 PC2.regs_out KS_C2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_1 : nth 1 PC2.regs_out (ELit 0) = ELit 134328. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_2 : nth 2 PC2.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_8 : nth 8 PC2.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_9 : nth 9 PC2.regs_out (ELit 0) = ELit 22. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_10 : nth 10 PC2.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_11 : nth 11 PC2.regs_out (ELit 0) = ELit 388648. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_12 : nth 12 PC2.regs_out (ELit 0) = ELit 269892. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_18 : nth 18 PC2.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_19 : nth 19 PC2.regs_out (ELit 0) = EVar 19. Proof. vm_compute. reflexivity. Qed.
Lemma cells_C2 : SR.ps_cells PC2.ps0 = PC2.cells. Proof. reflexivity. Qed.
Definition VAL_C2 (R : bvmap 5 word) (csp : Z) (obj : Z) (ref : Z) (x41 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 37%nat => Z_to_bv 64 ref | 41%nat => Z_to_bv 64 x41 | _ => getr R (reg k) end.
Definition VZ_C2 (R : bvmap 5 word) (csp : Z) (obj : Z) (ref : Z) (x41 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 37%nat => ref | 41%nat => x41 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_C2 R csp obj ref x41 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= ref < 2 ^ 64 -> 0 <= x41 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_C2 R csp obj ref x41) (fun _ => [])) k) = VZ_C2 R csp obj ref x41 k.
Proof.
  intros. cbn [ev]. unfold VAL_C2, VZ_C2.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e1c2u_conc fx R M csp obj ref x41 :
  getr R (reg 2) = Z_to_bv 64 (csp - 128) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 9) = Z_to_bv 64 (csp - 55) ->
  getr R (reg 10) = Z_to_bv 64 (ref) ->
  getr R (reg 18) = Z_to_bv 64 (16) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= ref < 2 ^ 64 ->
  0 <= x41 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 192) (64) ->
  L5.defined M ((csp) - 192) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (160) ->
  L5.defined M ((obj) - 128) (160) ->
  4096 <= ref <= 140737488355328 ->
  (ref) mod 16 = 0 ->
  L5.writable RSEGS M (ref) (41) ->
  L5.defined M (ref) (41) ->
  ((csp) + -192 + (192) <= (obj) + -128 \/ (obj) + -128 + (160) <= (csp) + -192) ->
  ((obj) + -128 + (160) <= (ref) + 0 \/ (ref) + 0 + (41) <= (obj) + -128) ->
  ((csp) + -192 + (192) <= (ref) + 0 \/ (ref) + 0 + (41) <= (csp) + -192) ->
  ((obj) + -128 + (160) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  ((ref) + 0 + (41) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (ref) + 0) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u64_at RSEGS M ((csp) - 120) (266272) ->
  L5.u64_at RSEGS M ((csp) - 128) (obj) ->
  L5.u64_at RSEGS M ((csp) - 56) (7235433442201979168) ->
  L5.u64_at RSEGS M ((csp) - 48) (7954884667833999648) ->
  L5KP.uw_at RSEGS 2 M ((csp) - 40) (116) ->
  L5.u64_at RSEGS M ((csp) - 72) (269780) ->
  L5.u64_at RSEGS M ((csp) - 80) (393560) ->
  L5.u64_at RSEGS M ((csp) - 88) (obj) ->
  L5.u64_at RSEGS M ((csp) - 96) (22) ->
  L5.u64_at RSEGS M ((csp) - 104) (bv_unsigned (getr R (reg 19))) ->
  L5.u64_at RSEGS M ((csp) - 8) (134328) ->
  L5.u64_at RSEGS M ((csp) - 16) (obj) ->
  L5.u64_at RSEGS M ((csp) - 24) (22) ->
  L5.u64_at RSEGS M ((csp) - 32) (x41) ->
  exists fx' R' M', msteps RSEGS (st fx R 371656 M) (st fx' R' 134348 M')
    /\ (forall i, In i KS_C2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (134328)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj)
    /\ getr R' (reg 9) = Z_to_bv 64 (22)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj)
    /\ getr R' (reg 11) = Z_to_bv 64 (388648)
    /\ getr R' (reg 12) = Z_to_bv 64 (269892)
    /\ getr R' (reg 18) = Z_to_bv 64 (x41)
    /\ getr R' (reg 19) = getr R (reg 19)
    /\ L5.u64_at RSEGS M' ((obj) + 24) (393560)
    /\ L5.u32_at RSEGS M' ((obj) + 16) (22)
    /\ L5.u64_at RSEGS M' ((obj) + 0) (388624)
    /\ L5.u64_at RSEGS M' ((obj) + 8) (ref + 24)
    /\ L5.u64_at RSEGS M' ((ref) + 24) (2334106421097295433)
    /\ L5.u64_at RSEGS M' ((ref) + 32) (8389754676633367137)
    /\ L5.u8_at RSEGS M' ((ref) + 40) (0)
    /\ L5.u32_at RSEGS M' ((ref) + 16) (0)
    /\ L5.u64_at RSEGS M' ((ref) + 8) (16)
    /\ L5.u64_at RSEGS M' ((ref) + 0) (16)
    /\ (forall x : word, ~ ((csp) + -192 <= bv_unsigned x < (csp) + -192 + (64)) -> ~ ((obj) + 0 <= bv_unsigned x < (obj) + 0 + (32)) -> ~ ((ref) + 0 <= bv_unsigned x < (ref) + 0 + (41)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H9 H10 H18 G2 G10 G37 G41 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34.
  set (Vf := VAL_C2 R csp obj ref x41). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_C2 R csp obj ref x41 k) by (apply VAL_VZ_C2; lia). unfold VZ_C2 in ZA.
  assert (HR: regs_ok E PC2.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PC2.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PC2.kn0). { unfold know_ok, PC2.kn0. kn_allx ZA. }
  destruct (PC2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PC2.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PC2.regs0 PC2.regs_out 56 KS_C2 KS_C2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 1 Hregs) by lia. rewrite ro_C2_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 2 Hregs) by lia. rewrite ro_C2_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 8 Hregs) by lia. rewrite ro_C2_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 9 Hregs) by lia. rewrite ro_C2_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 10 Hregs) by lia. rewrite ro_C2_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 11 Hregs) by lia. rewrite ro_C2_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 12 Hregs) by lia. rewrite ro_C2_12. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 18 Hregs) by lia. rewrite ro_C2_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 19 Hregs) by lia. rewrite ro_C2_19. cbn [edenot]. rewrite <- (proj1 Hag 19%nat) by lia. reflexivity. }
  rewrite cells_C2 in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.uw_of_KWordw. apply Hcells. unfold PC2.cells, PC2.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.uw_of_KWordw. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1 Hy2. apply Hfr. unfold PC2.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PT0 := LibSegZ_e1tu_v0.
Definition KS_T0 : list nat := Eval vm_compute in (BG.kept_list 56 PT0.regs0 PT0.regs_out).
Lemma KS_T0_ok : BG.kept_ok 56 PT0.regs0 PT0.regs_out KS_T0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T0_1 : nth 1 PT0.regs_out (ELit 0) = ELit 133644. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T0_2 : nth 2 PT0.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 32). Proof. vm_compute. reflexivity. Qed.
Lemma ro_T0_8 : nth 8 PT0.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T0_9 : nth 9 PT0.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T0_10 : nth 10 PT0.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_T0_11 : nth 11 PT0.regs_out (ELit 0) = ELit 1. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T0_12 : nth 12 PT0.regs_out (ELit 0) = ELit 260436. Proof. vm_compute. reflexivity. Qed.
Lemma cells_T0 : SR.ps_cells PT0.ps0 = PT0.cells. Proof. reflexivity. Qed.
Definition VAL_T0 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (s0v : Z) (s1v : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 32%nat => Z_to_bv 64 av | 33%nat => Z_to_bv 64 canary | 34%nat => Z_to_bv 64 uid | 36%nat => Z_to_bv 64 rnd | 39%nat => Z_to_bv 64 hw | 40%nat => Z_to_bv 64 s0v | 41%nat => Z_to_bv 64 s1v | _ => getr R (reg k) end.
Definition VZ_T0 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (s0v : Z) (s1v : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | 40%nat => s0v | 41%nat => s1v | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_T0 R csp obj av canary uid rnd hw s0v s1v : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= av < 2 ^ 64 -> 0 <= canary < 2 ^ 64 -> 0 <= uid < 2 ^ 64 -> 0 <= rnd < 2 ^ 64 -> 0 <= hw < 2 ^ 64 -> 0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_T0 R csp obj av canary uid rnd hw s0v s1v) (fun _ => [])) k) = VZ_T0 R csp obj av canary uid rnd hw s0v s1v k.
Proof.
  intros. cbn [ev]. unfold VAL_T0, VZ_T0.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e1tu_v0_conc fx R M csp obj av canary uid rnd hw s0v s1v :
  getr R (reg 1) = Z_to_bv 64 (134328) ->
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 10) = Z_to_bv 64 obj ->
  getr R (reg 11) = Z_to_bv 64 (388648) ->
  getr R (reg 12) = Z_to_bv 64 (269892) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= av < 2 ^ 64 ->
  0 <= canary < 2 ^ 64 ->
  0 <= uid < 2 ^ 64 ->
  0 <= rnd < 2 ^ 64 ->
  0 <= hw < 2 ^ 64 ->
  0 <= s0v < 2 ^ 64 ->
  0 <= s1v < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 7984) (7984) ->
  L5.defined M ((csp) - 7984) (7984) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (160) ->
  L5.defined M ((obj) - 128) (160) ->
  1099511627776 <= av <= 140737488355328 ->
  (av) mod 8 = 0 ->
  ((csp) + -7984 + (8016) <= (obj) + -128 \/ (obj) + -128 + (160) <= (csp) + -7984) ->
  ((obj) + -128 + (160) <= (av) + 0 \/ (av) + 0 + (160) <= (obj) + -128) ->
  ((csp) + -7984 + (8016) <= (av) + 0 \/ (av) + 0 + (160) <= (csp) + -7984) ->
  ((obj) + -128 + (160) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u32_at RSEGS M ((0) + 459776) (0) ->
  L5.u64_at RSEGS M ((0) + 594344) (canary) ->
  L5.u64_at RSEGS M ((0) + 594384) (av) ->
  L5.u64_at RSEGS M (av) (3) ->
  L5.u64_at RSEGS M ((av) + 8) (65600) ->
  L5.u64_at RSEGS M ((av) + 16) (4) ->
  L5.u64_at RSEGS M ((av) + 24) (56) ->
  L5.u64_at RSEGS M ((av) + 32) (5) ->
  L5.u64_at RSEGS M ((av) + 40) (10) ->
  L5.u64_at RSEGS M ((av) + 48) (16) ->
  L5.u64_at RSEGS M ((av) + 56) (hw) ->
  L5.u64_at RSEGS M ((av) + 64) (6) ->
  L5.u64_at RSEGS M ((av) + 72) (4096) ->
  L5.u64_at RSEGS M ((av) + 80) (11) ->
  L5.u64_at RSEGS M ((av) + 88) (uid) ->
  L5.u64_at RSEGS M ((av) + 96) (12) ->
  L5.u64_at RSEGS M ((av) + 104) (uid) ->
  L5.u64_at RSEGS M ((av) + 112) (23) ->
  L5.u64_at RSEGS M ((av) + 120) (0) ->
  L5.u64_at RSEGS M ((av) + 128) (25) ->
  L5.u64_at RSEGS M ((av) + 136) (rnd) ->
  L5.u64_at RSEGS M ((av) + 144) (0) ->
  L5.u64_at RSEGS M ((csp) + 24) (133176) ->
  L5.u64_at RSEGS M ((csp) + 16) (s0v) ->
  L5.u64_at RSEGS M ((csp) + 8) (s1v) ->
  L5.u8_at RSEGS M ((0) + 462433) (0) ->
  L5.u8_at RSEGS M ((0) + 462435) (0) ->
  L5.u8_at RSEGS M ((0) + 462437) (0) ->
  L5.writable RSEGS M ((0) + 462433) (6) ->
  L5.writable RSEGS M ((0) + 459776) (4) ->
  exists fx' R' M', msteps RSEGS (st fx R 134348 M) (st fx' R' 133644 M')
    /\ (forall i, In i KS_T0 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (133644)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 32)
    /\ getr R' (reg 8) = Z_to_bv 64 (s0v)
    /\ getr R' (reg 9) = Z_to_bv 64 (s1v)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = Z_to_bv 64 (1)
    /\ getr R' (reg 12) = Z_to_bv 64 (260436)
    /\ L5.u64_at RSEGS M' ((obj) - 8) (csp + 32)
    /\ L5.u64_at RSEGS M' ((obj) - 40) (obj)
    /\ L5.u64_at RSEGS M' ((obj) - 48) (133644)
    /\ L5.u64_at RSEGS M' ((obj) - 56) (91856)
    /\ L5.u64_at RSEGS M' ((obj) - 64) (91995)
    /\ L5.u32_at RSEGS M' ((obj) - 68) (1)
    /\ L5.u8_at RSEGS M' ((0) + 462436) (0)
    /\ L5.u8_at RSEGS M' ((0) + 462435) (1)
    /\ L5.u8_at RSEGS M' ((0) + 462438) (0)
    /\ L5.u8_at RSEGS M' ((0) + 462437) (1)
    /\ L5.u64_at RSEGS M' ((obj) - 16) (0)
    /\ L5.u8_at RSEGS M' ((0) + 462434) (0)
    /\ L5.u8_at RSEGS M' ((0) + 462433) (1)
    /\ L5.u64_at RSEGS M' ((obj) - 120) (1)
    /\ L5.u64_at RSEGS M' ((obj) - 24) (260436)
    /\ L5.u64_at RSEGS M' ((obj) - 32) (4849336966747728640)
    /\ L5.u64_at RSEGS M' ((obj) - 88) (145512)
    /\ L5.u64_at RSEGS M' ((obj) - 104) (269892)
    /\ L5.u64_at RSEGS M' ((obj) - 112) (388648)
    /\ L5.u64_at RSEGS M' ((obj) - 96) (145780)
    /\ L5.u32_at RSEGS M' ((0) + 459776) (1)
    /\ (forall x : word, ~ ((csp) + -7984 <= bv_unsigned x < (csp) + -7984 + (7984)) -> ~ ((obj) + -120 <= bv_unsigned x < (obj) + -120 + (40)) -> ~ ((obj) + -68 <= bv_unsigned x < (obj) + -68 + (68)) -> ~ ((0) + 459776 <= bv_unsigned x < (0) + 459776 + (4)) -> ~ ((0) + 462433 <= bv_unsigned x < (0) + 462433 + (6)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H1 H2 H3 H4 H10 H11 H12 G2 G10 G32 G33 G34 G36 G39 G40 G41 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47.
  set (Vf := VAL_T0 R csp obj av canary uid rnd hw s0v s1v). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_T0 R csp obj av canary uid rnd hw s0v s1v k) by (apply VAL_VZ_T0; lia). unfold VZ_T0 in ZA.
  assert (HR: regs_ok E PT0.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PT0.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PT0.kn0). { unfold know_ok, PT0.kn0. kn_allx ZA. }
  destruct (PT0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PT0.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PT0.regs0 PT0.regs_out 56 KS_T0 KS_T0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PT0.regs_out E' R' 1 Hregs) by lia. rewrite ro_T0_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT0.regs_out E' R' 2 Hregs) by lia. rewrite ro_T0_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT0.regs_out E' R' 8 Hregs) by lia. rewrite ro_T0_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT0.regs_out E' R' 9 Hregs) by lia. rewrite ro_T0_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT0.regs_out E' R' 10 Hregs) by lia. rewrite ro_T0_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT0.regs_out E' R' 11 Hregs) by lia. rewrite ro_T0_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT0.regs_out E' R' 12 Hregs) by lia. rewrite ro_T0_12. L5KP.wordE' ZA Hag. }
  rewrite cells_T0 in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT0.cells, PT0.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT0.cells, PT0.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.uw_of_KWordw. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.uw_of_KWordw. apply Hcells. unfold PT0.cells, PT0.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1 Hy2 Hy3 Hy4. apply Hfr. unfold PT0.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

End L5E1BU.
