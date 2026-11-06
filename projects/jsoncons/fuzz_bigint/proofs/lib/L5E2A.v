(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue BigLinkInlBase BigModel BigFactsRun BigFactsDigits L5Defs L5KnP L5ParseArith.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5E2A.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5E2A.
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).

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
Ltac land_rng := first [ lia | apply L5.land_byte_range; lia ].
Ltac zc_eval0r ZA := zc_eval0 ZA; cbn beta iota; reflexivity.
Ltac kn1x ZA := first [ L5KP.kn1 ZA
  | lazymatch goal with
    | |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5KP.kentry_KRange; [zc_eval0r ZA | lia]
    | |- kentry_ok _ _ _ (KWord _ 8 _) => eapply L5KP.kentry_KWord8; [L5KP.evalE ZA | zc_eval0r ZA | lia | lia | L5KP.kn_mem]
    | |- kentry_ok _ _ _ (KWord _ 1 _) => eapply L5KP.kentry_KWord1; [L5KP.evalE ZA | zc_eval0r ZA | lia | lia | land_rng | L5KP.kn_mem]
    end ].
Ltac kn_allx ZA := repeat (apply Forall_cons; [kn1x ZA|]); try apply Forall_nil.


(* [comment removed for export] *)
Module PA1 := LibSegZ_e2a1.
Definition KS_A1 : list nat := Eval vm_compute in (BG.kept_list 56 PA1.regs0 PA1.regs_out).
Lemma KS_A1_ok : BG.kept_ok 56 PA1.regs0 PA1.regs_out KS_A1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_1 : nth 1 PA1.regs_out (ELit 0) = ELit 259044. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_2 : nth 2 PA1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_8 : nth 8 PA1.regs_out (ELit 0) = ELit 144. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_10 : nth 10 PA1.regs_out (ELit 0) = ELit 16. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_11 : nth 11 PA1.regs_out (ELit 0) = ELit 144. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A1 : SR.ps_cells PA1.ps0 = PA1.cells. Proof. reflexivity. Qed.
Definition VAL_A1 (R : bvmap 5 word) (csp : Z) (obj : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | _ => getr R (reg k) end.
Definition VZ_A1 (R : bvmap 5 word) (csp : Z) (obj : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A1 R csp obj : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A1 R csp obj) (fun _ => [])) k) = VZ_A1 R csp obj k.
Proof.
  intros. cbn [ev]. unfold VAL_A1, VZ_A1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2a1_conc fx R M csp obj :
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (16) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 112) (112) ->
  L5.defined M ((csp) - 112) (112) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + -112 + (112) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -112) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  exists fx' R' M', msteps RSEGS (st fx R 140112 M) (st fx' R' 309576 M')
    /\ (forall i, In i KS_A1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (259044)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp - 48)
    /\ getr R' (reg 8) = Z_to_bv 64 (144)
    /\ getr R' (reg 10) = Z_to_bv 64 (16)
    /\ getr R' (reg 11) = Z_to_bv 64 (144)
    /\ L5.u64_at RSEGS M' ((csp) - 48) (144)
    /\ L5.u64_at RSEGS M' ((csp) - 40) (257240)
    /\ L5.u64_at RSEGS M' ((csp) - 24) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' ((csp) - 16) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' ((csp) - 8) (140116)
    /\ (forall x : word, ~ ((csp) + -112 <= bv_unsigned x < (csp) + -112 + (112)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13.
  set (Vf := VAL_A1 R csp obj). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A1 R csp obj k) by (apply VAL_VZ_A1; lia). unfold VZ_A1 in ZA.
  assert (HR: regs_ok E PA1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA1.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA1.kn0). { unfold know_ok, PA1.kn0. kn_allx ZA. }
  destruct (PA1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA1.regs0 PA1.regs_out 56 KS_A1 KS_A1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 1 Hregs) by lia. rewrite ro_A1_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 2 Hregs) by lia. rewrite ro_A1_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 8 Hregs) by lia. rewrite ro_A1_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 10 Hregs) by lia. rewrite ro_A1_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 11 Hregs) by lia. rewrite ro_A1_11. L5KP.wordE' ZA Hag. }
  rewrite cells_A1 in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PA1.cells, PA1.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0. apply Hfr. unfold PA1.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA2 := LibSegZ_e2a2.
Definition KS_A2 : list nat := Eval vm_compute in (BG.kept_list 56 PA2.regs0 PA2.regs_out).
Lemma KS_A2_ok : BG.kept_ok 56 PA2.regs0 PA2.regs_out KS_A2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_1 : nth 1 PA2.regs_out (ELit 0) = ELit 140116. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_2 : nth 2 PA2.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_8 : nth 8 PA2.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_9 : nth 9 PA2.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_10 : nth 10 PA2.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_11 : nth 11 PA2.regs_out (ELit 0) = ELit 77618. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A2 : SR.ps_cells PA2.ps0 = PA2.cells. Proof. reflexivity. Qed.
Definition VAL_A2 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_A2 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A2 R csp obj v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A2 R csp obj v40) (fun _ => [])) k) = VZ_A2 R csp obj v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_A2, VZ_A2.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2a2_conc fx R M csp obj v40 :
  getr R (reg 2) = Z_to_bv 64 (csp - 48) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 128) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 112) (64) ->
  L5.defined M ((csp) - 112) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + -112 + (112) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -112) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u64_at RSEGS M ((csp) - 40) (257240) ->
  L5.u64_at RSEGS M ((csp) - 48) (144) ->
  L5.u64_at RSEGS M ((csp) - 8) (140116) ->
  L5.u64_at RSEGS M ((csp) - 16) (v40) ->
  L5.u64_at RSEGS M ((csp) - 24) (csp + 304) ->
  exists fx' R' M', msteps RSEGS (st fx R 259044 M) (st fx' R' 140132 M')
    /\ (forall i, In i KS_A2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (140116)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp)
    /\ getr R' (reg 8) = Z_to_bv 64 (v40)
    /\ getr R' (reg 9) = Z_to_bv 64 (obj)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj)
    /\ getr R' (reg 11) = Z_to_bv 64 (77618)
    /\ L5KP.zeros_at M' ((obj) - 128) (144)
    /\ (forall x : word, ~ ((csp) + -112 <= bv_unsigned x < (csp) + -112 + (64)) -> ~ ((obj) + -128 <= bv_unsigned x < (obj) + -128 + (144)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18.
  set (Vf := VAL_A2 R csp obj v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A2 R csp obj v40 k) by (apply VAL_VZ_A2; lia). unfold VZ_A2 in ZA.
  assert (HR: regs_ok E PA2.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA2.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PA2.kn0). { unfold know_ok, PA2.kn0. kn_allx ZA. }
  destruct (PA2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PA2.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA2.regs0 PA2.regs_out 56 KS_A2 KS_A2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA2.regs_out E' R' 1 Hregs) by lia. rewrite ro_A2_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA2.regs_out E' R' 2 Hregs) by lia. rewrite ro_A2_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA2.regs_out E' R' 8 Hregs) by lia. rewrite ro_A2_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA2.regs_out E' R' 9 Hregs) by lia. rewrite ro_A2_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA2.regs_out E' R' 10 Hregs) by lia. rewrite ro_A2_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PA2.regs_out E' R' 11 Hregs) by lia. rewrite ro_A2_11. L5KP.wordE' ZA Hag. }
  rewrite cells_A2 in Hcells.
  split. { eapply L5KP.zeros_of_KZero. apply Hcells. unfold PA2.cells, PA2.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1. apply Hfr. unfold PA2.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PC1 := LibSegZ_e2c1.
Definition KS_C1 : list nat := Eval vm_compute in (BG.kept_list 56 PC1.regs0 PC1.regs_out).
Lemma KS_C1_ok : BG.kept_ok 56 PC1.regs0 PC1.regs_out KS_C1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_1 : nth 1 PC1.regs_out (ELit 0) = ELit 368844. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_2 : nth 2 PC1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-64)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_8 : nth 8 PC1.regs_out (ELit 0) = ELit 37. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_9 : nth 9 PC1.regs_out (ELit 0) = ELit 77618. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_10 : nth 10 PC1.regs_out (ELit 0) = ELit 37. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_18 : nth 18 PC1.regs_out (ELit 0) = ELit 12. Proof. vm_compute. reflexivity. Qed.
Lemma cells_C1 : SR.ps_cells PC1.ps0 = PC1.cells. Proof. reflexivity. Qed.
Definition VAL_C1 (R : bvmap 5 word) (csp : Z) (obj : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | _ => getr R (reg k) end.
Definition VZ_C1 (R : bvmap 5 word) (csp : Z) (obj : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_C1 R csp obj : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_C1 R csp obj) (fun _ => [])) k) = VZ_C1 R csp obj k.
Proof.
  intros. cbn [ev]. unfold VAL_C1, VZ_C1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2c1_conc fx R M csp obj :
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 obj ->
  getr R (reg 11) = Z_to_bv 64 (77618) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 128) (128) ->
  L5.defined M ((csp) - 128) (128) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + -128 + (128) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -128) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  exists fx' R' M', msteps RSEGS (st fx R 140132 M) (st fx' R' 309572 M')
    /\ (forall i, In i KS_C1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (368844)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp - 64)
    /\ getr R' (reg 8) = Z_to_bv 64 (37)
    /\ getr R' (reg 9) = Z_to_bv 64 (77618)
    /\ getr R' (reg 10) = Z_to_bv 64 (37)
    /\ getr R' (reg 18) = Z_to_bv 64 (12)
    /\ L5.u64_at RSEGS M' ((csp) - 64) (obj)
    /\ L5.u64_at RSEGS M' ((csp) - 56) (263612)
    /\ L5.u64_at RSEGS M' ((obj) + 0) (385144)
    /\ L5.u64_at RSEGS M' ((csp) - 40) (bv_unsigned (getr R (reg 19)))
    /\ L5.u64_at RSEGS M' ((csp) - 32) (bv_unsigned (getr R (reg 18)))
    /\ L5.u64_at RSEGS M' ((csp) - 24) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' ((csp) - 16) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' ((csp) - 8) (140136)
    /\ (forall x : word, ~ ((csp) + -128 <= bv_unsigned x < (csp) + -128 + (128)) -> ~ ((obj) + 0 <= bv_unsigned x < (obj) + 0 + (8)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 H11 G2 G10 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13.
  set (Vf := VAL_C1 R csp obj). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_C1 R csp obj k) by (apply VAL_VZ_C1; lia). unfold VZ_C1 in ZA.
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
  split. { intros x Hy0 Hy1. apply Hfr. unfold PC1.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PC2 := LibSegZ_e2c2.
Definition KS_C2 : list nat := Eval vm_compute in (BG.kept_list 56 PC2.regs0 PC2.regs_out).
Lemma KS_C2_ok : BG.kept_ok 56 PC2.regs0 PC2.regs_out KS_C2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_1 : nth 1 PC2.regs_out (ELit 0) = ELit 140136. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_2 : nth 2 PC2.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_8 : nth 8 PC2.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_9 : nth 9 PC2.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_10 : nth 10 PC2.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_11 : nth 11 PC2.regs_out (ELit 0) = ELit 385384. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_12 : nth 12 PC2.regs_out (ELit 0) = ELit 253816. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_18 : nth 18 PC2.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 416). Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_19 : nth 19 PC2.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma cells_C2 : SR.ps_cells PC2.ps0 = PC2.cells. Proof. reflexivity. Qed.
Definition VAL_C2 (R : bvmap 5 word) (csp : Z) (obj : Z) (ref : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 37%nat => Z_to_bv 64 ref | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_C2 (R : bvmap 5 word) (csp : Z) (obj : Z) (ref : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 37%nat => ref | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_C2 R csp obj ref v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= ref < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_C2 R csp obj ref v40) (fun _ => [])) k) = VZ_C2 R csp obj ref v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_C2, VZ_C2.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2c2_conc fx R M csp obj ref v40 :
  getr R (reg 2) = Z_to_bv 64 (csp - 64) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 9) = Z_to_bv 64 (77618) ->
  getr R (reg 10) = Z_to_bv 64 (ref) ->
  getr R (reg 18) = Z_to_bv 64 (12) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= ref < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 128) (64) ->
  L5.defined M ((csp) - 128) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  4096 <= ref <= 140737488355328 ->
  (ref) mod 16 = 0 ->
  L5.writable RSEGS M (ref) (37) ->
  L5.defined M (ref) (37) ->
  ((csp) + -128 + (128) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -128) ->
  ((obj) + -128 + (144) <= (ref) + 0 \/ (ref) + 0 + (37) <= (obj) + -128) ->
  ((csp) + -128 + (128) <= (ref) + 0 \/ (ref) + 0 + (37) <= (csp) + -128) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  ((ref) + 0 + (37) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (ref) + 0) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u64_at RSEGS M ((csp) - 56) (263612) ->
  L5.u64_at RSEGS M ((csp) - 64) (obj) ->
  L5.u64_at RSEGS M ((csp) - 8) (140136) ->
  L5.u64_at RSEGS M ((csp) - 16) (v40) ->
  L5.u64_at RSEGS M ((csp) - 24) (obj) ->
  L5.u64_at RSEGS M ((csp) - 32) (csp + 416) ->
  L5.u64_at RSEGS M ((csp) - 40) (0) ->
  exists fx' R' M', msteps RSEGS (st fx R 368844 M) (st fx' R' 140156 M')
    /\ (forall i, In i KS_C2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (140136)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp)
    /\ getr R' (reg 8) = Z_to_bv 64 (v40)
    /\ getr R' (reg 9) = Z_to_bv 64 (obj)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj)
    /\ getr R' (reg 11) = Z_to_bv 64 (385384)
    /\ getr R' (reg 12) = Z_to_bv 64 (253816)
    /\ getr R' (reg 18) = Z_to_bv 64 (csp + 416)
    /\ getr R' (reg 19) = Z_to_bv 64 (0)
    /\ L5.u64_at RSEGS M' ((obj) + 8) (ref + 24)
    /\ L5.u64_at RSEGS M' ((ref) + 24) (8532461059501614426)
    /\ L5.u8_at RSEGS M' ((ref) + 32) (105)
    /\ L5.u8_at RSEGS M' ((ref) + 33) (100)
    /\ L5.u8_at RSEGS M' ((ref) + 34) (101)
    /\ L5.u8_at RSEGS M' ((ref) + 35) (46)
    /\ L5.u8_at RSEGS M' ((ref) + 36) (0)
    /\ L5.u32_at RSEGS M' ((ref) + 16) (0)
    /\ L5.u64_at RSEGS M' ((ref) + 8) (12)
    /\ L5.u64_at RSEGS M' ((ref) + 0) (12)
    /\ (forall x : word, ~ ((csp) + -128 <= bv_unsigned x < (csp) + -128 + (64)) -> ~ ((obj) + 8 <= bv_unsigned x < (obj) + 8 + (8)) -> ~ ((ref) + 0 <= bv_unsigned x < (ref) + 0 + (37)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H9 H10 H18 G2 G10 G37 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27.
  set (Vf := VAL_C2 R csp obj ref v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_C2 R csp obj ref v40 k) by (apply VAL_VZ_C2; lia). unfold VZ_C2 in ZA.
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
  split. { rewrite (BG.out_reg PC2.regs_out E' R' 19 Hregs) by lia. rewrite ro_C2_19. L5KP.wordE' ZA Hag. }
  rewrite cells_C2 in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.uw_of_KWordw. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1 Hy2. apply Hfr. unfold PC2.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP1 := LibSegZ_e2p1.
Definition KS_P1 : list nat := Eval vm_compute in (BG.kept_list 56 PP1.regs0 PP1.regs_out).
Lemma KS_P1_ok : BG.kept_ok 56 PP1.regs0 PP1.regs_out KS_P1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1_2 : nth 2 PP1.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1_8 : nth 8 PP1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1_10 : nth 10 PP1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1_11 : nth 11 PP1.regs_out (ELit 0) = EVar 11. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P1 : SR.ps_cells PP1.ps0 = PP1.cells. Proof. reflexivity. Qed.
Definition VAL_P1 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_P1 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P1 R csp obj v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P1 R csp obj v40) (fun _ => [])) k) = VZ_P1 R csp obj v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_P1, VZ_P1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2p1_conc fx R M csp obj v40 :
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 32) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 64) (64) ->
  L5.defined M ((csp) - 64) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + -64 + (240) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -64) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  0 <= v40 <= 255 ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u8_at RSEGS M ((csp) + 168) (Z.land (v40) (254)) ->
  exists fx' R' M', msteps RSEGS (st fx R 140224 M) (st fx' R' 140392 M')
    /\ (forall i, In i KS_P1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (csp)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = getr R (reg 11)
    /\ (forall x : word, ~ ((csp) + -64 <= bv_unsigned x < (csp) + -64 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  set (Vf := VAL_P1 R csp obj v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P1 R csp obj v40 k) by (apply VAL_VZ_P1; lia). unfold VZ_P1 in ZA.
  assert (HR: regs_ok E PP1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP1.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP1.kn0). { unfold know_ok, PP1.kn0. kn_allx ZA. }
  destruct (PP1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP1.regs0 PP1.regs_out 56 KS_P1 KS_P1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP1.regs_out E' R' 2 Hregs) by lia. rewrite ro_P1_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1.regs_out E' R' 8 Hregs) by lia. rewrite ro_P1_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1.regs_out E' R' 10 Hregs) by lia. rewrite ro_P1_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1.regs_out E' R' 11 Hregs) by lia. rewrite ro_P1_11. cbn [edenot]. rewrite <- (proj1 Hag 11%nat) by lia. reflexivity. }
  rewrite cells_P1 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PP1.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP2 := LibSegZ_e2p2.
Definition KS_P2 : list nat := Eval vm_compute in (BG.kept_list 56 PP2.regs0 PP2.regs_out).
Lemma KS_P2_ok : BG.kept_ok 56 PP2.regs0 PP2.regs_out KS_P2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2_2 : nth 2 PP2.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 304). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2_8 : nth 8 PP2.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2_10 : nth 10 PP2.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2_11 : nth 11 PP2.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P2 : SR.ps_cells PP2.ps0 = PP2.cells. Proof. reflexivity. Qed.
Definition VAL_P2 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_P2 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P2 R csp obj v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P2 R csp obj v40) (fun _ => [])) k) = VZ_P2 R csp obj v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_P2, VZ_P2.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2p2_conc fx R M csp obj v40 :
  getr R (reg 2) = Z_to_bv 64 (csp + 304) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 32) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 240) (64) ->
  L5.defined M ((csp) + 240) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + 240 + (80) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 240) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  0 <= v40 <= 255 ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u8_at RSEGS M ((csp) + 304) (Z.land (v40) (254)) ->
  exists fx' R' M', msteps RSEGS (st fx R 138580 M) (st fx' R' 138620 M')
    /\ (forall i, In i KS_P2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 304)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = Z_to_bv 64 (0)
    /\ (forall x : word, ~ ((csp) + 240 <= bv_unsigned x < (csp) + 240 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  set (Vf := VAL_P2 R csp obj v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P2 R csp obj v40 k) by (apply VAL_VZ_P2; lia). unfold VZ_P2 in ZA.
  assert (HR: regs_ok E PP2.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP2.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP2.kn0). { unfold know_ok, PP2.kn0. kn_allx ZA. }
  destruct (PP2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP2.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP2.regs0 PP2.regs_out 56 KS_P2 KS_P2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP2.regs_out E' R' 2 Hregs) by lia. rewrite ro_P2_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2.regs_out E' R' 8 Hregs) by lia. rewrite ro_P2_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2.regs_out E' R' 10 Hregs) by lia. rewrite ro_P2_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2.regs_out E' R' 11 Hregs) by lia. rewrite ro_P2_11. L5KP.wordE' ZA Hag. }
  rewrite cells_P2 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PP2.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

End L5E2A.
