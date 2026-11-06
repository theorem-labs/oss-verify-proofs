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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5E3AU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5E3AU.
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
Lemma lor1_land254_range v : 0 <= v -> 0 <= Z.lor (Z.land v 254) 1 < 256.
Proof.
  intros Hv. pose proof (L5KP.land_le_r v 254 Hv ltac:(lia)) as R.
  assert (E: Z.lor (Z.land v 254) 1 = Z.land v 254 + 1).
  { pose proof (Z.add_lor_land (Z.land v 254) 1) as X. rewrite <- Z.land_assoc in X. change (Z.land 254 1) with 0 in X. rewrite Z.land_0_r in X. lia. }
  rewrite E. lia.
Qed.
Ltac land_rng := first [ lia | apply L5.land_byte_range; lia | apply lor1_land254_range; lia ].
Ltac zc_eval0r ZA := zc_eval0 ZA; cbn beta iota; reflexivity.
Ltac kn1x ZA := first [ L5KP.kn1 ZA
  | lazymatch goal with
    | |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5KP.kentry_KRange; [zc_eval0r ZA | lia]
    | |- kentry_ok _ _ _ (KWord _ 8 _) => eapply L5KP.kentry_KWord8; [L5KP.evalE ZA | zc_eval0r ZA | lia | lia | L5KP.kn_mem]
    | |- kentry_ok _ _ _ (KWord _ 1 _) => eapply L5KP.kentry_KWord1; [L5KP.evalE ZA | zc_eval0r ZA | lia | lia | land_rng | L5KP.kn_mem]
    end ].
Ltac kn_allx ZA := repeat (apply Forall_cons; [kn1x ZA|]); try apply Forall_nil.


(* [comment removed for export] *)
Module PA1 := LibSegZ_e3a1u.
Definition KS_A1 : list nat := Eval vm_compute in (BG.kept_list 56 PA1.regs0 PA1.regs_out).
Lemma KS_A1_ok : BG.kept_ok 56 PA1.regs0 PA1.regs_out KS_A1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_1 : nth 1 PA1.regs_out (ELit 0) = ELit 261856. Proof. vm_compute. reflexivity. Qed.
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
Lemma e3a1u_conc fx R M csp obj :
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
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
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  exists fx' R' M', msteps RSEGS (st fx R 137464 M) (st fx' R' 312388 M')
    /\ (forall i, In i KS_A1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (261856)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp - 48)
    /\ getr R' (reg 8) = Z_to_bv 64 (144)
    /\ getr R' (reg 10) = Z_to_bv 64 (16)
    /\ getr R' (reg 11) = Z_to_bv 64 (144)
    /\ L5.u64_at RSEGS M' ((csp) - 48) (144)
    /\ L5.u64_at RSEGS M' ((csp) - 40) (260052)
    /\ L5.u64_at RSEGS M' ((csp) - 24) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' ((csp) - 16) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' ((csp) - 8) (137468)
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
Module PA2 := LibSegZ_e3a2u.
Definition KS_A2 : list nat := Eval vm_compute in (BG.kept_list 56 PA2.regs0 PA2.regs_out).
Lemma KS_A2_ok : BG.kept_ok 56 PA2.regs0 PA2.regs_out KS_A2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_1 : nth 1 PA2.regs_out (ELit 0) = ELit 137468. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_2 : nth 2 PA2.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_8 : nth 8 PA2.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_9 : nth 9 PA2.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 1072). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_10 : nth 10 PA2.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 8). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_11 : nth 11 PA2.regs_out (ELit 0) = ELit 74669. Proof. vm_compute. reflexivity. Qed.
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
Lemma e3a2u_conc fx R M csp obj v40 :
  getr R (reg 2) = Z_to_bv 64 (csp - 48) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
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
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u64_at RSEGS M ((csp) - 40) (260052) ->
  L5.u64_at RSEGS M ((csp) - 48) (144) ->
  L5.u64_at RSEGS M ((csp) - 8) (137468) ->
  L5.u64_at RSEGS M ((csp) - 16) (v40) ->
  L5.u64_at RSEGS M ((csp) - 24) (csp + 1072) ->
  exists fx' R' M', msteps RSEGS (st fx R 261856 M) (st fx' R' 137484 M')
    /\ (forall i, In i KS_A2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (137468)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj)
    /\ getr R' (reg 9) = Z_to_bv 64 (csp + 1072)
    /\ getr R' (reg 10) = Z_to_bv 64 (csp + 8)
    /\ getr R' (reg 11) = Z_to_bv 64 (74669)
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
Module PS1 := LibSegZ_e3s1u.
Definition KS_S1 : list nat := Eval vm_compute in (BG.kept_list 56 PS1.regs0 PS1.regs_out).
Lemma KS_S1_ok : BG.kept_ok 56 PS1.regs0 PS1.regs_out KS_S1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1_1 : nth 1 PS1.regs_out (ELit 0) = ELit 371656. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1_2 : nth 2 PS1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-64)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1_8 : nth 8 PS1.regs_out (ELit 0) = ELit 48. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1_9 : nth 9 PS1.regs_out (ELit 0) = ELit 74669. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1_10 : nth 10 PS1.regs_out (ELit 0) = ELit 48. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1_11 : nth 11 PS1.regs_out (ELit 0) = ELit 18446744073709551608. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1_18 : nth 18 PS1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 8). Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1_20 : nth 20 PS1.regs_out (ELit 0) = ELit 48. Proof. vm_compute. reflexivity. Qed.
Lemma cells_S1 : SR.ps_cells PS1.ps0 = PS1.cells. Proof. reflexivity. Qed.
Definition VAL_S1 (R : bvmap 5 word) (csp : Z) (obj : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | _ => getr R (reg k) end.
Definition VZ_S1 (R : bvmap 5 word) (csp : Z) (obj : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_S1 R csp obj : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_S1 R csp obj) (fun _ => [])) k) = VZ_S1 R csp obj k.
Proof.
  intros. cbn [ev]. unfold VAL_S1, VZ_S1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3s1u_conc fx R M csp obj :
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 10) = Z_to_bv 64 (csp + 8) ->
  getr R (reg 11) = Z_to_bv 64 (74669) ->
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
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  exists fx' R' M', msteps RSEGS (st fx R 137484 M) (st fx' R' 312384 M')
    /\ (forall i, In i KS_S1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (371656)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp - 64)
    /\ getr R' (reg 8) = Z_to_bv 64 (48)
    /\ getr R' (reg 9) = Z_to_bv 64 (74669)
    /\ getr R' (reg 10) = Z_to_bv 64 (48)
    /\ getr R' (reg 11) = Z_to_bv 64 (18446744073709551608)
    /\ getr R' (reg 18) = Z_to_bv 64 (csp + 8)
    /\ getr R' (reg 20) = Z_to_bv 64 (48)
    /\ L5.u64_at RSEGS M' ((csp) - 64) (41)
    /\ L5.u64_at RSEGS M' ((csp) - 56) (137160)
    /\ L5.u64_at RSEGS M' ((csp) - 48) (bv_unsigned (getr R (reg 20)))
    /\ L5.u64_at RSEGS M' ((csp) - 40) (bv_unsigned (getr R (reg 19)))
    /\ L5.u64_at RSEGS M' ((csp) - 32) (bv_unsigned (getr R (reg 18)))
    /\ L5.u64_at RSEGS M' ((csp) - 24) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' ((csp) - 16) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' ((csp) - 8) (137488)
    /\ (forall x : word, ~ ((csp) + -128 <= bv_unsigned x < (csp) + -128 + (128)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 H11 G2 G10 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13.
  set (Vf := VAL_S1 R csp obj). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_S1 R csp obj k) by (apply VAL_VZ_S1; lia). unfold VZ_S1 in ZA.
  assert (HR: regs_ok E PS1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PS1.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PS1.kn0). { unfold know_ok, PS1.kn0. kn_allx ZA. }
  destruct (PS1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PS1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PS1.regs0 PS1.regs_out 56 KS_S1 KS_S1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PS1.regs_out E' R' 1 Hregs) by lia. rewrite ro_S1_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1.regs_out E' R' 2 Hregs) by lia. rewrite ro_S1_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1.regs_out E' R' 8 Hregs) by lia. rewrite ro_S1_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1.regs_out E' R' 9 Hregs) by lia. rewrite ro_S1_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1.regs_out E' R' 10 Hregs) by lia. rewrite ro_S1_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1.regs_out E' R' 11 Hregs) by lia. rewrite ro_S1_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1.regs_out E' R' 18 Hregs) by lia. rewrite ro_S1_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1.regs_out E' R' 20 Hregs) by lia. rewrite ro_S1_20. L5KP.wordE' ZA Hag. }
  rewrite cells_S1 in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1.cells, PS1.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1.cells, PS1.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1.cells, PS1.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1.cells, PS1.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1.cells, PS1.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1.cells, PS1.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1.cells, PS1.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1.cells, PS1.cells0. right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0. apply Hfr. unfold PS1.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PS2L := LibSegZ_e3s2u_bl.
Definition KS_S2L : list nat := Eval vm_compute in (BG.kept_list 56 PS2L.regs0 PS2L.regs_out).
Lemma KS_S2L_ok : BG.kept_ok 56 PS2L.regs0 PS2L.regs_out KS_S2L = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2L_1 : nth 1 PS2L.regs_out (ELit 0) = ELit 137512. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2L_2 : nth 2 PS2L.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-16)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2L_8 : nth 8 PS2L.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2L_9 : nth 9 PS2L.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 1072). Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2L_10 : nth 10 PS2L.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2L_11 : nth 11 PS2L.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 8). Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2L_18 : nth 18 PS2L.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2L_19 : nth 19 PS2L.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2L_20 : nth 20 PS2L.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma cells_S2L : SR.ps_cells PS2L.ps0 = PS2L.cells. Proof. reflexivity. Qed.
Definition VAL_S2L (R : bvmap 5 word) (csp : Z) (obj : Z) (msg : Z) (v40 : Z) (v41 : Z) (v42 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 38%nat => Z_to_bv 64 msg | 40%nat => Z_to_bv 64 v40 | 41%nat => Z_to_bv 64 v41 | 42%nat => Z_to_bv 64 v42 | _ => getr R (reg k) end.
Definition VZ_S2L (R : bvmap 5 word) (csp : Z) (obj : Z) (msg : Z) (v40 : Z) (v41 : Z) (v42 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 38%nat => msg | 40%nat => v40 | 41%nat => v41 | 42%nat => v42 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_S2L R csp obj msg v40 v41 v42 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= msg < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 -> 0 <= v41 < 2 ^ 64 -> 0 <= v42 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_S2L R csp obj msg v40 v41 v42) (fun _ => [])) k) = VZ_S2L R csp obj msg v40 v41 v42 k.
Proof.
  intros. cbn [ev]. unfold VAL_S2L, VZ_S2L.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3s2u_bl_conc fx R M csp obj msg v40 v41 v42 :
  getr R (reg 2) = Z_to_bv 64 (csp - 64) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 9) = Z_to_bv 64 (74669) ->
  getr R (reg 10) = Z_to_bv 64 (msg) ->
  getr R (reg 18) = Z_to_bv 64 (csp + 8) ->
  getr R (reg 20) = Z_to_bv 64 (48) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= msg < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  0 <= v41 < 2 ^ 64 ->
  0 <= v42 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 128) (64) ->
  L5.defined M ((csp) - 128) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  4096 <= msg <= 65488 ->
  (msg) mod 16 = 0 ->
  L5.writable RSEGS M (msg) (48) ->
  L5.defined M (msg) (48) ->
  ((csp) + -128 + (160) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -128) ->
  ((obj) + -128 + (144) <= (msg) + 0 \/ (msg) + 0 + (48) <= (obj) + -128) ->
  ((csp) + -128 + (160) <= (msg) + 0 \/ (msg) + 0 + (48) <= (csp) + -128) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  ((msg) + 0 + (48) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (msg) + 0) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u64_at RSEGS M ((csp) - 56) (137160) ->
  L5.u64_at RSEGS M ((csp) - 64) (41) ->
  L5.u64_at RSEGS M ((csp) - 8) (137488) ->
  L5.u64_at RSEGS M ((csp) - 16) (obj) ->
  L5.u64_at RSEGS M ((csp) - 24) (csp + 1072) ->
  L5.u64_at RSEGS M ((csp) - 32) (v40) ->
  L5.u64_at RSEGS M ((csp) - 40) (v41) ->
  L5.u64_at RSEGS M ((csp) - 48) (v42) ->
  L5.writable RSEGS M ((csp) - 16) (8) ->
  L5.writable RSEGS M ((csp) - 8) (8) ->
  L5.writable RSEGS M ((csp) + 8) (8) ->
  L5.writable RSEGS M ((csp) + 16) (8) ->
  L5.writable RSEGS M ((csp) + 24) (8) ->
  exists fx' R' M', msteps RSEGS (st fx R 371656 M) (st fx' R' 137268 M')
    /\ (forall i, In i KS_S2L -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (137512)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp - 16)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj)
    /\ getr R' (reg 9) = Z_to_bv 64 (csp + 1072)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj)
    /\ getr R' (reg 11) = Z_to_bv 64 (csp + 8)
    /\ getr R' (reg 18) = Z_to_bv 64 (v40)
    /\ getr R' (reg 19) = Z_to_bv 64 (v41)
    /\ getr R' (reg 20) = Z_to_bv 64 (v42)
    /\ L5.u64_at RSEGS M' ((csp) - 16) (obj)
    /\ L5.u64_at RSEGS M' ((csp) - 8) (137512)
    /\ L5.u8_at RSEGS M' ((msg) + 41) (0)
    /\ L5.u64_at RSEGS M' ((msg) + 0) (8028075845441778529)
    /\ L5.u64_at RSEGS M' ((msg) + 8) (7863351059373564014)
    /\ L5.u64_at RSEGS M' ((msg) + 16) (2838809733452757089)
    /\ L5.u64_at RSEGS M' ((msg) + 24) (2334102023183623712)
    /\ L5.u64_at RSEGS M' ((msg) + 32) (4188416081412519009)
    /\ L5.u8_at RSEGS M' ((msg) + 40) (48)
    /\ L5.u64_at RSEGS M' ((csp) + 24) (msg)
    /\ L5.u64_at RSEGS M' ((csp) + 16) (41)
    /\ L5.u64_at RSEGS M' ((csp) + 8) (49)
    /\ (forall x : word, ~ ((csp) + -128 <= bv_unsigned x < (csp) + -128 + (64)) -> ~ ((csp) + -16 <= bv_unsigned x < (csp) + -16 + (8)) -> ~ ((csp) + -8 <= bv_unsigned x < (csp) + -8 + (8)) -> ~ ((csp) + 8 <= bv_unsigned x < (csp) + 8 + (8)) -> ~ ((csp) + 16 <= bv_unsigned x < (csp) + 16 + (8)) -> ~ ((csp) + 24 <= bv_unsigned x < (csp) + 24 + (8)) -> ~ ((msg) + 0 <= bv_unsigned x < (msg) + 0 + (42)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H9 H10 H18 H20 G2 G10 G38 G40 G41 G42 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33.
  set (Vf := VAL_S2L R csp obj msg v40 v41 v42). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_S2L R csp obj msg v40 v41 v42 k) by (apply VAL_VZ_S2L; lia). unfold VZ_S2L in ZA.
  assert (HR: regs_ok E PS2L.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PS2L.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PS2L.kn0). { unfold know_ok, PS2L.kn0. kn_allx ZA. }
  destruct (PS2L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PS2L.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PS2L.regs0 PS2L.regs_out 56 KS_S2L KS_S2L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PS2L.regs_out E' R' 1 Hregs) by lia. rewrite ro_S2L_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2L.regs_out E' R' 2 Hregs) by lia. rewrite ro_S2L_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2L.regs_out E' R' 8 Hregs) by lia. rewrite ro_S2L_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2L.regs_out E' R' 9 Hregs) by lia. rewrite ro_S2L_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2L.regs_out E' R' 10 Hregs) by lia. rewrite ro_S2L_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2L.regs_out E' R' 11 Hregs) by lia. rewrite ro_S2L_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2L.regs_out E' R' 18 Hregs) by lia. rewrite ro_S2L_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2L.regs_out E' R' 19 Hregs) by lia. rewrite ro_S2L_19. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2L.regs_out E' R' 20 Hregs) by lia. rewrite ro_S2L_20. L5KP.wordE' ZA Hag. }
  rewrite cells_S2L in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2L.cells, PS2L.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2L.cells, PS2L.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PS2L.cells, PS2L.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2L.cells, PS2L.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2L.cells, PS2L.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2L.cells, PS2L.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2L.cells, PS2L.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2L.cells, PS2L.cells0. right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PS2L.cells, PS2L.cells0. right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2L.cells, PS2L.cells0. right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2L.cells, PS2L.cells0. right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2L.cells, PS2L.cells0. right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6. apply Hfr. unfold PS2L.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PS2H := LibSegZ_e3s2u_bh.
Definition KS_S2H : list nat := Eval vm_compute in (BG.kept_list 56 PS2H.regs0 PS2H.regs_out).
Lemma KS_S2H_ok : BG.kept_ok 56 PS2H.regs0 PS2H.regs_out KS_S2H = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2H_1 : nth 1 PS2H.regs_out (ELit 0) = ELit 137512. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2H_2 : nth 2 PS2H.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-16)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2H_8 : nth 8 PS2H.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2H_9 : nth 9 PS2H.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 1072). Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2H_10 : nth 10 PS2H.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2H_11 : nth 11 PS2H.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 8). Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2H_18 : nth 18 PS2H.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2H_19 : nth 19 PS2H.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2H_20 : nth 20 PS2H.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma cells_S2H : SR.ps_cells PS2H.ps0 = PS2H.cells. Proof. reflexivity. Qed.
Definition VAL_S2H (R : bvmap 5 word) (csp : Z) (obj : Z) (msg : Z) (v40 : Z) (v41 : Z) (v42 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 38%nat => Z_to_bv 64 msg | 40%nat => Z_to_bv 64 v40 | 41%nat => Z_to_bv 64 v41 | 42%nat => Z_to_bv 64 v42 | _ => getr R (reg k) end.
Definition VZ_S2H (R : bvmap 5 word) (csp : Z) (obj : Z) (msg : Z) (v40 : Z) (v41 : Z) (v42 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 38%nat => msg | 40%nat => v40 | 41%nat => v41 | 42%nat => v42 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_S2H R csp obj msg v40 v41 v42 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= msg < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 -> 0 <= v41 < 2 ^ 64 -> 0 <= v42 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_S2H R csp obj msg v40 v41 v42) (fun _ => [])) k) = VZ_S2H R csp obj msg v40 v41 v42 k.
Proof.
  intros. cbn [ev]. unfold VAL_S2H, VZ_S2H.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3s2u_bh_conc fx R M csp obj msg v40 v41 v42 :
  getr R (reg 2) = Z_to_bv 64 (csp - 64) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 9) = Z_to_bv 64 (74669) ->
  getr R (reg 10) = Z_to_bv 64 (msg) ->
  getr R (reg 18) = Z_to_bv 64 (csp + 8) ->
  getr R (reg 20) = Z_to_bv 64 (48) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= msg < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  0 <= v41 < 2 ^ 64 ->
  0 <= v42 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 128) (64) ->
  L5.defined M ((csp) - 128) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  598016 <= msg <= 140737488355328 ->
  (msg) mod 16 = 0 ->
  L5.writable RSEGS M (msg) (48) ->
  L5.defined M (msg) (48) ->
  ((csp) + -128 + (160) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -128) ->
  ((obj) + -128 + (144) <= (msg) + 0 \/ (msg) + 0 + (48) <= (obj) + -128) ->
  ((csp) + -128 + (160) <= (msg) + 0 \/ (msg) + 0 + (48) <= (csp) + -128) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  ((msg) + 0 + (48) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (msg) + 0) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u64_at RSEGS M ((csp) - 56) (137160) ->
  L5.u64_at RSEGS M ((csp) - 64) (41) ->
  L5.u64_at RSEGS M ((csp) - 8) (137488) ->
  L5.u64_at RSEGS M ((csp) - 16) (obj) ->
  L5.u64_at RSEGS M ((csp) - 24) (csp + 1072) ->
  L5.u64_at RSEGS M ((csp) - 32) (v40) ->
  L5.u64_at RSEGS M ((csp) - 40) (v41) ->
  L5.u64_at RSEGS M ((csp) - 48) (v42) ->
  L5.writable RSEGS M ((csp) - 16) (8) ->
  L5.writable RSEGS M ((csp) - 8) (8) ->
  L5.writable RSEGS M ((csp) + 8) (8) ->
  L5.writable RSEGS M ((csp) + 16) (8) ->
  L5.writable RSEGS M ((csp) + 24) (8) ->
  exists fx' R' M', msteps RSEGS (st fx R 371656 M) (st fx' R' 137268 M')
    /\ (forall i, In i KS_S2H -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (137512)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp - 16)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj)
    /\ getr R' (reg 9) = Z_to_bv 64 (csp + 1072)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj)
    /\ getr R' (reg 11) = Z_to_bv 64 (csp + 8)
    /\ getr R' (reg 18) = Z_to_bv 64 (v40)
    /\ getr R' (reg 19) = Z_to_bv 64 (v41)
    /\ getr R' (reg 20) = Z_to_bv 64 (v42)
    /\ L5.u64_at RSEGS M' ((csp) - 16) (obj)
    /\ L5.u64_at RSEGS M' ((csp) - 8) (137512)
    /\ L5.u8_at RSEGS M' ((msg) + 41) (0)
    /\ L5.u64_at RSEGS M' ((msg) + 0) (8028075845441778529)
    /\ L5.u64_at RSEGS M' ((msg) + 8) (7863351059373564014)
    /\ L5.u64_at RSEGS M' ((msg) + 16) (2838809733452757089)
    /\ L5.u64_at RSEGS M' ((msg) + 24) (2334102023183623712)
    /\ L5.u64_at RSEGS M' ((msg) + 32) (4188416081412519009)
    /\ L5.u8_at RSEGS M' ((msg) + 40) (48)
    /\ L5.u64_at RSEGS M' ((csp) + 24) (msg)
    /\ L5.u64_at RSEGS M' ((csp) + 16) (41)
    /\ L5.u64_at RSEGS M' ((csp) + 8) (49)
    /\ (forall x : word, ~ ((csp) + -128 <= bv_unsigned x < (csp) + -128 + (64)) -> ~ ((csp) + -16 <= bv_unsigned x < (csp) + -16 + (8)) -> ~ ((csp) + -8 <= bv_unsigned x < (csp) + -8 + (8)) -> ~ ((csp) + 8 <= bv_unsigned x < (csp) + 8 + (8)) -> ~ ((csp) + 16 <= bv_unsigned x < (csp) + 16 + (8)) -> ~ ((csp) + 24 <= bv_unsigned x < (csp) + 24 + (8)) -> ~ ((msg) + 0 <= bv_unsigned x < (msg) + 0 + (42)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H9 H10 H18 H20 G2 G10 G38 G40 G41 G42 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33.
  set (Vf := VAL_S2H R csp obj msg v40 v41 v42). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_S2H R csp obj msg v40 v41 v42 k) by (apply VAL_VZ_S2H; lia). unfold VZ_S2H in ZA.
  assert (HR: regs_ok E PS2H.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PS2H.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PS2H.kn0). { unfold know_ok, PS2H.kn0. kn_allx ZA. }
  destruct (PS2H.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PS2H.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PS2H.regs0 PS2H.regs_out 56 KS_S2H KS_S2H_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PS2H.regs_out E' R' 1 Hregs) by lia. rewrite ro_S2H_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2H.regs_out E' R' 2 Hregs) by lia. rewrite ro_S2H_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2H.regs_out E' R' 8 Hregs) by lia. rewrite ro_S2H_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2H.regs_out E' R' 9 Hregs) by lia. rewrite ro_S2H_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2H.regs_out E' R' 10 Hregs) by lia. rewrite ro_S2H_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2H.regs_out E' R' 11 Hregs) by lia. rewrite ro_S2H_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2H.regs_out E' R' 18 Hregs) by lia. rewrite ro_S2H_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2H.regs_out E' R' 19 Hregs) by lia. rewrite ro_S2H_19. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2H.regs_out E' R' 20 Hregs) by lia. rewrite ro_S2H_20. L5KP.wordE' ZA Hag. }
  rewrite cells_S2H in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2H.cells, PS2H.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2H.cells, PS2H.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PS2H.cells, PS2H.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2H.cells, PS2H.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2H.cells, PS2H.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2H.cells, PS2H.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2H.cells, PS2H.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2H.cells, PS2H.cells0. right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PS2H.cells, PS2H.cells0. right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2H.cells, PS2H.cells0. right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2H.cells, PS2H.cells0. right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS2H.cells, PS2H.cells0. right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6. apply Hfr. unfold PS2H.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PC1 := LibSegZ_e3c1u.
Definition KS_C1 : list nat := Eval vm_compute in (BG.kept_list 56 PC1.regs0 PC1.regs_out).
Lemma KS_C1_ok : BG.kept_ok 56 PC1.regs0 PC1.regs_out KS_C1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_1 : nth 1 PC1.regs_out (ELit 0) = ELit 371656. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_2 : nth 2 PC1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-80)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_8 : nth 8 PC1.regs_out (ELit 0) = ELit 66. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_9 : nth 9 PC1.regs_out (ELit 0) = EVar 38. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_10 : nth 10 PC1.regs_out (ELit 0) = ELit 66. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C1_18 : nth 18 PC1.regs_out (ELit 0) = ELit 41. Proof. vm_compute. reflexivity. Qed.
Lemma cells_C1 : SR.ps_cells PC1.ps0 = PC1.cells. Proof. reflexivity. Qed.
Definition VAL_C1 (R : bvmap 5 word) (csp : Z) (obj : Z) (msg : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 38%nat => Z_to_bv 64 msg | _ => getr R (reg k) end.
Definition VZ_C1 (R : bvmap 5 word) (csp : Z) (obj : Z) (msg : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 38%nat => msg | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_C1 R csp obj msg : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= msg < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_C1 R csp obj msg) (fun _ => [])) k) = VZ_C1 R csp obj msg k.
Proof.
  intros. cbn [ev]. unfold VAL_C1, VZ_C1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3c1u_conc fx R M csp obj msg :
  getr R (reg 2) = Z_to_bv 64 (csp - 16) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 10) = Z_to_bv 64 obj ->
  getr R (reg 11) = Z_to_bv 64 (csp + 8) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= msg < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 144) (128) ->
  L5.defined M ((csp) - 144) (128) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  4096 <= msg <= 140737488355328 ->
  (msg) mod 16 = 0 ->
  L5.writable RSEGS M (msg) (48) ->
  L5.defined M (msg) (48) ->
  ((csp) + -144 + (176) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -144) ->
  ((obj) + -128 + (144) <= (msg) + 0 \/ (msg) + 0 + (48) <= (obj) + -128) ->
  ((csp) + -144 + (176) <= (msg) + 0 \/ (msg) + 0 + (48) <= (csp) + -144) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  ((msg) + 0 + (48) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (msg) + 0) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u8_at RSEGS M ((csp) + 8) (49) ->
  L5.u64_at RSEGS M ((csp) + 24) (msg) ->
  L5.u8_at RSEGS M (msg) (97) ->
  L5.u8_at RSEGS M ((msg) + 1) (115) ->
  L5.u8_at RSEGS M ((msg) + 2) (115) ->
  L5.u8_at RSEGS M ((msg) + 3) (101) ->
  L5.u8_at RSEGS M ((msg) + 4) (114) ->
  L5.u8_at RSEGS M ((msg) + 5) (116) ->
  L5.u8_at RSEGS M ((msg) + 6) (105) ->
  L5.u8_at RSEGS M ((msg) + 7) (111) ->
  L5.u8_at RSEGS M ((msg) + 8) (110) ->
  L5.u8_at RSEGS M ((msg) + 9) (32) ->
  L5.u8_at RSEGS M ((msg) + 10) (39) ->
  L5.u8_at RSEGS M ((msg) + 11) (110) ->
  L5.u8_at RSEGS M ((msg) + 12) (32) ->
  L5.u8_at RSEGS M ((msg) + 13) (60) ->
  L5.u8_at RSEGS M ((msg) + 14) (32) ->
  L5.u8_at RSEGS M ((msg) + 15) (109) ->
  L5.u8_at RSEGS M ((msg) + 16) (97) ->
  L5.u8_at RSEGS M ((msg) + 17) (120) ->
  L5.u8_at RSEGS M ((msg) + 18) (95) ->
  L5.u8_at RSEGS M ((msg) + 19) (115) ->
  L5.u8_at RSEGS M ((msg) + 20) (105) ->
  L5.u8_at RSEGS M ((msg) + 21) (122) ->
  L5.u8_at RSEGS M ((msg) + 22) (101) ->
  L5.u8_at RSEGS M ((msg) + 23) (39) ->
  L5.u8_at RSEGS M ((msg) + 24) (32) ->
  L5.u8_at RSEGS M ((msg) + 25) (102) ->
  L5.u8_at RSEGS M ((msg) + 26) (97) ->
  L5.u8_at RSEGS M ((msg) + 27) (105) ->
  L5.u8_at RSEGS M ((msg) + 28) (108) ->
  L5.u8_at RSEGS M ((msg) + 29) (101) ->
  L5.u8_at RSEGS M ((msg) + 30) (100) ->
  L5.u8_at RSEGS M ((msg) + 31) (32) ->
  L5.u8_at RSEGS M ((msg) + 32) (97) ->
  L5.u8_at RSEGS M ((msg) + 33) (116) ->
  L5.u8_at RSEGS M ((msg) + 34) (32) ->
  L5.u8_at RSEGS M ((msg) + 35) (32) ->
  L5.u8_at RSEGS M ((msg) + 36) (60) ->
  L5.u8_at RSEGS M ((msg) + 37) (62) ->
  L5.u8_at RSEGS M ((msg) + 38) (32) ->
  L5.u8_at RSEGS M ((msg) + 39) (58) ->
  L5.u8_at RSEGS M ((msg) + 40) (48) ->
  L5.u8_at RSEGS M ((msg) + 41) (0) ->
  exists fx' R' M', msteps RSEGS (st fx R 137268 M) (st fx' R' 312384 M')
    /\ (forall i, In i KS_C1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (371656)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp - 80)
    /\ getr R' (reg 8) = Z_to_bv 64 (66)
    /\ getr R' (reg 9) = Z_to_bv 64 (msg)
    /\ getr R' (reg 10) = Z_to_bv 64 (66)
    /\ getr R' (reg 18) = Z_to_bv 64 (41)
    /\ L5.u64_at RSEGS M' ((csp) - 80) (obj)
    /\ L5.u64_at RSEGS M' ((csp) - 72) (266272)
    /\ L5.u64_at RSEGS M' ((obj) + 0) (387952)
    /\ L5.u64_at RSEGS M' ((csp) - 56) (bv_unsigned (getr R (reg 19)))
    /\ L5.u64_at RSEGS M' ((csp) - 48) (bv_unsigned (getr R (reg 18)))
    /\ L5.u64_at RSEGS M' ((csp) - 40) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' ((csp) - 32) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' ((csp) - 24) (137272)
    /\ (forall x : word, ~ ((csp) + -144 <= bv_unsigned x < (csp) + -144 + (128)) -> ~ ((obj) + 0 <= bv_unsigned x < (obj) + 0 + (8)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 H11 G2 G10 G38 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64.
  set (Vf := VAL_C1 R csp obj msg). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_C1 R csp obj msg k) by (apply VAL_VZ_C1; lia). unfold VZ_C1 in ZA.
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
Module PC2 := LibSegZ_e3c2u.
Definition KS_C2 : list nat := Eval vm_compute in (BG.kept_list 56 PC2.regs0 PC2.regs_out).
Lemma KS_C2_ok : BG.kept_ok 56 PC2.regs0 PC2.regs_out KS_C2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_1 : nth 1 PC2.regs_out (ELit 0) = ELit 137512. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_2 : nth 2 PC2.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_8 : nth 8 PC2.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_9 : nth 9 PC2.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 1072). Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_10 : nth 10 PC2.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_11 : nth 11 PC2.regs_out (ELit 0) = ELit 376040. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_12 : nth 12 PC2.regs_out (ELit 0) = ELit 256628. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_18 : nth 18 PC2.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma ro_C2_19 : nth 19 PC2.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma cells_C2 : SR.ps_cells PC2.ps0 = PC2.cells. Proof. reflexivity. Qed.
Definition VAL_C2 (R : bvmap 5 word) (csp : Z) (obj : Z) (ref : Z) (msg : Z) (v40 : Z) (v41 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 37%nat => Z_to_bv 64 ref | 38%nat => Z_to_bv 64 msg | 40%nat => Z_to_bv 64 v40 | 41%nat => Z_to_bv 64 v41 | _ => getr R (reg k) end.
Definition VZ_C2 (R : bvmap 5 word) (csp : Z) (obj : Z) (ref : Z) (msg : Z) (v40 : Z) (v41 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 37%nat => ref | 38%nat => msg | 40%nat => v40 | 41%nat => v41 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_C2 R csp obj ref msg v40 v41 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= ref < 2 ^ 64 -> 0 <= msg < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 -> 0 <= v41 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_C2 R csp obj ref msg v40 v41) (fun _ => [])) k) = VZ_C2 R csp obj ref msg v40 v41 k.
Proof.
  intros. cbn [ev]. unfold VAL_C2, VZ_C2.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3c2u_conc fx R M csp obj ref msg v40 v41 :
  getr R (reg 2) = Z_to_bv 64 (csp - 80) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 9) = Z_to_bv 64 (msg) ->
  getr R (reg 10) = Z_to_bv 64 (ref) ->
  getr R (reg 18) = Z_to_bv 64 (41) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= ref < 2 ^ 64 ->
  0 <= msg < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  0 <= v41 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 144) (64) ->
  L5.defined M ((csp) - 144) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  4096 <= ref <= 140737488355328 ->
  (ref) mod 16 = 0 ->
  L5.writable RSEGS M (ref) (66) ->
  L5.defined M (ref) (66) ->
  4096 <= msg <= 140737488355328 ->
  (msg) mod 16 = 0 ->
  L5.writable RSEGS M (msg) (48) ->
  L5.defined M (msg) (48) ->
  ((csp) + -144 + (144) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -144) ->
  ((obj) + -128 + (144) <= (ref) + 0 \/ (ref) + 0 + (66) <= (obj) + -128) ->
  ((obj) + -128 + (144) <= (msg) + 0 \/ (msg) + 0 + (48) <= (obj) + -128) ->
  ((csp) + -144 + (144) <= (ref) + 0 \/ (ref) + 0 + (66) <= (csp) + -144) ->
  ((ref) + 0 + (66) <= (msg) + 0 \/ (msg) + 0 + (48) <= (ref) + 0) ->
  ((csp) + -144 + (144) <= (msg) + 0 \/ (msg) + 0 + (48) <= (csp) + -144) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  ((ref) + 0 + (66) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (ref) + 0) ->
  ((msg) + 0 + (48) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (msg) + 0) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u64_at RSEGS M ((csp) - 72) (266272) ->
  L5.u64_at RSEGS M ((csp) - 80) (obj) ->
  L5.u8_at RSEGS M (msg) (97) ->
  L5.u8_at RSEGS M ((msg) + 1) (115) ->
  L5.u8_at RSEGS M ((msg) + 2) (115) ->
  L5.u8_at RSEGS M ((msg) + 3) (101) ->
  L5.u8_at RSEGS M ((msg) + 4) (114) ->
  L5.u8_at RSEGS M ((msg) + 5) (116) ->
  L5.u8_at RSEGS M ((msg) + 6) (105) ->
  L5.u8_at RSEGS M ((msg) + 7) (111) ->
  L5.u8_at RSEGS M ((msg) + 8) (110) ->
  L5.u8_at RSEGS M ((msg) + 9) (32) ->
  L5.u8_at RSEGS M ((msg) + 10) (39) ->
  L5.u8_at RSEGS M ((msg) + 11) (110) ->
  L5.u8_at RSEGS M ((msg) + 12) (32) ->
  L5.u8_at RSEGS M ((msg) + 13) (60) ->
  L5.u8_at RSEGS M ((msg) + 14) (32) ->
  L5.u8_at RSEGS M ((msg) + 15) (109) ->
  L5.u8_at RSEGS M ((msg) + 16) (97) ->
  L5.u8_at RSEGS M ((msg) + 17) (120) ->
  L5.u8_at RSEGS M ((msg) + 18) (95) ->
  L5.u8_at RSEGS M ((msg) + 19) (115) ->
  L5.u8_at RSEGS M ((msg) + 20) (105) ->
  L5.u8_at RSEGS M ((msg) + 21) (122) ->
  L5.u8_at RSEGS M ((msg) + 22) (101) ->
  L5.u8_at RSEGS M ((msg) + 23) (39) ->
  L5.u8_at RSEGS M ((msg) + 24) (32) ->
  L5.u8_at RSEGS M ((msg) + 25) (102) ->
  L5.u8_at RSEGS M ((msg) + 26) (97) ->
  L5.u8_at RSEGS M ((msg) + 27) (105) ->
  L5.u8_at RSEGS M ((msg) + 28) (108) ->
  L5.u8_at RSEGS M ((msg) + 29) (101) ->
  L5.u8_at RSEGS M ((msg) + 30) (100) ->
  L5.u8_at RSEGS M ((msg) + 31) (32) ->
  L5.u8_at RSEGS M ((msg) + 32) (97) ->
  L5.u8_at RSEGS M ((msg) + 33) (116) ->
  L5.u8_at RSEGS M ((msg) + 34) (32) ->
  L5.u8_at RSEGS M ((msg) + 35) (32) ->
  L5.u8_at RSEGS M ((msg) + 36) (60) ->
  L5.u8_at RSEGS M ((msg) + 37) (62) ->
  L5.u8_at RSEGS M ((msg) + 38) (32) ->
  L5.u8_at RSEGS M ((msg) + 39) (58) ->
  L5.u8_at RSEGS M ((msg) + 40) (48) ->
  L5.u8_at RSEGS M ((msg) + 41) (0) ->
  L5.u64_at RSEGS M ((csp) - 24) (137272) ->
  L5.u64_at RSEGS M ((csp) - 32) (obj) ->
  L5.u64_at RSEGS M ((csp) - 40) (csp + 1072) ->
  L5.u64_at RSEGS M ((csp) - 48) (v40) ->
  L5.u64_at RSEGS M ((csp) - 56) (v41) ->
  L5.u64_at RSEGS M ((csp) - 8) (137512) ->
  L5.u64_at RSEGS M ((csp) - 16) (obj) ->
  exists fx' R' M', msteps RSEGS (st fx R 371656 M) (st fx' R' 137532 M')
    /\ (forall i, In i KS_C2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (137512)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj)
    /\ getr R' (reg 9) = Z_to_bv 64 (csp + 1072)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj)
    /\ getr R' (reg 11) = Z_to_bv 64 (376040)
    /\ getr R' (reg 12) = Z_to_bv 64 (256628)
    /\ getr R' (reg 18) = Z_to_bv 64 (v40)
    /\ getr R' (reg 19) = Z_to_bv 64 (v41)
    /\ L5.u64_at RSEGS M' ((obj) + 0) (376080)
    /\ L5.u64_at RSEGS M' ((obj) + 8) (ref + 24)
    /\ L5.u64_at RSEGS M' ((ref) + 24) (8028075845441778529)
    /\ L5.u64_at RSEGS M' ((ref) + 32) (7863351059373564014)
    /\ L5.u64_at RSEGS M' ((ref) + 40) (2838809733452757089)
    /\ L5.u64_at RSEGS M' ((ref) + 48) (2334102023183623712)
    /\ L5.u64_at RSEGS M' ((ref) + 56) (4188416081412519009)
    /\ L5.u8_at RSEGS M' ((ref) + 64) (48)
    /\ L5.u8_at RSEGS M' ((ref) + 65) (0)
    /\ L5.u32_at RSEGS M' ((ref) + 16) (0)
    /\ L5.u64_at RSEGS M' ((ref) + 8) (41)
    /\ L5.u64_at RSEGS M' ((ref) + 0) (41)
    /\ (forall x : word, ~ ((csp) + -144 <= bv_unsigned x < (csp) + -144 + (64)) -> ~ ((obj) + 0 <= bv_unsigned x < (obj) + 0 + (16)) -> ~ ((ref) + 0 <= bv_unsigned x < (ref) + 0 + (66)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H9 H10 H18 G2 G10 G37 G38 G40 G41 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70 K71 K72 K73 K74 K75 K76 K77 K78 K79.
  set (Vf := VAL_C2 R csp obj ref msg v40 v41). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_C2 R csp obj ref msg v40 v41 k) by (apply VAL_VZ_C2; lia). unfold VZ_C2 in ZA.
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
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.uw_of_KWordw. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PC2.cells, PC2.cells0. right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1 Hy2. apply Hfr. unfold PC2.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

End L5E3AU.
