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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_e3r4u LibSegZ_e3r5u LibSegZ_e3r6u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5E3R2U.
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
Module PR4 := LibSegZ_e3r4u.
Definition KS_R4 : list nat := Eval vm_compute in (BG.kept_list 56 PR4.regs0 PR4.regs_out).
Lemma KS_R4_ok : BG.kept_ok 56 PR4.regs0 PR4.regs_out KS_R4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R4_1 : nth 1 PR4.regs_out (ELit 0) = ELit 142484. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R4_2 : nth 2 PR4.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 592). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R4_8 : nth 8 PR4.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 1072). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R4_9 : nth 9 PR4.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 944). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R4_10 : nth 10 PR4.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R4_11 : nth 11 PR4.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma cells_R4 : SR.ps_cells PR4.ps0 = PR4.cells. Proof. reflexivity. Qed.
Definition VAL_R4 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 32%nat => Z_to_bv 64 av | 33%nat => Z_to_bv 64 canary | 34%nat => Z_to_bv 64 uid | 36%nat => Z_to_bv 64 rnd | 39%nat => Z_to_bv 64 hw | _ => getr R (reg k) end.
Definition VZ_R4 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_R4 R csp obj av canary uid rnd hw : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= av < 2 ^ 64 -> 0 <= canary < 2 ^ 64 -> 0 <= uid < 2 ^ 64 -> 0 <= rnd < 2 ^ 64 -> 0 <= hw < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_R4 R csp obj av canary uid rnd hw) (fun _ => [])) k) = VZ_R4 R csp obj av canary uid rnd hw k.
Proof.
  intros. cbn [ev]. unfold VAL_R4, VZ_R4.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3r4u_conc fx R M csp obj av canary uid rnd hw :
  getr R (reg 2) = Z_to_bv 64 (csp + 528) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 32) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= av < 2 ^ 64 ->
  0 <= canary < 2 ^ 64 ->
  0 <= uid < 2 ^ 64 ->
  0 <= rnd < 2 ^ 64 ->
  0 <= hw < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 7936) (8464) ->
  L5.defined M ((csp) - 7936) (8464) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  1099511627776 <= av <= 140737488355328 ->
  (av) mod 8 = 0 ->
  ((csp) + -7936 + (8528) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -7936) ->
  ((obj) + -128 + (144) <= (av) + 0 \/ (av) + 0 + (160) <= (obj) + -128) ->
  ((csp) + -7936 + (8528) <= (av) + 0 \/ (av) + 0 + (160) <= (csp) + -7936) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u64_at RSEGS M ((obj) - 16) (0) ->
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
  L5.u64_at RSEGS M ((obj) - 8) (csp + 1008) ->
  L5.u64_at RSEGS M ((obj) - 32) (4849336966747728640) ->
  L5.u64_at RSEGS M ((csp) + 584) (141856) ->
  L5.u64_at RSEGS M ((csp) + 576) (csp + 1072) ->
  L5.u64_at RSEGS M ((csp) + 568) (csp + 944) ->
  L5.u8_at RSEGS M ((0) + 462433) (1) ->
  L5.u8_at RSEGS M ((0) + 462434) (0) ->
  L5.u8_at RSEGS M ((0) + 462435) (1) ->
  L5.u8_at RSEGS M ((0) + 462436) (0) ->
  L5.u8_at RSEGS M ((0) + 462437) (1) ->
  L5.u8_at RSEGS M ((0) + 462438) (0) ->
  exists fx' R' M', msteps RSEGS (st fx R 143876 M) (st fx' R' 142484 M')
    /\ (forall i, In i KS_R4 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (142484)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 592)
    /\ getr R' (reg 8) = Z_to_bv 64 (csp + 1072)
    /\ getr R' (reg 9) = Z_to_bv 64 (csp + 944)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = Z_to_bv 64 (0)
    /\ (forall x : word, ~ ((csp) + -7936 <= bv_unsigned x < (csp) + -7936 + (8464)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G32 G33 G34 G36 G39 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  set (Vf := VAL_R4 R csp obj av canary uid rnd hw). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_R4 R csp obj av canary uid rnd hw k) by (apply VAL_VZ_R4; lia). unfold VZ_R4 in ZA.
  assert (HR: regs_ok E PR4.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PR4.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PR4.kn0). { unfold know_ok, PR4.kn0. kn_allx ZA. }
  destruct (PR4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PR4.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PR4.regs0 PR4.regs_out 56 KS_R4 KS_R4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PR4.regs_out E' R' 1 Hregs) by lia. rewrite ro_R4_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR4.regs_out E' R' 2 Hregs) by lia. rewrite ro_R4_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR4.regs_out E' R' 8 Hregs) by lia. rewrite ro_R4_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR4.regs_out E' R' 9 Hregs) by lia. rewrite ro_R4_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR4.regs_out E' R' 10 Hregs) by lia. rewrite ro_R4_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR4.regs_out E' R' 11 Hregs) by lia. rewrite ro_R4_11. L5KP.wordE' ZA Hag. }
  rewrite cells_R4 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PR4.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PR5 := LibSegZ_e3r5u.
Definition KS_R5 : list nat := Eval vm_compute in (BG.kept_list 56 PR5.regs0 PR5.regs_out).
Lemma KS_R5_ok : BG.kept_ok 56 PR5.regs0 PR5.regs_out KS_R5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_1 : nth 1 PR5.regs_out (ELit 0) = ELit 140488. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_2 : nth 2 PR5.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 944). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_8 : nth 8 PR5.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 1072). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_9 : nth 9 PR5.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_10 : nth 10 PR5.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_11 : nth 11 PR5.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_18 : nth 18 PR5.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_19 : nth 19 PR5.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_20 : nth 20 PR5.regs_out (ELit 0) = EVar 43. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_21 : nth 21 PR5.regs_out (ELit 0) = EVar 44. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_22 : nth 22 PR5.regs_out (ELit 0) = EVar 45. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_23 : nth 23 PR5.regs_out (ELit 0) = EVar 46. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_24 : nth 24 PR5.regs_out (ELit 0) = EVar 47. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_25 : nth 25 PR5.regs_out (ELit 0) = EVar 48. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_26 : nth 26 PR5.regs_out (ELit 0) = EVar 49. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R5_27 : nth 27 PR5.regs_out (ELit 0) = EVar 50. Proof. vm_compute. reflexivity. Qed.
Lemma cells_R5 : SR.ps_cells PR5.ps0 = PR5.cells. Proof. reflexivity. Qed.
Definition VAL_R5 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (v40 : Z) (v41 : Z) (v42 : Z) (v43 : Z) (v44 : Z) (v45 : Z) (v46 : Z) (v47 : Z) (v48 : Z) (v49 : Z) (v50 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 32%nat => Z_to_bv 64 av | 33%nat => Z_to_bv 64 canary | 34%nat => Z_to_bv 64 uid | 36%nat => Z_to_bv 64 rnd | 39%nat => Z_to_bv 64 hw | 40%nat => Z_to_bv 64 v40 | 41%nat => Z_to_bv 64 v41 | 42%nat => Z_to_bv 64 v42 | 43%nat => Z_to_bv 64 v43 | 44%nat => Z_to_bv 64 v44 | 45%nat => Z_to_bv 64 v45 | 46%nat => Z_to_bv 64 v46 | 47%nat => Z_to_bv 64 v47 | 48%nat => Z_to_bv 64 v48 | 49%nat => Z_to_bv 64 v49 | 50%nat => Z_to_bv 64 v50 | _ => getr R (reg k) end.
Definition VZ_R5 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (v40 : Z) (v41 : Z) (v42 : Z) (v43 : Z) (v44 : Z) (v45 : Z) (v46 : Z) (v47 : Z) (v48 : Z) (v49 : Z) (v50 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | 40%nat => v40 | 41%nat => v41 | 42%nat => v42 | 43%nat => v43 | 44%nat => v44 | 45%nat => v45 | 46%nat => v46 | 47%nat => v47 | 48%nat => v48 | 49%nat => v49 | 50%nat => v50 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_R5 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= av < 2 ^ 64 -> 0 <= canary < 2 ^ 64 -> 0 <= uid < 2 ^ 64 -> 0 <= rnd < 2 ^ 64 -> 0 <= hw < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 -> 0 <= v41 < 2 ^ 64 -> 0 <= v42 < 2 ^ 64 -> 0 <= v43 < 2 ^ 64 -> 0 <= v44 < 2 ^ 64 -> 0 <= v45 < 2 ^ 64 -> 0 <= v46 < 2 ^ 64 -> 0 <= v47 < 2 ^ 64 -> 0 <= v48 < 2 ^ 64 -> 0 <= v49 < 2 ^ 64 -> 0 <= v50 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_R5 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50) (fun _ => [])) k) = VZ_R5 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 k.
Proof.
  intros. cbn [ev]. unfold VAL_R5, VZ_R5.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3r5u_conc fx R M csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 :
  getr R (reg 2) = Z_to_bv 64 (csp + 592) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 32) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= av < 2 ^ 64 ->
  0 <= canary < 2 ^ 64 ->
  0 <= uid < 2 ^ 64 ->
  0 <= rnd < 2 ^ 64 ->
  0 <= hw < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  0 <= v41 < 2 ^ 64 ->
  0 <= v42 < 2 ^ 64 ->
  0 <= v43 < 2 ^ 64 ->
  0 <= v44 < 2 ^ 64 ->
  0 <= v45 < 2 ^ 64 ->
  0 <= v46 < 2 ^ 64 ->
  0 <= v47 < 2 ^ 64 ->
  0 <= v48 < 2 ^ 64 ->
  0 <= v49 < 2 ^ 64 ->
  0 <= v50 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 7936) (8528) ->
  L5.defined M ((csp) - 7936) (8528) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  1099511627776 <= av <= 140737488355328 ->
  (av) mod 8 = 0 ->
  ((csp) + -7936 + (8880) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -7936) ->
  ((obj) + -128 + (144) <= (av) + 0 \/ (av) + 0 + (160) <= (obj) + -128) ->
  ((csp) + -7936 + (8880) <= (av) + 0 \/ (av) + 0 + (160) <= (csp) + -7936) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u64_at RSEGS M ((obj) - 16) (0) ->
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
  L5.u64_at RSEGS M ((obj) - 8) (csp + 1008) ->
  L5.u64_at RSEGS M ((obj) - 32) (4849336966747728640) ->
  L5.u64_at RSEGS M ((csp) + 936) (140436) ->
  L5.u64_at RSEGS M ((csp) + 928) (csp + 1072) ->
  L5.u64_at RSEGS M ((csp) + 920) (v40) ->
  L5.u64_at RSEGS M ((csp) + 912) (v41) ->
  L5.u64_at RSEGS M ((csp) + 904) (v42) ->
  L5.u64_at RSEGS M ((csp) + 896) (v43) ->
  L5.u64_at RSEGS M ((csp) + 888) (v44) ->
  L5.u64_at RSEGS M ((csp) + 880) (v45) ->
  L5.u64_at RSEGS M ((csp) + 872) (v46) ->
  L5.u64_at RSEGS M ((csp) + 864) (v47) ->
  L5.u64_at RSEGS M ((csp) + 856) (v48) ->
  L5.u64_at RSEGS M ((csp) + 848) (v49) ->
  L5.u64_at RSEGS M ((csp) + 840) (v50) ->
  L5.u8_at RSEGS M ((0) + 462433) (1) ->
  L5.u8_at RSEGS M ((0) + 462434) (0) ->
  L5.u8_at RSEGS M ((0) + 462435) (1) ->
  L5.u8_at RSEGS M ((0) + 462436) (0) ->
  L5.u8_at RSEGS M ((0) + 462437) (1) ->
  L5.u8_at RSEGS M ((0) + 462438) (0) ->
  exists fx' R' M', msteps RSEGS (st fx R 142632 M) (st fx' R' 140488 M')
    /\ (forall i, In i KS_R5 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (140488)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 944)
    /\ getr R' (reg 8) = Z_to_bv 64 (csp + 1072)
    /\ getr R' (reg 9) = Z_to_bv 64 (v40)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = Z_to_bv 64 (0)
    /\ getr R' (reg 18) = Z_to_bv 64 (v41)
    /\ getr R' (reg 19) = Z_to_bv 64 (v42)
    /\ getr R' (reg 20) = Z_to_bv 64 (v43)
    /\ getr R' (reg 21) = Z_to_bv 64 (v44)
    /\ getr R' (reg 22) = Z_to_bv 64 (v45)
    /\ getr R' (reg 23) = Z_to_bv 64 (v46)
    /\ getr R' (reg 24) = Z_to_bv 64 (v47)
    /\ getr R' (reg 25) = Z_to_bv 64 (v48)
    /\ getr R' (reg 26) = Z_to_bv 64 (v49)
    /\ getr R' (reg 27) = Z_to_bv 64 (v50)
    /\ (forall x : word, ~ ((csp) + -7936 <= bv_unsigned x < (csp) + -7936 + (8528)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G32 G33 G34 G36 G39 G40 G41 G42 G43 G44 G45 G46 G47 G48 G49 G50 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60.
  set (Vf := VAL_R5 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_R5 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 k) by (apply VAL_VZ_R5; lia). unfold VZ_R5 in ZA.
  assert (HR: regs_ok E PR5.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PR5.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PR5.kn0). { unfold know_ok, PR5.kn0. kn_allx ZA. }
  destruct (PR5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PR5.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PR5.regs0 PR5.regs_out 56 KS_R5 KS_R5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 1 Hregs) by lia. rewrite ro_R5_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 2 Hregs) by lia. rewrite ro_R5_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 8 Hregs) by lia. rewrite ro_R5_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 9 Hregs) by lia. rewrite ro_R5_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 10 Hregs) by lia. rewrite ro_R5_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 11 Hregs) by lia. rewrite ro_R5_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 18 Hregs) by lia. rewrite ro_R5_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 19 Hregs) by lia. rewrite ro_R5_19. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 20 Hregs) by lia. rewrite ro_R5_20. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 21 Hregs) by lia. rewrite ro_R5_21. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 22 Hregs) by lia. rewrite ro_R5_22. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 23 Hregs) by lia. rewrite ro_R5_23. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 24 Hregs) by lia. rewrite ro_R5_24. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 25 Hregs) by lia. rewrite ro_R5_25. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 26 Hregs) by lia. rewrite ro_R5_26. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR5.regs_out E' R' 27 Hregs) by lia. rewrite ro_R5_27. L5KP.wordE' ZA Hag. }
  rewrite cells_R5 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PR5.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PR6 := LibSegZ_e3r6u.
Definition KS_R6 : list nat := Eval vm_compute in (BG.kept_list 56 PR6.regs0 PR6.regs_out).
Lemma KS_R6_ok : BG.kept_ok 56 PR6.regs0 PR6.regs_out KS_R6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R6_1 : nth 1 PR6.regs_out (ELit 0) = ELit 133556. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R6_2 : nth 2 PR6.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 1008). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R6_8 : nth 8 PR6.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R6_10 : nth 10 PR6.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R6_11 : nth 11 PR6.regs_out (ELit 0) = ELit 1. Proof. vm_compute. reflexivity. Qed.
Lemma cells_R6 : SR.ps_cells PR6.ps0 = PR6.cells. Proof. reflexivity. Qed.
Definition VAL_R6 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 32%nat => Z_to_bv 64 av | 33%nat => Z_to_bv 64 canary | 34%nat => Z_to_bv 64 uid | 36%nat => Z_to_bv 64 rnd | 39%nat => Z_to_bv 64 hw | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_R6 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_R6 R csp obj av canary uid rnd hw v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= av < 2 ^ 64 -> 0 <= canary < 2 ^ 64 -> 0 <= uid < 2 ^ 64 -> 0 <= rnd < 2 ^ 64 -> 0 <= hw < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_R6 R csp obj av canary uid rnd hw v40) (fun _ => [])) k) = VZ_R6 R csp obj av canary uid rnd hw v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_R6, VZ_R6.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3r6u_conc fx R M csp obj av canary uid rnd hw v40 :
  getr R (reg 2) = Z_to_bv 64 (csp + 944) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 32) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= av < 2 ^ 64 ->
  0 <= canary < 2 ^ 64 ->
  0 <= uid < 2 ^ 64 ->
  0 <= rnd < 2 ^ 64 ->
  0 <= hw < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 7936) (8880) ->
  L5.defined M ((csp) - 7936) (8880) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  1099511627776 <= av <= 140737488355328 ->
  (av) mod 8 = 0 ->
  ((csp) + -7936 + (8944) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -7936) ->
  ((obj) + -128 + (144) <= (av) + 0 \/ (av) + 0 + (160) <= (obj) + -128) ->
  ((csp) + -7936 + (8944) <= (av) + 0 \/ (av) + 0 + (160) <= (csp) + -7936) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u64_at RSEGS M ((obj) - 16) (0) ->
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
  L5.u64_at RSEGS M ((obj) - 8) (csp + 1008) ->
  L5.u64_at RSEGS M ((obj) - 32) (4849336966747728640) ->
  L5.u64_at RSEGS M ((csp) + 984) (134416) ->
  L5.u64_at RSEGS M ((csp) + 976) (csp + 1104) ->
  L5.u64_at RSEGS M ((csp) + 1000) (133204) ->
  L5.u64_at RSEGS M ((csp) + 992) (v40) ->
  L5.u32_at RSEGS M ((obj) - 68) (1) ->
  L5.u64_at RSEGS M ((obj) - 48) (133556) ->
  L5.u8_at RSEGS M ((0) + 462433) (1) ->
  L5.u8_at RSEGS M ((0) + 462434) (0) ->
  L5.u8_at RSEGS M ((0) + 462435) (1) ->
  L5.u8_at RSEGS M ((0) + 462436) (0) ->
  L5.u8_at RSEGS M ((0) + 462437) (1) ->
  L5.u8_at RSEGS M ((0) + 462438) (0) ->
  exists fx' R' M', msteps RSEGS (st fx R 140528 M) (st fx' R' 133556 M')
    /\ (forall i, In i KS_R6 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (133556)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 1008)
    /\ getr R' (reg 8) = Z_to_bv 64 (v40)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = Z_to_bv 64 (1)
    /\ (forall x : word, ~ ((csp) + -7936 <= bv_unsigned x < (csp) + -7936 + (8880)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G32 G33 G34 G36 G39 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53.
  set (Vf := VAL_R6 R csp obj av canary uid rnd hw v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_R6 R csp obj av canary uid rnd hw v40 k) by (apply VAL_VZ_R6; lia). unfold VZ_R6 in ZA.
  assert (HR: regs_ok E PR6.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PR6.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PR6.kn0). { unfold know_ok, PR6.kn0. kn_allx ZA. }
  destruct (PR6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PR6.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PR6.regs0 PR6.regs_out 56 KS_R6 KS_R6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PR6.regs_out E' R' 1 Hregs) by lia. rewrite ro_R6_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR6.regs_out E' R' 2 Hregs) by lia. rewrite ro_R6_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR6.regs_out E' R' 8 Hregs) by lia. rewrite ro_R6_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR6.regs_out E' R' 10 Hregs) by lia. rewrite ro_R6_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR6.regs_out E' R' 11 Hregs) by lia. rewrite ro_R6_11. L5KP.wordE' ZA Hag. }
  rewrite cells_R6 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PR6.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

End L5E3R2U.
