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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5E3P.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5E3P.
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
Module PP1 := LibSegZ_e3p1.
Definition KS_P1 : list nat := Eval vm_compute in (BG.kept_list 56 PP1.regs0 PP1.regs_out).
Lemma KS_P1_ok : BG.kept_ok 56 PP1.regs0 PP1.regs_out KS_P1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1_1 : nth 1 PP1.regs_out (ELit 0) = ELit 136400. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1_2 : nth 2 PP1.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1_9 : nth 9 PP1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1_10 : nth 10 PP1.regs_out (ELit 0) = EVar 38. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1_11 : nth 11 PP1.regs_out (ELit 0) = ELit 48. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P1 : SR.ps_cells PP1.ps0 = PP1.cells. Proof. reflexivity. Qed.
Definition VAL_P1 (R : bvmap 5 word) (csp : Z) (obj : Z) (msg : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 38%nat => Z_to_bv 64 msg | _ => getr R (reg k) end.
Definition VZ_P1 (R : bvmap 5 word) (csp : Z) (obj : Z) (msg : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 38%nat => msg | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P1 R csp obj msg : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= msg < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P1 R csp obj msg) (fun _ => [])) k) = VZ_P1 R csp obj msg k.
Proof.
  intros. cbn [ev]. unfold VAL_P1, VZ_P1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3p1_conc fx R M csp obj msg :
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 32) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= msg < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 64) (64) ->
  L5.defined M ((csp) - 64) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  4096 <= msg <= 140737488355328 ->
  (msg) mod 16 = 0 ->
  L5.writable RSEGS M (msg) (48) ->
  L5.defined M (msg) (48) ->
  ((csp) + -64 + (96) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -64) ->
  ((obj) + -128 + (144) <= (msg) + 0 \/ (msg) + 0 + (48) <= (obj) + -128) ->
  ((csp) + -64 + (96) <= (msg) + 0 \/ (msg) + 0 + (48) <= (csp) + -64) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  ((msg) + 0 + (48) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (msg) + 0) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u64_at RSEGS M (csp) (49) ->
  L5.u64_at RSEGS M ((csp) + 16) (msg) ->
  exists fx' R' M', msteps RSEGS (st fx R 136368 M) (st fx' R' 309252 M')
    /\ (forall i, In i KS_P1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (136400)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp)
    /\ getr R' (reg 9) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 10) = Z_to_bv 64 (msg)
    /\ getr R' (reg 11) = Z_to_bv 64 (48)
    /\ (forall x : word, ~ ((csp) + -64 <= bv_unsigned x < (csp) + -64 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G38 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22.
  set (Vf := VAL_P1 R csp obj msg). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P1 R csp obj msg k) by (apply VAL_VZ_P1; lia). unfold VZ_P1 in ZA.
  assert (HR: regs_ok E PP1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP1.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP1.kn0). { unfold know_ok, PP1.kn0. kn_allx ZA. }
  destruct (PP1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP1.regs0 PP1.regs_out 56 KS_P1 KS_P1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP1.regs_out E' R' 1 Hregs) by lia. rewrite ro_P1_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1.regs_out E' R' 2 Hregs) by lia. rewrite ro_P1_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1.regs_out E' R' 9 Hregs) by lia. rewrite ro_P1_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1.regs_out E' R' 10 Hregs) by lia. rewrite ro_P1_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1.regs_out E' R' 11 Hregs) by lia. rewrite ro_P1_11. L5KP.wordE' ZA Hag. }
  rewrite cells_P1 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PP1.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP1B := LibSegZ_e3p1b.
Definition KS_P1B : list nat := Eval vm_compute in (BG.kept_list 56 PP1B.regs0 PP1B.regs_out).
Lemma KS_P1B_ok : BG.kept_ok 56 PP1B.regs0 PP1B.regs_out KS_P1B = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1B_2 : nth 2 PP1B.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1B_9 : nth 9 PP1B.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1B_10 : nth 10 PP1B.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1B_11 : nth 11 PP1B.regs_out (ELit 0) = EVar 11. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P1B : SR.ps_cells PP1B.ps0 = PP1B.cells. Proof. reflexivity. Qed.
Definition VAL_P1B (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_P1B (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P1B R csp obj v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P1B R csp obj v40) (fun _ => [])) k) = VZ_P1B R csp obj v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_P1B, VZ_P1B.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3p1b_conc fx R M csp obj v40 :
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 9) = Z_to_bv 64 (obj - 32) ->
  getr R (reg 10) = Z_to_bv 64 (v40) ->
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
  ((csp) + -64 + (64) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -64) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  exists fx' R' M', msteps RSEGS (st fx R 136400 M) (st fx' R' 136420 M')
    /\ (forall i, In i KS_P1B -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (csp)
    /\ getr R' (reg 9) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = getr R (reg 11)
    /\ (forall x : word, ~ ((csp) + -64 <= bv_unsigned x < (csp) + -64 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H9 H10 G2 G10 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13.
  set (Vf := VAL_P1B R csp obj v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P1B R csp obj v40 k) by (apply VAL_VZ_P1B; lia). unfold VZ_P1B in ZA.
  assert (HR: regs_ok E PP1B.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP1B.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP1B.kn0). { unfold know_ok, PP1B.kn0. kn_allx ZA. }
  destruct (PP1B.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP1B.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP1B.regs0 PP1B.regs_out 56 KS_P1B KS_P1B_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP1B.regs_out E' R' 2 Hregs) by lia. rewrite ro_P1B_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1B.regs_out E' R' 9 Hregs) by lia. rewrite ro_P1B_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1B.regs_out E' R' 10 Hregs) by lia. rewrite ro_P1B_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1B.regs_out E' R' 11 Hregs) by lia. rewrite ro_P1B_11. cbn [edenot]. rewrite <- (proj1 Hag 11%nat) by lia. reflexivity. }
  rewrite cells_P1B in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PP1B.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP2 := LibSegZ_e3p2.
Definition KS_P2 : list nat := Eval vm_compute in (BG.kept_list 56 PP2.regs0 PP2.regs_out).
Lemma KS_P2_ok : BG.kept_ok 56 PP2.regs0 PP2.regs_out KS_P2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2_1 : nth 1 PP2.regs_out (ELit 0) = ELit 140316. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2_2 : nth 2 PP2.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 128). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2_8 : nth 8 PP2.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2_10 : nth 10 PP2.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2_11 : nth 11 PP2.regs_out (ELit 0) = ELit 64. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P2 : SR.ps_cells PP2.ps0 = PP2.cells. Proof. reflexivity. Qed.
Definition VAL_P2 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (v41 : Z) (v42 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | 41%nat => Z_to_bv 64 v41 | 42%nat => Z_to_bv 64 v42 | _ => getr R (reg k) end.
Definition VZ_P2 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (v41 : Z) (v42 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | 41%nat => v41 | 42%nat => v42 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P2 R csp obj v40 v41 v42 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 -> 0 <= v41 < 2 ^ 64 -> 0 <= v42 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P2 R csp obj v40 v41 v42) (fun _ => [])) k) = VZ_P2 R csp obj v40 v41 v42 k.
Proof.
  intros. cbn [ev]. unfold VAL_P2, VZ_P2.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3p2_conc fx R M csp obj v40 v41 v42 :
  getr R (reg 2) = Z_to_bv 64 (csp + 128) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 32) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  0 <= v41 < 2 ^ 64 ->
  0 <= v42 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 64) (64) ->
  L5.defined M ((csp) + 64) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + 64 + (208) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 64) ->
  ((obj) + -128 + (144) <= (v42) + 0 \/ (v42) + 0 + (64) <= (obj) + -128) ->
  ((csp) + 64 + (208) <= (v42) + 0 \/ (v42) + 0 + (64) <= (csp) + 64) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  ((v42) + 0 + (64) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (v42) + 0) ->
  0 <= v40 <= 255 ->
  0 <= v41 <= 255 ->
  4096 <= v42 <= 140737488355328 ->
  (v42) mod 16 = 0 ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u8_at RSEGS M ((csp) + 200) (Z.land (v40) (254)) ->
  L5.u8_at RSEGS M ((csp) + 232) (Z.lor (Z.land (v41) (254)) (1)) ->
  L5.u64_at RSEGS M ((csp) + 256) (v42) ->
  L5.u64_at RSEGS M ((csp) + 248) (8) ->
  exists fx' R' M', msteps RSEGS (st fx R 140248 M) (st fx' R' 309252 M')
    /\ (forall i, In i KS_P2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (140316)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 128)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 10) = Z_to_bv 64 (v42)
    /\ getr R' (reg 11) = Z_to_bv 64 (64)
    /\ (forall x : word, ~ ((csp) + 64 <= bv_unsigned x < (csp) + 64 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G40 G41 G42 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24.
  set (Vf := VAL_P2 R csp obj v40 v41 v42). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P2 R csp obj v40 v41 v42 k) by (apply VAL_VZ_P2; lia). unfold VZ_P2 in ZA.
  assert (HR: regs_ok E PP2.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP2.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP2.kn0). { unfold know_ok, PP2.kn0. kn_allx ZA. }
  destruct (PP2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP2.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP2.regs0 PP2.regs_out 56 KS_P2 KS_P2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP2.regs_out E' R' 1 Hregs) by lia. rewrite ro_P2_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2.regs_out E' R' 2 Hregs) by lia. rewrite ro_P2_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2.regs_out E' R' 8 Hregs) by lia. rewrite ro_P2_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2.regs_out E' R' 10 Hregs) by lia. rewrite ro_P2_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2.regs_out E' R' 11 Hregs) by lia. rewrite ro_P2_11. L5KP.wordE' ZA Hag. }
  rewrite cells_P2 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PP2.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP2B := LibSegZ_e3p2b.
Definition KS_P2B : list nat := Eval vm_compute in (BG.kept_list 56 PP2B.regs0 PP2B.regs_out).
Lemma KS_P2B_ok : BG.kept_ok 56 PP2B.regs0 PP2B.regs_out KS_P2B = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2B_1 : nth 1 PP2B.regs_out (ELit 0) = ELit 140348. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2B_2 : nth 2 PP2B.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 128). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2B_10 : nth 10 PP2B.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2B_11 : nth 11 PP2B.regs_out (ELit 0) = ELit 64. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P2B : SR.ps_cells PP2B.ps0 = PP2B.cells. Proof. reflexivity. Qed.
Definition VAL_P2B (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (v41 : Z) (v42 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | 41%nat => Z_to_bv 64 v41 | 42%nat => Z_to_bv 64 v42 | _ => getr R (reg k) end.
Definition VZ_P2B (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (v41 : Z) (v42 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | 41%nat => v41 | 42%nat => v42 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P2B R csp obj v40 v41 v42 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 -> 0 <= v41 < 2 ^ 64 -> 0 <= v42 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P2B R csp obj v40 v41 v42) (fun _ => [])) k) = VZ_P2B R csp obj v40 v41 v42 k.
Proof.
  intros. cbn [ev]. unfold VAL_P2B, VZ_P2B.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3p2b_conc fx R M csp obj v40 v41 v42 :
  getr R (reg 2) = Z_to_bv 64 (csp + 128) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (v40) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  0 <= v41 < 2 ^ 64 ->
  0 <= v42 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 64) (64) ->
  L5.defined M ((csp) + 64) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + 64 + (240) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 64) ->
  ((obj) + -128 + (144) <= (v42) + 0 \/ (v42) + 0 + (64) <= (obj) + -128) ->
  ((csp) + 64 + (240) <= (v42) + 0 \/ (v42) + 0 + (64) <= (csp) + 64) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  ((v42) + 0 + (64) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (v42) + 0) ->
  0 <= v41 <= 255 ->
  4096 <= v42 <= 140737488355328 ->
  (v42) mod 16 = 0 ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u8_at RSEGS M ((csp) + 264) (Z.lor (Z.land (v41) (254)) (1)) ->
  L5.u64_at RSEGS M ((csp) + 288) (v42) ->
  L5.u64_at RSEGS M ((csp) + 280) (8) ->
  exists fx' R' M', msteps RSEGS (st fx R 140316 M) (st fx' R' 309252 M')
    /\ (forall i, In i KS_P2B -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (140348)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 128)
    /\ getr R' (reg 10) = Z_to_bv 64 (v42)
    /\ getr R' (reg 11) = Z_to_bv 64 (64)
    /\ (forall x : word, ~ ((csp) + 64 <= bv_unsigned x < (csp) + 64 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G40 G41 G42 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22.
  set (Vf := VAL_P2B R csp obj v40 v41 v42). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P2B R csp obj v40 v41 v42 k) by (apply VAL_VZ_P2B; lia). unfold VZ_P2B in ZA.
  assert (HR: regs_ok E PP2B.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP2B.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP2B.kn0). { unfold know_ok, PP2B.kn0. kn_allx ZA. }
  destruct (PP2B.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP2B.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP2B.regs0 PP2B.regs_out 56 KS_P2B KS_P2B_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP2B.regs_out E' R' 1 Hregs) by lia. rewrite ro_P2B_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2B.regs_out E' R' 2 Hregs) by lia. rewrite ro_P2B_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2B.regs_out E' R' 10 Hregs) by lia. rewrite ro_P2B_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2B.regs_out E' R' 11 Hregs) by lia. rewrite ro_P2B_11. L5KP.wordE' ZA Hag. }
  rewrite cells_P2B in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PP2B.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP2C := LibSegZ_e3p2c.
Definition KS_P2C : list nat := Eval vm_compute in (BG.kept_list 56 PP2C.regs0 PP2C.regs_out).
Lemma KS_P2C_ok : BG.kept_ok 56 PP2C.regs0 PP2C.regs_out KS_P2C = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2C_2 : nth 2 PP2C.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 128). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2C_8 : nth 8 PP2C.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2C_10 : nth 10 PP2C.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2C_11 : nth 11 PP2C.regs_out (ELit 0) = EVar 11. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P2C : SR.ps_cells PP2C.ps0 = PP2C.cells. Proof. reflexivity. Qed.
Definition VAL_P2C (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (v41 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | 41%nat => Z_to_bv 64 v41 | _ => getr R (reg k) end.
Definition VZ_P2C (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (v41 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | 41%nat => v41 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P2C R csp obj v40 v41 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 -> 0 <= v41 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P2C R csp obj v40 v41) (fun _ => [])) k) = VZ_P2C R csp obj v40 v41 k.
Proof.
  intros. cbn [ev]. unfold VAL_P2C, VZ_P2C.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3p2c_conc fx R M csp obj v40 v41 :
  getr R (reg 2) = Z_to_bv 64 (csp + 128) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 8) = Z_to_bv 64 (obj - 32) ->
  getr R (reg 10) = Z_to_bv 64 (v40) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  0 <= v41 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 64) (64) ->
  L5.defined M ((csp) + 64) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + 64 + (240) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 64) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  0 <= v41 <= 255 ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u8_at RSEGS M ((csp) + 296) (Z.land (v41) (254)) ->
  exists fx' R' M', msteps RSEGS (st fx R 140348 M) (st fx' R' 140392 M')
    /\ (forall i, In i KS_P2C -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 128)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = getr R (reg 11)
    /\ (forall x : word, ~ ((csp) + 64 <= bv_unsigned x < (csp) + 64 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H8 H10 G2 G10 G40 G41 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  set (Vf := VAL_P2C R csp obj v40 v41). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P2C R csp obj v40 v41 k) by (apply VAL_VZ_P2C; lia). unfold VZ_P2C in ZA.
  assert (HR: regs_ok E PP2C.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP2C.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP2C.kn0). { unfold know_ok, PP2C.kn0. kn_allx ZA. }
  destruct (PP2C.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP2C.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP2C.regs0 PP2C.regs_out 56 KS_P2C KS_P2C_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP2C.regs_out E' R' 2 Hregs) by lia. rewrite ro_P2C_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2C.regs_out E' R' 8 Hregs) by lia. rewrite ro_P2C_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2C.regs_out E' R' 10 Hregs) by lia. rewrite ro_P2C_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2C.regs_out E' R' 11 Hregs) by lia. rewrite ro_P2C_11. cbn [edenot]. rewrite <- (proj1 Hag 11%nat) by lia. reflexivity. }
  rewrite cells_P2C in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PP2C.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP3 := LibSegZ_e3p3.
Definition KS_P3 : list nat := Eval vm_compute in (BG.kept_list 56 PP3.regs0 PP3.regs_out).
Lemma KS_P3_ok : BG.kept_ok 56 PP3.regs0 PP3.regs_out KS_P3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P3_2 : nth 2 PP3.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 432). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P3_8 : nth 8 PP3.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P3_10 : nth 10 PP3.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P3_11 : nth 11 PP3.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P3 : SR.ps_cells PP3.ps0 = PP3.cells. Proof. reflexivity. Qed.
Definition VAL_P3 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_P3 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P3 R csp obj v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P3 R csp obj v40) (fun _ => [])) k) = VZ_P3 R csp obj v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_P3, VZ_P3.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3p3_conc fx R M csp obj v40 :
  getr R (reg 2) = Z_to_bv 64 (csp + 432) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 32) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 368) (64) ->
  L5.defined M ((csp) + 368) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + 368 + (80) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 368) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  0 <= v40 <= 255 ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u8_at RSEGS M ((csp) + 432) (Z.land (v40) (254)) ->
  exists fx' R' M', msteps RSEGS (st fx R 142188 M) (st fx' R' 142228 M')
    /\ (forall i, In i KS_P3 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 432)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = Z_to_bv 64 (0)
    /\ (forall x : word, ~ ((csp) + 368 <= bv_unsigned x < (csp) + 368 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  set (Vf := VAL_P3 R csp obj v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P3 R csp obj v40 k) by (apply VAL_VZ_P3; lia). unfold VZ_P3 in ZA.
  assert (HR: regs_ok E PP3.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP3.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP3.kn0). { unfold know_ok, PP3.kn0. kn_allx ZA. }
  destruct (PP3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP3.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP3.regs0 PP3.regs_out 56 KS_P3 KS_P3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP3.regs_out E' R' 2 Hregs) by lia. rewrite ro_P3_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP3.regs_out E' R' 8 Hregs) by lia. rewrite ro_P3_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP3.regs_out E' R' 10 Hregs) by lia. rewrite ro_P3_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP3.regs_out E' R' 11 Hregs) by lia. rewrite ro_P3_11. L5KP.wordE' ZA Hag. }
  rewrite cells_P3 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PP3.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP4 := LibSegZ_e3p4.
Definition KS_P4 : list nat := Eval vm_compute in (BG.kept_list 56 PP4.regs0 PP4.regs_out).
Lemma KS_P4_ok : BG.kept_ok 56 PP4.regs0 PP4.regs_out KS_P4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P4_2 : nth 2 PP4.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 480). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P4_8 : nth 8 PP4.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P4_10 : nth 10 PP4.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P4_11 : nth 11 PP4.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P4 : SR.ps_cells PP4.ps0 = PP4.cells. Proof. reflexivity. Qed.
Definition VAL_P4 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_P4 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P4 R csp obj v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P4 R csp obj v40) (fun _ => [])) k) = VZ_P4 R csp obj v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_P4, VZ_P4.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3p4_conc fx R M csp obj v40 :
  getr R (reg 2) = Z_to_bv 64 (csp + 480) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 32) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 416) (64) ->
  L5.defined M ((csp) + 416) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + 416 + (80) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 416) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  0 <= v40 <= 255 ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u8_at RSEGS M ((csp) + 488) (Z.land (v40) (254)) ->
  exists fx' R' M', msteps RSEGS (st fx R 141340 M) (st fx' R' 141380 M')
    /\ (forall i, In i KS_P4 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 480)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = Z_to_bv 64 (0)
    /\ (forall x : word, ~ ((csp) + 416 <= bv_unsigned x < (csp) + 416 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  set (Vf := VAL_P4 R csp obj v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P4 R csp obj v40 k) by (apply VAL_VZ_P4; lia). unfold VZ_P4 in ZA.
  assert (HR: regs_ok E PP4.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP4.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP4.kn0). { unfold know_ok, PP4.kn0. kn_allx ZA. }
  destruct (PP4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP4.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP4.regs0 PP4.regs_out 56 KS_P4 KS_P4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP4.regs_out E' R' 2 Hregs) by lia. rewrite ro_P4_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP4.regs_out E' R' 8 Hregs) by lia. rewrite ro_P4_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP4.regs_out E' R' 10 Hregs) by lia. rewrite ro_P4_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP4.regs_out E' R' 11 Hregs) by lia. rewrite ro_P4_11. L5KP.wordE' ZA Hag. }
  rewrite cells_P4 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PP4.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP5 := LibSegZ_e3p5.
Definition KS_P5 : list nat := Eval vm_compute in (BG.kept_list 56 PP5.regs0 PP5.regs_out).
Lemma KS_P5_ok : BG.kept_ok 56 PP5.regs0 PP5.regs_out KS_P5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P5_1 : nth 1 PP5.regs_out (ELit 0) = ELit 140348. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P5_2 : nth 2 PP5.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 544). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P5_8 : nth 8 PP5.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P5_10 : nth 10 PP5.regs_out (ELit 0) = EVar 43. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P5_11 : nth 11 PP5.regs_out (ELit 0) = ELit 64. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P5 : SR.ps_cells PP5.ps0 = PP5.cells. Proof. reflexivity. Qed.
Definition VAL_P5 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (v41 : Z) (v42 : Z) (v43 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | 41%nat => Z_to_bv 64 v41 | 42%nat => Z_to_bv 64 v42 | 43%nat => Z_to_bv 64 v43 | _ => getr R (reg k) end.
Definition VZ_P5 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (v41 : Z) (v42 : Z) (v43 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | 41%nat => v41 | 42%nat => v42 | 43%nat => v43 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P5 R csp obj v40 v41 v42 v43 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 -> 0 <= v41 < 2 ^ 64 -> 0 <= v42 < 2 ^ 64 -> 0 <= v43 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P5 R csp obj v40 v41 v42 v43) (fun _ => [])) k) = VZ_P5 R csp obj v40 v41 v42 v43 k.
Proof.
  intros. cbn [ev]. unfold VAL_P5, VZ_P5.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3p5_conc fx R M csp obj v40 v41 v42 v43 :
  getr R (reg 2) = Z_to_bv 64 (csp + 544) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 32) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  0 <= v41 < 2 ^ 64 ->
  0 <= v42 < 2 ^ 64 ->
  0 <= v43 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 480) (64) ->
  L5.defined M ((csp) + 480) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + 480 + (240) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 480) ->
  ((obj) + -128 + (144) <= (v43) + 0 \/ (v43) + 0 + (64) <= (obj) + -128) ->
  ((csp) + 480 + (240) <= (v43) + 0 \/ (v43) + 0 + (64) <= (csp) + 480) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  ((v43) + 0 + (64) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (v43) + 0) ->
  0 <= v40 <= 255 ->
  0 <= v41 <= 255 ->
  0 <= v42 <= 255 ->
  4096 <= v43 <= 140737488355328 ->
  (v43) mod 16 = 0 ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u8_at RSEGS M ((csp) + 616) (Z.land (v40) (254)) ->
  L5.u8_at RSEGS M ((csp) + 648) (Z.land (v41) (254)) ->
  L5.u8_at RSEGS M ((csp) + 680) (Z.lor (Z.land (v42) (254)) (1)) ->
  L5.u64_at RSEGS M ((csp) + 704) (v43) ->
  L5.u64_at RSEGS M ((csp) + 696) (8) ->
  exists fx' R' M', msteps RSEGS (st fx R 140244 M) (st fx' R' 309252 M')
    /\ (forall i, In i KS_P5 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (140348)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 544)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 10) = Z_to_bv 64 (v43)
    /\ getr R' (reg 11) = Z_to_bv 64 (64)
    /\ (forall x : word, ~ ((csp) + 480 <= bv_unsigned x < (csp) + 480 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G40 G41 G42 G43 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26.
  set (Vf := VAL_P5 R csp obj v40 v41 v42 v43). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P5 R csp obj v40 v41 v42 v43 k) by (apply VAL_VZ_P5; lia). unfold VZ_P5 in ZA.
  assert (HR: regs_ok E PP5.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP5.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP5.kn0). { unfold know_ok, PP5.kn0. kn_allx ZA. }
  destruct (PP5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP5.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP5.regs0 PP5.regs_out 56 KS_P5 KS_P5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP5.regs_out E' R' 1 Hregs) by lia. rewrite ro_P5_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP5.regs_out E' R' 2 Hregs) by lia. rewrite ro_P5_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP5.regs_out E' R' 8 Hregs) by lia. rewrite ro_P5_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP5.regs_out E' R' 10 Hregs) by lia. rewrite ro_P5_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP5.regs_out E' R' 11 Hregs) by lia. rewrite ro_P5_11. L5KP.wordE' ZA Hag. }
  rewrite cells_P5 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PP5.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP5B := LibSegZ_e3p5b.
Definition KS_P5B : list nat := Eval vm_compute in (BG.kept_list 56 PP5B.regs0 PP5B.regs_out).
Lemma KS_P5B_ok : BG.kept_ok 56 PP5B.regs0 PP5B.regs_out KS_P5B = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P5B_1 : nth 1 PP5B.regs_out (ELit 0) = ELit 140388. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P5B_2 : nth 2 PP5B.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 544). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P5B_10 : nth 10 PP5B.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P5B_11 : nth 11 PP5B.regs_out (ELit 0) = ELit 64. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P5B : SR.ps_cells PP5B.ps0 = PP5B.cells. Proof. reflexivity. Qed.
Definition VAL_P5B (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (v41 : Z) (v42 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | 41%nat => Z_to_bv 64 v41 | 42%nat => Z_to_bv 64 v42 | _ => getr R (reg k) end.
Definition VZ_P5B (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (v41 : Z) (v42 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | 41%nat => v41 | 42%nat => v42 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P5B R csp obj v40 v41 v42 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 -> 0 <= v41 < 2 ^ 64 -> 0 <= v42 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P5B R csp obj v40 v41 v42) (fun _ => [])) k) = VZ_P5B R csp obj v40 v41 v42 k.
Proof.
  intros. cbn [ev]. unfold VAL_P5B, VZ_P5B.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3p5b_conc fx R M csp obj v40 v41 v42 :
  getr R (reg 2) = Z_to_bv 64 (csp + 544) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (v40) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  0 <= v41 < 2 ^ 64 ->
  0 <= v42 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 480) (64) ->
  L5.defined M ((csp) + 480) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + 480 + (272) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 480) ->
  ((obj) + -128 + (144) <= (v42) + 0 \/ (v42) + 0 + (64) <= (obj) + -128) ->
  ((csp) + 480 + (272) <= (v42) + 0 \/ (v42) + 0 + (64) <= (csp) + 480) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  ((v42) + 0 + (64) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (v42) + 0) ->
  0 <= v41 <= 255 ->
  4096 <= v42 <= 140737488355328 ->
  (v42) mod 16 = 0 ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u8_at RSEGS M ((csp) + 712) (Z.lor (Z.land (v41) (254)) (1)) ->
  L5.u64_at RSEGS M ((csp) + 736) (v42) ->
  L5.u64_at RSEGS M ((csp) + 728) (8) ->
  exists fx' R' M', msteps RSEGS (st fx R 140348 M) (st fx' R' 309252 M')
    /\ (forall i, In i KS_P5B -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (140388)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 544)
    /\ getr R' (reg 10) = Z_to_bv 64 (v42)
    /\ getr R' (reg 11) = Z_to_bv 64 (64)
    /\ (forall x : word, ~ ((csp) + 480 <= bv_unsigned x < (csp) + 480 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G40 G41 G42 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22.
  set (Vf := VAL_P5B R csp obj v40 v41 v42). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P5B R csp obj v40 v41 v42 k) by (apply VAL_VZ_P5B; lia). unfold VZ_P5B in ZA.
  assert (HR: regs_ok E PP5B.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP5B.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP5B.kn0). { unfold know_ok, PP5B.kn0. kn_allx ZA. }
  destruct (PP5B.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP5B.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP5B.regs0 PP5B.regs_out 56 KS_P5B KS_P5B_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP5B.regs_out E' R' 1 Hregs) by lia. rewrite ro_P5B_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP5B.regs_out E' R' 2 Hregs) by lia. rewrite ro_P5B_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP5B.regs_out E' R' 10 Hregs) by lia. rewrite ro_P5B_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP5B.regs_out E' R' 11 Hregs) by lia. rewrite ro_P5B_11. L5KP.wordE' ZA Hag. }
  rewrite cells_P5B in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PP5B.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP5C := LibSegZ_e3p5c.
Definition KS_P5C : list nat := Eval vm_compute in (BG.kept_list 56 PP5C.regs0 PP5C.regs_out).
Lemma KS_P5C_ok : BG.kept_ok 56 PP5C.regs0 PP5C.regs_out KS_P5C = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P5C_2 : nth 2 PP5C.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 544). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P5C_8 : nth 8 PP5C.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P5C_10 : nth 10 PP5C.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P5C_11 : nth 11 PP5C.regs_out (ELit 0) = EVar 11. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P5C : SR.ps_cells PP5C.ps0 = PP5C.cells. Proof. reflexivity. Qed.
Definition VAL_P5C (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_P5C (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P5C R csp obj v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P5C R csp obj v40) (fun _ => [])) k) = VZ_P5C R csp obj v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_P5C, VZ_P5C.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3p5c_conc fx R M csp obj v40 :
  getr R (reg 2) = Z_to_bv 64 (csp + 544) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 8) = Z_to_bv 64 (obj - 32) ->
  getr R (reg 10) = Z_to_bv 64 (v40) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 480) (64) ->
  L5.defined M ((csp) + 480) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + 480 + (64) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 480) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  exists fx' R' M', msteps RSEGS (st fx R 140388 M) (st fx' R' 140392 M')
    /\ (forall i, In i KS_P5C -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 544)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = getr R (reg 11)
    /\ (forall x : word, ~ ((csp) + 480 <= bv_unsigned x < (csp) + 480 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H8 H10 G2 G10 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13.
  set (Vf := VAL_P5C R csp obj v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P5C R csp obj v40 k) by (apply VAL_VZ_P5C; lia). unfold VZ_P5C in ZA.
  assert (HR: regs_ok E PP5C.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP5C.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP5C.kn0). { unfold know_ok, PP5C.kn0. kn_allx ZA. }
  destruct (PP5C.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP5C.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP5C.regs0 PP5C.regs_out 56 KS_P5C KS_P5C_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP5C.regs_out E' R' 2 Hregs) by lia. rewrite ro_P5C_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP5C.regs_out E' R' 8 Hregs) by lia. rewrite ro_P5C_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP5C.regs_out E' R' 10 Hregs) by lia. rewrite ro_P5C_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP5C.regs_out E' R' 11 Hregs) by lia. rewrite ro_P5C_11. cbn [edenot]. rewrite <- (proj1 Hag 11%nat) by lia. reflexivity. }
  rewrite cells_P5C in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PP5C.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP6 := LibSegZ_e3p6.
Definition KS_P6 : list nat := Eval vm_compute in (BG.kept_list 56 PP6.regs0 PP6.regs_out).
Lemma KS_P6_ok : BG.kept_ok 56 PP6.regs0 PP6.regs_out KS_P6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P6_2 : nth 2 PP6.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 848). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P6_8 : nth 8 PP6.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P6_10 : nth 10 PP6.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P6_11 : nth 11 PP6.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P6 : SR.ps_cells PP6.ps0 = PP6.cells. Proof. reflexivity. Qed.
Definition VAL_P6 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_P6 (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P6 R csp obj v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P6 R csp obj v40) (fun _ => [])) k) = VZ_P6 R csp obj v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_P6, VZ_P6.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e3p6_conc fx R M csp obj v40 :
  getr R (reg 2) = Z_to_bv 64 (csp + 848) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 32) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 784) (64) ->
  L5.defined M ((csp) + 784) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + 784 + (80) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 784) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  0 <= v40 <= 255 ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u8_at RSEGS M ((csp) + 848) (Z.land (v40) (254)) ->
  exists fx' R' M', msteps RSEGS (st fx R 138580 M) (st fx' R' 138620 M')
    /\ (forall i, In i KS_P6 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 848)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = Z_to_bv 64 (0)
    /\ (forall x : word, ~ ((csp) + 784 <= bv_unsigned x < (csp) + 784 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  set (Vf := VAL_P6 R csp obj v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P6 R csp obj v40 k) by (apply VAL_VZ_P6; lia). unfold VZ_P6 in ZA.
  assert (HR: regs_ok E PP6.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP6.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP6.kn0). { unfold know_ok, PP6.kn0. kn_allx ZA. }
  destruct (PP6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP6.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP6.regs0 PP6.regs_out 56 KS_P6 KS_P6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP6.regs_out E' R' 2 Hregs) by lia. rewrite ro_P6_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP6.regs_out E' R' 8 Hregs) by lia. rewrite ro_P6_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP6.regs_out E' R' 10 Hregs) by lia. rewrite ro_P6_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP6.regs_out E' R' 11 Hregs) by lia. rewrite ro_P6_11. L5KP.wordE' ZA Hag. }
  rewrite cells_P6 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PP6.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

End L5E3P.
