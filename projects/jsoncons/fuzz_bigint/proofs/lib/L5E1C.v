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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_e1t_v1.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5E1C.
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
Ltac kn1x ZA := first [ L5KP.kn1 ZA
  | lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5KP.kentry_KRange; [zc_eval0 ZA; reflexivity | lia] end ].
Ltac kn_allx ZA := repeat (apply Forall_cons; [kn1x ZA|]); try apply Forall_nil.


(* [comment removed for export] *)
Module PT1 := LibSegZ_e1t_v1.
Definition KS_T1 : list nat := Eval vm_compute in (BG.kept_list 56 PT1.regs0 PT1.regs_out).
Lemma KS_T1_ok : BG.kept_ok 56 PT1.regs0 PT1.regs_out KS_T1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T1_1 : nth 1 PT1.regs_out (ELit 0) = ELit 132924. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T1_2 : nth 2 PT1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 32). Proof. vm_compute. reflexivity. Qed.
Lemma ro_T1_8 : nth 8 PT1.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T1_9 : nth 9 PT1.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T1_10 : nth 10 PT1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_T1_11 : nth 11 PT1.regs_out (ELit 0) = ELit 1. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T1_12 : nth 12 PT1.regs_out (ELit 0) = ELit 257624. Proof. vm_compute. reflexivity. Qed.
Lemma cells_T1 : SR.ps_cells PT1.ps0 = PT1.cells. Proof. reflexivity. Qed.
Definition VAL_T1 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (s0v : Z) (s1v : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 32%nat => Z_to_bv 64 av | 33%nat => Z_to_bv 64 canary | 34%nat => Z_to_bv 64 uid | 36%nat => Z_to_bv 64 rnd | 39%nat => Z_to_bv 64 hw | 40%nat => Z_to_bv 64 s0v | 41%nat => Z_to_bv 64 s1v | _ => getr R (reg k) end.
Definition VZ_T1 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (s0v : Z) (s1v : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | 40%nat => s0v | 41%nat => s1v | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_T1 R csp obj av canary uid rnd hw s0v s1v : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= av < 2 ^ 64 -> 0 <= canary < 2 ^ 64 -> 0 <= uid < 2 ^ 64 -> 0 <= rnd < 2 ^ 64 -> 0 <= hw < 2 ^ 64 -> 0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_T1 R csp obj av canary uid rnd hw s0v s1v) (fun _ => [])) k) = VZ_T1 R csp obj av canary uid rnd hw s0v s1v k.
Proof.
  intros. cbn [ev]. unfold VAL_T1, VZ_T1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e1t_v1_conc fx R M csp obj av canary uid rnd hw s0v s1v :
  getr R (reg 1) = Z_to_bv 64 (133712) ->
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 obj ->
  getr R (reg 11) = Z_to_bv 64 (385840) ->
  getr R (reg 12) = Z_to_bv 64 (267080) ->
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
  ((obj) + -128 + (160) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u32_at RSEGS M ((0) + 456960) (0) ->
  L5.u64_at RSEGS M ((0) + 591528) (canary) ->
  L5.u64_at RSEGS M ((0) + 591568) (av) ->
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
  L5.u64_at RSEGS M ((csp) + 24) (132584) ->
  L5.u64_at RSEGS M ((csp) + 16) (s0v) ->
  L5.u64_at RSEGS M ((csp) + 8) (s1v) ->
  L5.u8_at RSEGS M ((0) + 459617) (1) ->
  L5.u8_at RSEGS M ((0) + 459618) (0) ->
  L5.u8_at RSEGS M ((0) + 459619) (1) ->
  L5.u8_at RSEGS M ((0) + 459620) (0) ->
  L5.u8_at RSEGS M ((0) + 459621) (1) ->
  L5.u8_at RSEGS M ((0) + 459622) (0) ->
  L5.writable RSEGS M ((0) + 459617) (6) ->
  L5.writable RSEGS M ((0) + 456960) (4) ->
  exists fx' R' M', msteps RSEGS (st fx R 133732 M) (st fx' R' 132924 M')
    /\ (forall i, In i KS_T1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (132924)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 32)
    /\ getr R' (reg 8) = Z_to_bv 64 (s0v)
    /\ getr R' (reg 9) = Z_to_bv 64 (s1v)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = Z_to_bv 64 (1)
    /\ getr R' (reg 12) = Z_to_bv 64 (257624)
    /\ L5.u64_at RSEGS M' ((obj) - 8) (csp + 32)
    /\ L5.u64_at RSEGS M' ((obj) - 40) (obj)
    /\ L5.u64_at RSEGS M' ((obj) - 48) (132924)
    /\ L5.u64_at RSEGS M' ((obj) - 56) (91560)
    /\ L5.u64_at RSEGS M' ((obj) - 64) (91699)
    /\ L5.u32_at RSEGS M' ((obj) - 68) (1)
    /\ L5.u64_at RSEGS M' ((obj) - 16) (0)
    /\ L5.u64_at RSEGS M' ((obj) - 120) (1)
    /\ L5.u64_at RSEGS M' ((obj) - 24) (257624)
    /\ L5.u64_at RSEGS M' ((obj) - 32) (4849336966747728640)
    /\ L5.u64_at RSEGS M' ((obj) - 88) (142700)
    /\ L5.u64_at RSEGS M' ((obj) - 104) (267080)
    /\ L5.u64_at RSEGS M' ((obj) - 112) (385840)
    /\ L5.u64_at RSEGS M' ((obj) - 96) (142968)
    /\ L5.u32_at RSEGS M' ((0) + 456960) (1)
    /\ L5.u8_at RSEGS M' ((0) + 459617) (1)
    /\ L5.u8_at RSEGS M' ((0) + 459618) (0)
    /\ L5.u8_at RSEGS M' ((0) + 459619) (1)
    /\ L5.u8_at RSEGS M' ((0) + 459620) (0)
    /\ L5.u8_at RSEGS M' ((0) + 459621) (1)
    /\ L5.u8_at RSEGS M' ((0) + 459622) (0)
    /\ (forall x : word, ~ ((csp) + -7984 <= bv_unsigned x < (csp) + -7984 + (7984)) -> ~ ((obj) + -120 <= bv_unsigned x < (obj) + -120 + (40)) -> ~ ((obj) + -68 <= bv_unsigned x < (obj) + -68 + (68)) -> ~ ((0) + 456960 <= bv_unsigned x < (0) + 456960 + (4)) -> ~ ((0) + 459617 <= bv_unsigned x < (0) + 459617 + (6)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H1 H2 H3 H4 H10 H11 H12 G2 G10 G32 G33 G34 G36 G39 G40 G41 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  set (Vf := VAL_T1 R csp obj av canary uid rnd hw s0v s1v). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_T1 R csp obj av canary uid rnd hw s0v s1v k) by (apply VAL_VZ_T1; lia). unfold VZ_T1 in ZA.
  assert (HR: regs_ok E PT1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PT1.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PT1.kn0). { unfold know_ok, PT1.kn0. kn_allx ZA. }
  destruct (PT1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PT1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PT1.regs0 PT1.regs_out 56 KS_T1 KS_T1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PT1.regs_out E' R' 1 Hregs) by lia. rewrite ro_T1_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT1.regs_out E' R' 2 Hregs) by lia. rewrite ro_T1_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT1.regs_out E' R' 8 Hregs) by lia. rewrite ro_T1_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT1.regs_out E' R' 9 Hregs) by lia. rewrite ro_T1_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT1.regs_out E' R' 10 Hregs) by lia. rewrite ro_T1_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT1.regs_out E' R' 11 Hregs) by lia. rewrite ro_T1_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT1.regs_out E' R' 12 Hregs) by lia. rewrite ro_T1_12. L5KP.wordE' ZA Hag. }
  rewrite cells_T1 in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT1.cells, PT1.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT1.cells, PT1.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.uw_of_KWordw. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.uw_of_KWordw. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PT1.cells, PT1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { intros x Hy0 Hy1 Hy2 Hy3 Hy4. apply Hfr. unfold PT1.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

End L5E1C.
