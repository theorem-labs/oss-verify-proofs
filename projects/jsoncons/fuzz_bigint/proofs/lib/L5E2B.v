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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_e2t_v0 LibSegZ_e2r1x LibSegZ_e2r2x.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5E2B.
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
Module PT0 := LibSegZ_e2t_v0.
Definition KS_T0 : list nat := Eval vm_compute in (BG.kept_list 56 PT0.regs0 PT0.regs_out).
Lemma KS_T0_ok : BG.kept_ok 56 PT0.regs0 PT0.regs_out KS_T0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T0_1 : nth 1 PT0.regs_out (ELit 0) = ELit 140224. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T0_2 : nth 2 PT0.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T0_9 : nth 9 PT0.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T0_10 : nth 10 PT0.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_T0_11 : nth 11 PT0.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma ro_T0_12 : nth 12 PT0.regs_out (ELit 0) = ELit 257624. Proof. vm_compute. reflexivity. Qed.
Lemma cells_T0 : SR.ps_cells PT0.ps0 = PT0.cells. Proof. reflexivity. Qed.
Definition VAL_T0 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (v40 : Z) (v41 : Z) (v42 : Z) (v43 : Z) (v44 : Z) (v45 : Z) (v46 : Z) (v47 : Z) (v48 : Z) (v49 : Z) (v50 : Z) (v51 : Z) (v52 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 32%nat => Z_to_bv 64 av | 33%nat => Z_to_bv 64 canary | 34%nat => Z_to_bv 64 uid | 36%nat => Z_to_bv 64 rnd | 39%nat => Z_to_bv 64 hw | 40%nat => Z_to_bv 64 v40 | 41%nat => Z_to_bv 64 v41 | 42%nat => Z_to_bv 64 v42 | 43%nat => Z_to_bv 64 v43 | 44%nat => Z_to_bv 64 v44 | 45%nat => Z_to_bv 64 v45 | 46%nat => Z_to_bv 64 v46 | 47%nat => Z_to_bv 64 v47 | 48%nat => Z_to_bv 64 v48 | 49%nat => Z_to_bv 64 v49 | 50%nat => Z_to_bv 64 v50 | 51%nat => Z_to_bv 64 v51 | 52%nat => Z_to_bv 64 v52 | _ => getr R (reg k) end.
Definition VZ_T0 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (v40 : Z) (v41 : Z) (v42 : Z) (v43 : Z) (v44 : Z) (v45 : Z) (v46 : Z) (v47 : Z) (v48 : Z) (v49 : Z) (v50 : Z) (v51 : Z) (v52 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | 40%nat => v40 | 41%nat => v41 | 42%nat => v42 | 43%nat => v43 | 44%nat => v44 | 45%nat => v45 | 46%nat => v46 | 47%nat => v47 | 48%nat => v48 | 49%nat => v49 | 50%nat => v50 | 51%nat => v51 | 52%nat => v52 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_T0 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= av < 2 ^ 64 -> 0 <= canary < 2 ^ 64 -> 0 <= uid < 2 ^ 64 -> 0 <= rnd < 2 ^ 64 -> 0 <= hw < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 -> 0 <= v41 < 2 ^ 64 -> 0 <= v42 < 2 ^ 64 -> 0 <= v43 < 2 ^ 64 -> 0 <= v44 < 2 ^ 64 -> 0 <= v45 < 2 ^ 64 -> 0 <= v46 < 2 ^ 64 -> 0 <= v47 < 2 ^ 64 -> 0 <= v48 < 2 ^ 64 -> 0 <= v49 < 2 ^ 64 -> 0 <= v50 < 2 ^ 64 -> 0 <= v51 < 2 ^ 64 -> 0 <= v52 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_T0 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52) (fun _ => [])) k) = VZ_T0 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 k.
Proof.
  intros. cbn [ev]. unfold VAL_T0, VZ_T0.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2t_v0_conc fx R M csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 :
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 9) = Z_to_bv 64 (obj) ->
  getr R (reg 10) = Z_to_bv 64 obj ->
  getr R (reg 11) = Z_to_bv 64 (385384) ->
  getr R (reg 12) = Z_to_bv 64 (253816) ->
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
  0 <= v51 < 2 ^ 64 ->
  0 <= v52 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 7936) (7936) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (128) ->
  1099511627776 <= av <= 140737488355328 ->
  (av) mod 8 = 0 ->
  ((csp) + -7936 + (8288) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -7936) ->
  ((csp) + -7936 + (8288) <= (av) + 0 \/ (av) + 0 + (160) <= (csp) + -7936) ->
  ((obj) + -128 + (144) <= (av) + 0 \/ (av) + 0 + (160) <= (obj) + -128) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.u32_at RSEGS M ((0) + 456960) (0) ->
  L5.writable RSEGS M ((0) + 456960) (4) ->
  L5.u64_at RSEGS M ((0) + 591528) (canary) ->
  L5.u64_at RSEGS M ((0) + 591568) (av) ->
  L5.writable RSEGS M ((0) + 459617) (6) ->
  L5.u8_at RSEGS M ((0) + 459617) (0) ->
  L5.u8_at RSEGS M ((0) + 459619) (0) ->
  L5.u8_at RSEGS M ((0) + 459621) (0) ->
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
  L5.u64_at RSEGS M ((csp) + 200) (v40) ->
  L5.u64_at RSEGS M ((csp) + 208) (v41) ->
  L5.u64_at RSEGS M ((csp) + 216) (v42) ->
  L5.u64_at RSEGS M ((csp) + 224) (v43) ->
  L5.u64_at RSEGS M ((csp) + 232) (v44) ->
  L5.u64_at RSEGS M ((csp) + 240) (v45) ->
  L5.u64_at RSEGS M ((csp) + 248) (v46) ->
  L5.u64_at RSEGS M ((csp) + 256) (v47) ->
  L5.u64_at RSEGS M ((csp) + 264) (v48) ->
  L5.u64_at RSEGS M ((csp) + 272) (v49) ->
  L5.u64_at RSEGS M ((csp) + 280) (v50) ->
  L5.u64_at RSEGS M ((csp) + 288) (v51) ->
  L5.u64_at RSEGS M ((csp) + 296) (138528) ->
  L5.u64_at RSEGS M ((csp) + 336) (v52) ->
  L5.u64_at RSEGS M ((csp) + 344) (132608) ->
  exists fx' R' M', msteps RSEGS (st fx R 140156 M) (st fx' R' 140224 M')
    /\ (forall i, In i KS_T0 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (140224)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp)
    /\ getr R' (reg 9) = Z_to_bv 64 (obj)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = Z_to_bv 64 (0)
    /\ getr R' (reg 12) = Z_to_bv 64 (257624)
    /\ L5.u64_at RSEGS M' ((obj) - 8) (csp + 352)
    /\ L5.u64_at RSEGS M' ((obj) - 40) (obj)
    /\ L5.u64_at RSEGS M' ((obj) - 48) (133016)
    /\ L5.u64_at RSEGS M' ((obj) - 56) (91560)
    /\ L5.u64_at RSEGS M' ((obj) - 64) (91699)
    /\ L5.u32_at RSEGS M' ((obj) - 68) (1)
    /\ L5.u8_at RSEGS M' ((0) + 459620) (0)
    /\ L5.u8_at RSEGS M' ((0) + 459619) (1)
    /\ L5.u8_at RSEGS M' ((0) + 459622) (0)
    /\ L5.u8_at RSEGS M' ((0) + 459621) (1)
    /\ L5.u64_at RSEGS M' ((obj) - 16) (0)
    /\ L5.u8_at RSEGS M' ((0) + 459618) (0)
    /\ L5.u8_at RSEGS M' ((0) + 459617) (1)
    /\ L5.u64_at RSEGS M' ((obj) - 120) (1)
    /\ L5.u64_at RSEGS M' ((obj) - 24) (257624)
    /\ L5.u64_at RSEGS M' ((obj) - 32) (4849336966747728640)
    /\ L5.u64_at RSEGS M' ((obj) - 88) (142700)
    /\ L5.u64_at RSEGS M' ((obj) - 104) (253816)
    /\ L5.u64_at RSEGS M' ((obj) - 112) (385384)
    /\ L5.u64_at RSEGS M' ((obj) - 96) (142968)
    /\ L5.u32_at RSEGS M' ((0) + 456960) (1)
    /\ (forall x : word, ~ ((csp) + -7936 <= bv_unsigned x < (csp) + -7936 + (7936)) -> ~ ((obj) + -120 <= bv_unsigned x < (obj) + -120 + (40)) -> ~ ((obj) + -68 <= bv_unsigned x < (obj) + -68 + (68)) -> ~ ((0) + 456960 <= bv_unsigned x < (0) + 456960 + (4)) -> ~ ((0) + 459617 <= bv_unsigned x < (0) + 459617 + (6)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H9 H10 H11 H12 G2 G10 G32 G33 G34 G36 G39 G40 G41 G42 G43 G44 G45 G46 G47 G48 G49 G50 G51 G52 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57.
  set (Vf := VAL_T0 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_T0 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 k) by (apply VAL_VZ_T0; lia). unfold VZ_T0 in ZA.
  assert (HR: regs_ok E PT0.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PT0.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PT0.kn0). { unfold know_ok, PT0.kn0. kn_allx ZA. }
  destruct (PT0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PT0.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PT0.regs0 PT0.regs_out 56 KS_T0 KS_T0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PT0.regs_out E' R' 1 Hregs) by lia. rewrite ro_T0_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PT0.regs_out E' R' 2 Hregs) by lia. rewrite ro_T0_2. L5KP.wordE' ZA Hag. }
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

(* [comment removed for export] *)
Module PR1 := LibSegZ_e2r1x.
Definition KS_R1 : list nat := Eval vm_compute in (BG.kept_list 56 PR1.regs0 PR1.regs_out).
Lemma KS_R1_ok : BG.kept_ok 56 PR1.regs0 PR1.regs_out KS_R1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_1 : nth 1 PR1.regs_out (ELit 0) = ELit 138580. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_2 : nth 2 PR1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 304). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_8 : nth 8 PR1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 416). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_9 : nth 9 PR1.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_10 : nth 10 PR1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_11 : nth 11 PR1.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_18 : nth 18 PR1.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_19 : nth 19 PR1.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_20 : nth 20 PR1.regs_out (ELit 0) = EVar 43. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_21 : nth 21 PR1.regs_out (ELit 0) = EVar 44. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_22 : nth 22 PR1.regs_out (ELit 0) = EVar 45. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_23 : nth 23 PR1.regs_out (ELit 0) = EVar 46. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_24 : nth 24 PR1.regs_out (ELit 0) = EVar 47. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_25 : nth 25 PR1.regs_out (ELit 0) = EVar 48. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_26 : nth 26 PR1.regs_out (ELit 0) = EVar 49. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R1_27 : nth 27 PR1.regs_out (ELit 0) = EVar 50. Proof. vm_compute. reflexivity. Qed.
Lemma cells_R1 : SR.ps_cells PR1.ps0 = PR1.cells. Proof. reflexivity. Qed.
Definition VAL_R1 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (v40 : Z) (v41 : Z) (v42 : Z) (v43 : Z) (v44 : Z) (v45 : Z) (v46 : Z) (v47 : Z) (v48 : Z) (v49 : Z) (v50 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 32%nat => Z_to_bv 64 av | 33%nat => Z_to_bv 64 canary | 34%nat => Z_to_bv 64 uid | 36%nat => Z_to_bv 64 rnd | 39%nat => Z_to_bv 64 hw | 40%nat => Z_to_bv 64 v40 | 41%nat => Z_to_bv 64 v41 | 42%nat => Z_to_bv 64 v42 | 43%nat => Z_to_bv 64 v43 | 44%nat => Z_to_bv 64 v44 | 45%nat => Z_to_bv 64 v45 | 46%nat => Z_to_bv 64 v46 | 47%nat => Z_to_bv 64 v47 | 48%nat => Z_to_bv 64 v48 | 49%nat => Z_to_bv 64 v49 | 50%nat => Z_to_bv 64 v50 | _ => getr R (reg k) end.
Definition VZ_R1 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (v40 : Z) (v41 : Z) (v42 : Z) (v43 : Z) (v44 : Z) (v45 : Z) (v46 : Z) (v47 : Z) (v48 : Z) (v49 : Z) (v50 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | 40%nat => v40 | 41%nat => v41 | 42%nat => v42 | 43%nat => v43 | 44%nat => v44 | 45%nat => v45 | 46%nat => v46 | 47%nat => v47 | 48%nat => v48 | 49%nat => v49 | 50%nat => v50 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_R1 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= av < 2 ^ 64 -> 0 <= canary < 2 ^ 64 -> 0 <= uid < 2 ^ 64 -> 0 <= rnd < 2 ^ 64 -> 0 <= hw < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 -> 0 <= v41 < 2 ^ 64 -> 0 <= v42 < 2 ^ 64 -> 0 <= v43 < 2 ^ 64 -> 0 <= v44 < 2 ^ 64 -> 0 <= v45 < 2 ^ 64 -> 0 <= v46 < 2 ^ 64 -> 0 <= v47 < 2 ^ 64 -> 0 <= v48 < 2 ^ 64 -> 0 <= v49 < 2 ^ 64 -> 0 <= v50 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_R1 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50) (fun _ => [])) k) = VZ_R1 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 k.
Proof.
  intros. cbn [ev]. unfold VAL_R1, VZ_R1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2r1x_conc fx R M csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 :
  getr R (reg 1) = Z_to_bv 64 (140224) ->
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
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
  L5.writable RSEGS M ((csp) - 7936) (7936) ->
  L5.defined M ((csp) - 7936) (7936) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  1099511627776 <= av <= 140737488355328 ->
  (av) mod 8 = 0 ->
  ((csp) + -7936 + (8240) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -7936) ->
  ((obj) + -128 + (144) <= (av) + 0 \/ (av) + 0 + (160) <= (obj) + -128) ->
  ((csp) + -7936 + (8240) <= (av) + 0 \/ (av) + 0 + (160) <= (csp) + -7936) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u64_at RSEGS M ((obj) - 16) (0) ->
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
  L5.u64_at RSEGS M ((obj) - 8) (csp + 352) ->
  L5.u64_at RSEGS M ((obj) - 32) (4849336966747728640) ->
  L5.u64_at RSEGS M ((csp) + 296) (138528) ->
  L5.u64_at RSEGS M ((csp) + 288) (csp + 416) ->
  L5.u64_at RSEGS M ((csp) + 280) (v40) ->
  L5.u64_at RSEGS M ((csp) + 272) (v41) ->
  L5.u64_at RSEGS M ((csp) + 264) (v42) ->
  L5.u64_at RSEGS M ((csp) + 256) (v43) ->
  L5.u64_at RSEGS M ((csp) + 248) (v44) ->
  L5.u64_at RSEGS M ((csp) + 240) (v45) ->
  L5.u64_at RSEGS M ((csp) + 232) (v46) ->
  L5.u64_at RSEGS M ((csp) + 224) (v47) ->
  L5.u64_at RSEGS M ((csp) + 216) (v48) ->
  L5.u64_at RSEGS M ((csp) + 208) (v49) ->
  L5.u64_at RSEGS M ((csp) + 200) (v50) ->
  L5.u8_at RSEGS M ((0) + 459617) (1) ->
  L5.u8_at RSEGS M ((0) + 459618) (0) ->
  L5.u8_at RSEGS M ((0) + 459619) (1) ->
  L5.u8_at RSEGS M ((0) + 459620) (0) ->
  L5.u8_at RSEGS M ((0) + 459621) (1) ->
  L5.u8_at RSEGS M ((0) + 459622) (0) ->
  exists fx' R' M', msteps RSEGS (st fx R 140392 M) (st fx' R' 138580 M')
    /\ (forall i, In i KS_R1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (138580)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 304)
    /\ getr R' (reg 8) = Z_to_bv 64 (csp + 416)
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
    /\ (forall x : word, ~ ((csp) + -7936 <= bv_unsigned x < (csp) + -7936 + (7936)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H1 H2 H3 H4 H10 G2 G10 G32 G33 G34 G36 G39 G40 G41 G42 G43 G44 G45 G46 G47 G48 G49 G50 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60.
  set (Vf := VAL_R1 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_R1 R csp obj av canary uid rnd hw v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 k) by (apply VAL_VZ_R1; lia). unfold VZ_R1 in ZA.
  assert (HR: regs_ok E PR1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PR1.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PR1.kn0). { unfold know_ok, PR1.kn0. kn_allx ZA. }
  destruct (PR1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PR1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PR1.regs0 PR1.regs_out 56 KS_R1 KS_R1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 1 Hregs) by lia. rewrite ro_R1_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 2 Hregs) by lia. rewrite ro_R1_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 8 Hregs) by lia. rewrite ro_R1_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 9 Hregs) by lia. rewrite ro_R1_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 10 Hregs) by lia. rewrite ro_R1_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 11 Hregs) by lia. rewrite ro_R1_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 18 Hregs) by lia. rewrite ro_R1_18. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 19 Hregs) by lia. rewrite ro_R1_19. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 20 Hregs) by lia. rewrite ro_R1_20. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 21 Hregs) by lia. rewrite ro_R1_21. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 22 Hregs) by lia. rewrite ro_R1_22. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 23 Hregs) by lia. rewrite ro_R1_23. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 24 Hregs) by lia. rewrite ro_R1_24. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 25 Hregs) by lia. rewrite ro_R1_25. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 26 Hregs) by lia. rewrite ro_R1_26. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR1.regs_out E' R' 27 Hregs) by lia. rewrite ro_R1_27. L5KP.wordE' ZA Hag. }
  rewrite cells_R1 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PR1.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PR2 := LibSegZ_e2r2x.
Definition KS_R2 : list nat := Eval vm_compute in (BG.kept_list 56 PR2.regs0 PR2.regs_out).
Lemma KS_R2_ok : BG.kept_ok 56 PR2.regs0 PR2.regs_out KS_R2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R2_1 : nth 1 PR2.regs_out (ELit 0) = ELit 133016. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R2_2 : nth 2 PR2.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 352). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R2_8 : nth 8 PR2.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma ro_R2_10 : nth 10 PR2.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_R2_11 : nth 11 PR2.regs_out (ELit 0) = ELit 1. Proof. vm_compute. reflexivity. Qed.
Lemma cells_R2 : SR.ps_cells PR2.ps0 = PR2.cells. Proof. reflexivity. Qed.
Definition VAL_R2 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 32%nat => Z_to_bv 64 av | 33%nat => Z_to_bv 64 canary | 34%nat => Z_to_bv 64 uid | 36%nat => Z_to_bv 64 rnd | 39%nat => Z_to_bv 64 hw | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_R2 (R : bvmap 5 word) (csp : Z) (obj : Z) (av : Z) (canary : Z) (uid : Z) (rnd : Z) (hw : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_R2 R csp obj av canary uid rnd hw v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= av < 2 ^ 64 -> 0 <= canary < 2 ^ 64 -> 0 <= uid < 2 ^ 64 -> 0 <= rnd < 2 ^ 64 -> 0 <= hw < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_R2 R csp obj av canary uid rnd hw v40) (fun _ => [])) k) = VZ_R2 R csp obj av canary uid rnd hw v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_R2, VZ_R2.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2r2x_conc fx R M csp obj av canary uid rnd hw v40 :
  getr R (reg 1) = Z_to_bv 64 (138580) ->
  getr R (reg 2) = Z_to_bv 64 (csp + 304) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
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
  L5.writable RSEGS M ((csp) - 7936) (8240) ->
  L5.defined M ((csp) - 7936) (8240) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  1099511627776 <= av <= 140737488355328 ->
  (av) mod 8 = 0 ->
  ((csp) + -7936 + (8288) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + -7936) ->
  ((obj) + -128 + (144) <= (av) + 0 \/ (av) + 0 + (160) <= (obj) + -128) ->
  ((csp) + -7936 + (8288) <= (av) + 0 \/ (av) + 0 + (160) <= (csp) + -7936) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u64_at RSEGS M ((obj) - 16) (0) ->
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
  L5.u64_at RSEGS M ((obj) - 8) (csp + 352) ->
  L5.u64_at RSEGS M ((obj) - 32) (4849336966747728640) ->
  L5.u64_at RSEGS M ((csp) + 344) (132608) ->
  L5.u64_at RSEGS M ((csp) + 336) (v40) ->
  L5.u32_at RSEGS M ((obj) - 68) (1) ->
  L5.u64_at RSEGS M ((obj) - 48) (133016) ->
  L5.u8_at RSEGS M ((0) + 459617) (1) ->
  L5.u8_at RSEGS M ((0) + 459618) (0) ->
  L5.u8_at RSEGS M ((0) + 459619) (1) ->
  L5.u8_at RSEGS M ((0) + 459620) (0) ->
  L5.u8_at RSEGS M ((0) + 459621) (1) ->
  L5.u8_at RSEGS M ((0) + 459622) (0) ->
  exists fx' R' M', msteps RSEGS (st fx R 138620 M) (st fx' R' 133016 M')
    /\ (forall i, In i KS_R2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (133016)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 352)
    /\ getr R' (reg 8) = Z_to_bv 64 (v40)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 32)
    /\ getr R' (reg 11) = Z_to_bv 64 (1)
    /\ (forall x : word, ~ ((csp) + -7936 <= bv_unsigned x < (csp) + -7936 + (8240)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H1 H2 H3 H4 H10 G2 G10 G32 G33 G34 G36 G39 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  set (Vf := VAL_R2 R csp obj av canary uid rnd hw v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_R2 R csp obj av canary uid rnd hw v40 k) by (apply VAL_VZ_R2; lia). unfold VZ_R2 in ZA.
  assert (HR: regs_ok E PR2.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PR2.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PR2.kn0). { unfold know_ok, PR2.kn0. kn_allx ZA. }
  destruct (PR2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PR2.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PR2.regs0 PR2.regs_out 56 KS_R2 KS_R2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PR2.regs_out E' R' 1 Hregs) by lia. rewrite ro_R2_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR2.regs_out E' R' 2 Hregs) by lia. rewrite ro_R2_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR2.regs_out E' R' 8 Hregs) by lia. rewrite ro_R2_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR2.regs_out E' R' 10 Hregs) by lia. rewrite ro_R2_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PR2.regs_out E' R' 11 Hregs) by lia. rewrite ro_R2_11. L5KP.wordE' ZA Hag. }
  rewrite cells_R2 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PR2.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

End L5E2B.
