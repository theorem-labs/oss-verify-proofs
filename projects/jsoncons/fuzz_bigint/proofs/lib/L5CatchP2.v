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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5CatchP2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5CP2.
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
Module PB1 := LibSegZ_e2b1.
Definition KS_B1 : list nat := Eval vm_compute in (BG.kept_list 56 PB1.regs0 PB1.regs_out).
Lemma KS_B1_ok : BG.kept_ok 56 PB1.regs0 PB1.regs_out KS_B1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_B1_1 : nth 1 PB1.regs_out (ELit 0) = ELit 133140. Proof. vm_compute. reflexivity. Qed.
Lemma ro_B1_2 : nth 2 PB1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 352). Proof. vm_compute. reflexivity. Qed.
Lemma ro_B1_10 : nth 10 PB1.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_B1_11 : nth 11 PB1.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_B1_12 : nth 12 PB1.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma ro_B1_13 : nth 13 PB1.regs_out (ELit 0) = ELit 1. Proof. vm_compute. reflexivity. Qed.
Lemma ro_B1_14 : nth 14 PB1.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma cells_B1 : SR.ps_cells PB1.ps0 = PB1.cells. Proof. reflexivity. Qed.
Definition VAL_B1 (R : bvmap 5 word) (csp : Z) (obj : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | _ => getr R (reg k) end.
Definition VZ_B1 (R : bvmap 5 word) (csp : Z) (obj : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_B1 R csp obj : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_B1 R csp obj) (fun _ => [])) k) = VZ_B1 R csp obj k.
Proof.
  intros. cbn [ev]. unfold VAL_B1, VZ_B1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2b1_conc fx R M csp obj :
  getr R (reg 2) = Z_to_bv 64 (csp + 352) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 32) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 256) (96) ->
  L5.defined M ((csp) + 256) (96) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + 256 + (96) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 256) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u64_at RSEGS M ((obj) - 32) (4849336966747728640) ->
  L5.u32_at RSEGS M ((obj) - 72) (0) ->
  L5.u64_at RSEGS M ((0) + 456952) (0) ->
  L5.u32_at RSEGS M ((0) + 456960) (1) ->
  L5.u64_at RSEGS M ((obj) - 40) (obj) ->
  L5.writable RSEGS M ((0) + 456952) (8) ->
  L5.writable RSEGS M ((0) + 456960) (4) ->
  exists fx' R' M', msteps RSEGS (st fx R 133136 M) (st fx' R' 133140 M')
    /\ (forall i, In i KS_B1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (133140)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 352)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj)
    /\ getr R' (reg 11) = Z_to_bv 64 (obj)
    /\ getr R' (reg 12) = Z_to_bv 64 (0)
    /\ getr R' (reg 13) = Z_to_bv 64 (1)
    /\ getr R' (reg 14) = Z_to_bv 64 (0)
    /\ L5.u32_at RSEGS M' ((0) + 456960) (0)
    /\ L5.u64_at RSEGS M' ((0) + 456952) (obj - 128)
    /\ L5.u64_at RSEGS M' ((obj) - 80) (0)
    /\ L5.u32_at RSEGS M' ((obj) - 72) (1)
    /\ (forall x : word, ~ ((csp) + 256 <= bv_unsigned x < (csp) + 256 + (96)) -> ~ ((obj) + -80 <= bv_unsigned x < (obj) + -80 + (12)) -> ~ ((0) + 456952 <= bv_unsigned x < (0) + 456952 + (8)) -> ~ ((0) + 456960 <= bv_unsigned x < (0) + 456960 + (4)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20.
  set (Vf := VAL_B1 R csp obj). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_B1 R csp obj k) by (apply VAL_VZ_B1; lia). unfold VZ_B1 in ZA.
  assert (HR: regs_ok E PB1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PB1.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PB1.kn0). { unfold know_ok, PB1.kn0. kn_allx ZA. }
  destruct (PB1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PB1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PB1.regs0 PB1.regs_out 56 KS_B1 KS_B1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PB1.regs_out E' R' 1 Hregs) by lia. rewrite ro_B1_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PB1.regs_out E' R' 2 Hregs) by lia. rewrite ro_B1_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PB1.regs_out E' R' 10 Hregs) by lia. rewrite ro_B1_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PB1.regs_out E' R' 11 Hregs) by lia. rewrite ro_B1_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PB1.regs_out E' R' 12 Hregs) by lia. rewrite ro_B1_12. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PB1.regs_out E' R' 13 Hregs) by lia. rewrite ro_B1_13. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PB1.regs_out E' R' 14 Hregs) by lia. rewrite ro_B1_14. L5KP.wordE' ZA Hag. }
  rewrite cells_B1 in Hcells.
  split. { eapply L5KP.uw_of_KWordw. apply Hcells. unfold PB1.cells, PB1.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PB1.cells, PB1.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PB1.cells, PB1.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.uw_of_KWordw. apply Hcells. unfold PB1.cells, PB1.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1 Hy2 Hy3. apply Hfr. unfold PB1.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PE1 := LibSegZ_e2e1.
Definition KS_E1 : list nat := Eval vm_compute in (BG.kept_list 56 PE1.regs0 PE1.regs_out).
Lemma KS_E1_ok : BG.kept_ok 56 PE1.regs0 PE1.regs_out KS_E1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E1_1 : nth 1 PE1.regs_out (ELit 0) = ELit 253884. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E1_2 : nth 2 PE1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 304). Proof. vm_compute. reflexivity. Qed.
Lemma ro_E1_8 : nth 8 PE1.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E1_10 : nth 10 PE1.regs_out (ELit 0) = EVar 37. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E1_11 : nth 11 PE1.regs_out (ELit 0) = EVar 37. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E1_12 : nth 12 PE1.regs_out (ELit 0) = ELit 18446744073709551615. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E1_13 : nth 13 PE1.regs_out (ELit 0) = ELit 18446744073709551615. Proof. vm_compute. reflexivity. Qed.
Lemma cells_E1 : SR.ps_cells PE1.ps0 = PE1.cells. Proof. reflexivity. Qed.
Definition VAL_E1 (R : bvmap 5 word) (csp : Z) (obj : Z) (ref : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 37%nat => Z_to_bv 64 ref | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_E1 (R : bvmap 5 word) (csp : Z) (obj : Z) (ref : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 37%nat => ref | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_E1 R csp obj ref v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= ref < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_E1 R csp obj ref v40) (fun _ => [])) k) = VZ_E1 R csp obj ref v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_E1, VZ_E1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2e1_conc fx R M csp obj ref v40 :
  getr R (reg 2) = Z_to_bv 64 (csp + 352) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (v40) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= ref < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 240) (112) ->
  L5.defined M ((csp) + 240) (112) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  4096 <= ref <= 140737488355328 ->
  (ref) mod 16 = 0 ->
  L5.writable RSEGS M (ref) (37) ->
  L5.defined M (ref) (37) ->
  ((csp) + 240 + (112) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 240) ->
  ((obj) + -128 + (144) <= (ref) + 0 \/ (ref) + 0 + (37) <= (obj) + -128) ->
  ((csp) + 240 + (112) <= (ref) + 0 \/ (ref) + 0 + (37) <= (csp) + 240) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  ((ref) + 0 + (37) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (ref) + 0) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u64_at RSEGS M ((0) + 456952) (obj - 128) ->
  L5.u64_at RSEGS M ((obj) - 32) (4849336966747728640) ->
  L5.u32_at RSEGS M ((obj) - 72) (1) ->
  L5.u64_at RSEGS M ((obj) - 80) (0) ->
  L5.u64_at RSEGS M ((obj) - 120) (1) ->
  L5.u64_at RSEGS M ((obj) - 104) (253816) ->
  L5.u64_at RSEGS M ((obj) + 8) (ref + 24) ->
  L5.u32_at RSEGS M ((ref) + 16) (0) ->
  L5.writable RSEGS M ((0) + 456952) (8) ->
  exists fx' R' M', msteps RSEGS (st fx R 133140 M) (st fx' R' 309252 M')
    /\ (forall i, In i KS_E1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (253884)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 304)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj)
    /\ getr R' (reg 10) = Z_to_bv 64 (ref)
    /\ getr R' (reg 11) = Z_to_bv 64 (ref)
    /\ getr R' (reg 12) = Z_to_bv 64 (18446744073709551615)
    /\ getr R' (reg 13) = Z_to_bv 64 (18446744073709551615)
    /\ L5.u64_at RSEGS M' ((csp) + 304) (obj - 128)
    /\ L5.u64_at RSEGS M' ((csp) + 312) (258088)
    /\ L5.u32_at RSEGS M' ((ref) + 16) (18446744073709551615)
    /\ L5.u64_at RSEGS M' ((obj) + 0) (385144)
    /\ L5.u64_at RSEGS M' ((obj) - 120) (0)
    /\ L5.u64_at RSEGS M' ((0) + 456952) (0)
    /\ L5.u32_at RSEGS M' ((obj) - 72) (0)
    /\ L5.u64_at RSEGS M' ((csp) + 328) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' ((csp) + 336) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' ((csp) + 344) (133144)
    /\ L5.u64_at RSEGS M' ((obj) - 32) (4849336966747728640)
    /\ L5.u64_at RSEGS M' ((obj) - 80) (0)
    /\ L5.u64_at RSEGS M' ((obj) - 104) (253816)
    /\ (forall x : word, ~ ((csp) + 240 <= bv_unsigned x < (csp) + 240 + (112)) -> ~ ((obj) + -120 <= bv_unsigned x < (obj) + -120 + (128)) -> ~ ((ref) + 16 <= bv_unsigned x < (ref) + 16 + (4)) -> ~ ((0) + 456952 <= bv_unsigned x < (0) + 456952 + (8)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G37 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29.
  set (Vf := VAL_E1 R csp obj ref v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_E1 R csp obj ref v40 k) by (apply VAL_VZ_E1; lia). unfold VZ_E1 in ZA.
  assert (HR: regs_ok E PE1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PE1.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PE1.kn0). { unfold know_ok, PE1.kn0. kn_allx ZA. }
  destruct (PE1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PE1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PE1.regs0 PE1.regs_out 56 KS_E1 KS_E1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PE1.regs_out E' R' 1 Hregs) by lia. rewrite ro_E1_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE1.regs_out E' R' 2 Hregs) by lia. rewrite ro_E1_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE1.regs_out E' R' 8 Hregs) by lia. rewrite ro_E1_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE1.regs_out E' R' 10 Hregs) by lia. rewrite ro_E1_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE1.regs_out E' R' 11 Hregs) by lia. rewrite ro_E1_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE1.regs_out E' R' 12 Hregs) by lia. rewrite ro_E1_12. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE1.regs_out E' R' 13 Hregs) by lia. rewrite ro_E1_13. L5KP.wordE' ZA Hag. }
  rewrite cells_E1 in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PE1.cells, PE1.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PE1.cells, PE1.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.uw_of_KWordw. apply Hcells. unfold PE1.cells, PE1.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PE1.cells, PE1.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PE1.cells, PE1.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PE1.cells, PE1.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.uw_of_KWordw. apply Hcells. unfold PE1.cells, PE1.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PE1.cells, PE1.cells0. right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PE1.cells, PE1.cells0. right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PE1.cells, PE1.cells0. right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PE1.cells, PE1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PE1.cells, PE1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PE1.cells, PE1.cells0. right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1 Hy2 Hy3. apply Hfr. unfold PE1.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PE2L := LibSegZ_e2e2_bl.
Definition KS_E2L : list nat := Eval vm_compute in (BG.kept_list 56 PE2L.regs0 PE2L.regs_out).
Lemma KS_E2L_ok : BG.kept_ok 56 PE2L.regs0 PE2L.regs_out KS_E2L = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E2L_1 : nth 1 PE2L.regs_out (ELit 0) = ELit 258096. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E2L_2 : nth 2 PE2L.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 320). Proof. vm_compute. reflexivity. Qed.
Lemma ro_E2L_8 : nth 8 PE2L.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-128)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_E2L_10 : nth 10 PE2L.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-128)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_E2L_11 : nth 11 PE2L.regs_out (ELit 0) = ELit 456976. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E2L_12 : nth 12 PE2L.regs_out (ELit 0) = ELit 456992. Proof. vm_compute. reflexivity. Qed.
Lemma cells_E2L : SR.ps_cells PE2L.ps0 = PE2L.cells. Proof. reflexivity. Qed.
Definition VAL_E2L (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_E2L (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_E2L R csp obj v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_E2L R csp obj v40) (fun _ => [])) k) = VZ_E2L R csp obj v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_E2L, VZ_E2L.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2e2_bl_conc fx R M csp obj v40 :
  getr R (reg 2) = Z_to_bv 64 (csp + 304) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 8) = Z_to_bv 64 (obj) ->
  getr R (reg 10) = Z_to_bv 64 (v40) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 240) (64) ->
  L5.defined M ((csp) + 240) (64) ->
  4224 <= obj <= 65520 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + 240 + (80) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 240) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u64_at RSEGS M ((csp) + 312) (258088) ->
  L5.u64_at RSEGS M ((csp) + 304) (obj - 128) ->
  exists fx' R' M', msteps RSEGS (st fx R 253884 M) (st fx' R' 309252 M')
    /\ (forall i, In i KS_E2L -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (258096)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 320)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj - 128)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 128)
    /\ getr R' (reg 11) = Z_to_bv 64 (456976)
    /\ getr R' (reg 12) = Z_to_bv 64 (456992)
    /\ (forall x : word, ~ ((csp) + 240 <= bv_unsigned x < (csp) + 240 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H8 H10 G2 G10 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  set (Vf := VAL_E2L R csp obj v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_E2L R csp obj v40 k) by (apply VAL_VZ_E2L; lia). unfold VZ_E2L in ZA.
  assert (HR: regs_ok E PE2L.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PE2L.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PE2L.kn0). { unfold know_ok, PE2L.kn0. kn_allx ZA. }
  destruct (PE2L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PE2L.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PE2L.regs0 PE2L.regs_out 56 KS_E2L KS_E2L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PE2L.regs_out E' R' 1 Hregs) by lia. rewrite ro_E2L_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE2L.regs_out E' R' 2 Hregs) by lia. rewrite ro_E2L_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE2L.regs_out E' R' 8 Hregs) by lia. rewrite ro_E2L_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE2L.regs_out E' R' 10 Hregs) by lia. rewrite ro_E2L_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE2L.regs_out E' R' 11 Hregs) by lia. rewrite ro_E2L_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE2L.regs_out E' R' 12 Hregs) by lia. rewrite ro_E2L_12. L5KP.wordE' ZA Hag. }
  rewrite cells_E2L in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PE2L.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PE2H := LibSegZ_e2e2_bh.
Definition KS_E2H : list nat := Eval vm_compute in (BG.kept_list 56 PE2H.regs0 PE2H.regs_out).
Lemma KS_E2H_ok : BG.kept_ok 56 PE2H.regs0 PE2H.regs_out KS_E2H = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E2H_1 : nth 1 PE2H.regs_out (ELit 0) = ELit 258096. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E2H_2 : nth 2 PE2H.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 320). Proof. vm_compute. reflexivity. Qed.
Lemma ro_E2H_8 : nth 8 PE2H.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-128)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_E2H_10 : nth 10 PE2H.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit (-128)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_E2H_11 : nth 11 PE2H.regs_out (ELit 0) = ELit 456976. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E2H_12 : nth 12 PE2H.regs_out (ELit 0) = ELit 456992. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E2H_14 : nth 14 PE2H.regs_out (ELit 0) = ELit 457504. Proof. vm_compute. reflexivity. Qed.
Lemma cells_E2H : SR.ps_cells PE2H.ps0 = PE2H.cells. Proof. reflexivity. Qed.
Definition VAL_E2H (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 v40 | _ => getr R (reg k) end.
Definition VZ_E2H (R : bvmap 5 word) (csp : Z) (obj : Z) (v40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => v40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_E2H R csp obj v40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_E2H R csp obj v40) (fun _ => [])) k) = VZ_E2H R csp obj v40 k.
Proof.
  intros. cbn [ev]. unfold VAL_E2H, VZ_E2H.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2e2_bh_conc fx R M csp obj v40 :
  getr R (reg 2) = Z_to_bv 64 (csp + 304) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 8) = Z_to_bv 64 (obj) ->
  getr R (reg 10) = Z_to_bv 64 (v40) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 240) (64) ->
  L5.defined M ((csp) + 240) (64) ->
  594048 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (144) ->
  L5.defined M ((obj) - 128) (144) ->
  ((csp) + 240 + (80) <= (obj) + -128 \/ (obj) + -128 + (144) <= (csp) + 240) ->
  ((obj) + -128 + (144) <= (0) + 65536 \/ (0) + 65536 + (528384) <= (obj) + -128) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u64_at RSEGS M ((csp) + 312) (258088) ->
  L5.u64_at RSEGS M ((csp) + 304) (obj - 128) ->
  exists fx' R' M', msteps RSEGS (st fx R 253884 M) (st fx' R' 309252 M')
    /\ (forall i, In i KS_E2H -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (258096)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 320)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj - 128)
    /\ getr R' (reg 10) = Z_to_bv 64 (obj - 128)
    /\ getr R' (reg 11) = Z_to_bv 64 (456976)
    /\ getr R' (reg 12) = Z_to_bv 64 (456992)
    /\ getr R' (reg 14) = Z_to_bv 64 (457504)
    /\ (forall x : word, ~ ((csp) + 240 <= bv_unsigned x < (csp) + 240 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H8 H10 G2 G10 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  set (Vf := VAL_E2H R csp obj v40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_E2H R csp obj v40 k) by (apply VAL_VZ_E2H; lia). unfold VZ_E2H in ZA.
  assert (HR: regs_ok E PE2H.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PE2H.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PE2H.kn0). { unfold know_ok, PE2H.kn0. kn_allx ZA. }
  destruct (PE2H.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PE2H.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PE2H.regs0 PE2H.regs_out 56 KS_E2H KS_E2H_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PE2H.regs_out E' R' 1 Hregs) by lia. rewrite ro_E2H_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE2H.regs_out E' R' 2 Hregs) by lia. rewrite ro_E2H_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE2H.regs_out E' R' 8 Hregs) by lia. rewrite ro_E2H_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE2H.regs_out E' R' 10 Hregs) by lia. rewrite ro_E2H_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE2H.regs_out E' R' 11 Hregs) by lia. rewrite ro_E2H_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE2H.regs_out E' R' 12 Hregs) by lia. rewrite ro_E2H_12. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE2H.regs_out E' R' 14 Hregs) by lia. rewrite ro_E2H_14. L5KP.wordE' ZA Hag. }
  rewrite cells_E2H in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PE2H.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PE3 := LibSegZ_e2e3.
Definition KS_E3 : list nat := Eval vm_compute in (BG.kept_list 56 PE3.regs0 PE3.regs_out).
Lemma KS_E3_ok : BG.kept_ok 56 PE3.regs0 PE3.regs_out KS_E3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E3_1 : nth 1 PE3.regs_out (ELit 0) = ELit 133144. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E3_2 : nth 2 PE3.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit 352). Proof. vm_compute. reflexivity. Qed.
Lemma ro_E3_8 : nth 8 PE3.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E3_9 : nth 9 PE3.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E3_10 : nth 10 PE3.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma ro_E3_11 : nth 11 PE3.regs_out (ELit 0) = EVar 11. Proof. vm_compute. reflexivity. Qed.
Lemma cells_E3 : SR.ps_cells PE3.ps0 = PE3.cells. Proof. reflexivity. Qed.
Definition VAL_E3 (R : bvmap 5 word) (csp : Z) (v40 : Z) (v41 : Z) (v42 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 40%nat => Z_to_bv 64 v40 | 41%nat => Z_to_bv 64 v41 | 42%nat => Z_to_bv 64 v42 | _ => getr R (reg k) end.
Definition VZ_E3 (R : bvmap 5 word) (csp : Z) (v40 : Z) (v41 : Z) (v42 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 40%nat => v40 | 41%nat => v41 | 42%nat => v42 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_E3 R csp v40 v41 v42 : 0 <= csp < 2 ^ 64 -> 0 <= v40 < 2 ^ 64 -> 0 <= v41 < 2 ^ 64 -> 0 <= v42 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_E3 R csp v40 v41 v42) (fun _ => [])) k) = VZ_E3 R csp v40 v41 v42 k.
Proof.
  intros. cbn [ev]. unfold VAL_E3, VZ_E3.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e2e3_conc fx R M csp v40 v41 v42 :
  getr R (reg 2) = Z_to_bv 64 (csp + 320) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (459832) ->
  getr R (reg 10) = Z_to_bv 64 (v40) ->
  0 <= csp < 2 ^ 64 ->
  0 <= v40 < 2 ^ 64 ->
  0 <= v41 < 2 ^ 64 ->
  0 <= v42 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) + 256) (64) ->
  L5.defined M ((csp) + 256) (64) ->
  L5.img_clear M 65536 390664 ->
  L5.img_clear M 390704 390736 ->
  L5.img_clear M 390752 390760 ->
  L5.u64_at RSEGS M ((csp) + 344) (133144) ->
  L5.u64_at RSEGS M ((csp) + 336) (v41) ->
  L5.u64_at RSEGS M ((csp) + 328) (v42) ->
  exists fx' R' M', msteps RSEGS (st fx R 258096 M) (st fx' R' 133144 M')
    /\ (forall i, In i KS_E3 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (133144)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp + 352)
    /\ getr R' (reg 8) = Z_to_bv 64 (v41)
    /\ getr R' (reg 9) = Z_to_bv 64 (v42)
    /\ getr R' (reg 10) = Z_to_bv 64 (v40)
    /\ getr R' (reg 11) = getr R (reg 11)
    /\ (forall x : word, ~ ((csp) + 256 <= bv_unsigned x < (csp) + 256 + (64)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G40 G41 G42 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10.
  set (Vf := VAL_E3 R csp v40 v41 v42). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_E3 R csp v40 v41 v42 k) by (apply VAL_VZ_E3; lia). unfold VZ_E3 in ZA.
  assert (HR: regs_ok E PE3.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PE3.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PE3.kn0). { unfold know_ok, PE3.kn0. kn_allx ZA. }
  destruct (PE3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PE3.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PE3.regs0 PE3.regs_out 56 KS_E3 KS_E3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PE3.regs_out E' R' 1 Hregs) by lia. rewrite ro_E3_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE3.regs_out E' R' 2 Hregs) by lia. rewrite ro_E3_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE3.regs_out E' R' 8 Hregs) by lia. rewrite ro_E3_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE3.regs_out E' R' 9 Hregs) by lia. rewrite ro_E3_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE3.regs_out E' R' 10 Hregs) by lia. rewrite ro_E3_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PE3.regs_out E' R' 11 Hregs) by lia. rewrite ro_E3_11. cbn [edenot]. rewrite <- (proj1 Hag 11%nat) by lia. reflexivity. }
  rewrite cells_E3 in Hcells.
  split. { intros x Hy0. apply Hfr. unfold PE3.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

End L5CP2.
