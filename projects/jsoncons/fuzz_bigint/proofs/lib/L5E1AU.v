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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5E1AU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5E1U.
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
Module PS1S := LibSegZ_ps1su.
Definition KS_S1S : list nat := Eval vm_compute in (BG.kept_list 48 PS1S.regs0 PS1S.regs_out).
Lemma KS_S1S_ok : BG.kept_ok 48 PS1S.regs0 PS1S.regs_out KS_S1S = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1S_1 : nth 1 PS1S.regs_out (ELit 0) = ELit 134256. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1S_2 : nth 2 PS1S.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1S_10 : nth 10 PS1S.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 11) (ELit 1). Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1S_11 : nth 11 PS1S.regs_out (ELit 0) = EAlu Instr.ALU_SRL (EVar 41) (ELit 1). Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1S_12 : nth 12 PS1S.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma cells_S1S : SR.ps_cells PS1S.ps0 = PS1S.cells. Proof. reflexivity. Qed.
Definition VAL_S1S (R : bvmap 5 word) (sp : Z) (o : Z) (so : Z) (fbo : Z) (b0 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 10%nat => Z_to_bv 64 o | 11%nat => Z_to_bv 64 so | 40%nat => Z_to_bv 64 fbo | 41%nat => Z_to_bv 64 b0 | _ => getr R (reg k) end.
Definition VZ_S1S (R : bvmap 5 word) (sp : Z) (o : Z) (so : Z) (fbo : Z) (b0 : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 10%nat => o | 11%nat => so | 40%nat => fbo | 41%nat => b0 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_S1S R sp o so fbo b0 : 0 <= sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= so < 2 ^ 64 -> 0 <= fbo < 2 ^ 64 -> 0 <= b0 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_S1S R sp o so fbo b0) (fun _ => [])) k) = VZ_S1S R sp o so fbo b0 k.
Proof.
  intros. cbn [ev]. unfold VAL_S1S, VZ_S1S.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma ps1su_conc fx R M sp o so fbo b0 :
  getr R (reg 2) = Z_to_bv 64 sp ->
  getr R (reg 10) = Z_to_bv 64 o ->
  getr R (reg 11) = Z_to_bv 64 so ->
  0 <= sp < 2 ^ 64 ->
  0 <= o < 2 ^ 64 ->
  0 <= so < 2 ^ 64 ->
  0 <= fbo < 2 ^ 64 ->
  0 <= b0 < 2 ^ 64 ->
  140735332483104 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 32) (32) ->
  L5.writable RSEGS M (o) (32) ->
  L5.u8_at RSEGS M (o) (fbo) ->
  0 <= fbo <= 255 ->
  L5.u8_at RSEGS M (so) (b0) ->
  0 <= b0 <= 255 ->
  0 <= (Z.land (b0) (1)) <= 0 ->
  4096 <= o <= 140737488355327 ->
  (o) mod 8 = 0 ->
  4096 <= so <= 140737488355327 ->
  (so) mod 8 = 0 ->
  ((o) + 0 + (32) <= (so) + 0 \/ (so) + 0 + (24) <= (o) + 0) ->
  ((sp) + -32 + (32) <= (o) + 0 \/ (o) + 0 + (32) <= (sp) + -32) ->
  ((sp) + -32 + (32) <= (so) + 0 \/ (so) + 0 + (24) <= (sp) + -32) ->
  exists fx' R' M', msteps RSEGS (st fx R 134172 M) (st fx' R' 139880 M')
    /\ (forall i, In i KS_S1S -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (134256)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 32)
    /\ getr R' (reg 10) = Z_to_bv 64 (so + 1)
    /\ getr R' (reg 11) = Z_to_bv 64 (b0 / 2)
    /\ getr R' (reg 12) = Z_to_bv 64 (o)
    /\ L5.u64_at RSEGS M' ((o) + 24) (0)
    /\ L5.u64_at RSEGS M' ((o) + 16) (0)
    /\ L5.u64_at RSEGS M' ((o) + 8) (0)
    /\ L5.u8_at RSEGS M' ((o) + 0) (Z.land fbo 252)
    /\ L5.u64_at RSEGS M' ((sp) - 24) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' ((sp) - 16) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' ((sp) - 8) (bv_unsigned (getr R (reg 1)))
    /\ (forall x : word, ~ ((sp) + -32 <= bv_unsigned x < (sp) + -32 + (32)) -> ~ ((o) + 0 <= bv_unsigned x < (o) + 0 + (32)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H10 H11 G2 G10 G11 G40 G41 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16.
  set (Vf := VAL_S1S R sp o so fbo b0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_S1S R sp o so fbo b0 k) by (apply VAL_VZ_S1S; lia). unfold VZ_S1S in ZA.
  assert (HR: regs_ok E PS1S.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PS1S.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PS1S.kn0). { unfold know_ok, PS1S.kn0. kn_allx ZA. }
  destruct (PS1S.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PS1S.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PS1S.regs0 PS1S.regs_out 48 KS_S1S KS_S1S_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PS1S.regs_out E' R' 1 Hregs) by lia. rewrite ro_S1S_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1S.regs_out E' R' 2 Hregs) by lia. rewrite ro_S1S_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1S.regs_out E' R' 10 Hregs) by lia. rewrite ro_S1S_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1S.regs_out E' R' 11 Hregs) by lia. rewrite ro_S1S_11. apply BG.word_of_unsigned. zc_eval ZA Hag. first [reflexivity | lia]. }
  split. { rewrite (BG.out_reg PS1S.regs_out E' R' 12 Hregs) by lia. rewrite ro_S1S_12. L5KP.wordE' ZA Hag. }
  rewrite cells_S1S in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1S.cells, PS1S.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1S.cells, PS1S.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1S.cells, PS1S.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PS1S.cells, PS1S.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. zc_eval ZA Hag. rewrite ?Z.mod_small; [symmetry; apply L5PA.land252_div4; lia | rewrite L5PA.MM_val; lia]. apply L5PA.land252_range; lia. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1S.cells, PS1S.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1S.cells, PS1S.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1S.cells, PS1S.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1. apply Hfr. unfold PS1S.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PS1L := LibSegZ_ps1lu.
Definition KS_S1L : list nat := Eval vm_compute in (BG.kept_list 48 PS1L.regs0 PS1L.regs_out).
Lemma KS_S1L_ok : BG.kept_ok 48 PS1L.regs0 PS1L.regs_out KS_S1L = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1L_1 : nth 1 PS1L.regs_out (ELit 0) = ELit 134256. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1L_2 : nth 2 PS1L.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1L_10 : nth 10 PS1L.regs_out (ELit 0) = EVar 43. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1L_11 : nth 11 PS1L.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S1L_12 : nth 12 PS1L.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma cells_S1L : SR.ps_cells PS1L.ps0 = PS1L.cells. Proof. reflexivity. Qed.
Definition VAL_S1L (R : bvmap 5 word) (sp : Z) (o : Z) (so : Z) (fbo : Z) (b0 : Z) (slen : Z) (pd : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 10%nat => Z_to_bv 64 o | 11%nat => Z_to_bv 64 so | 40%nat => Z_to_bv 64 fbo | 41%nat => Z_to_bv 64 b0 | 42%nat => Z_to_bv 64 slen | 43%nat => Z_to_bv 64 pd | _ => getr R (reg k) end.
Definition VZ_S1L (R : bvmap 5 word) (sp : Z) (o : Z) (so : Z) (fbo : Z) (b0 : Z) (slen : Z) (pd : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 10%nat => o | 11%nat => so | 40%nat => fbo | 41%nat => b0 | 42%nat => slen | 43%nat => pd | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_S1L R sp o so fbo b0 slen pd : 0 <= sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= so < 2 ^ 64 -> 0 <= fbo < 2 ^ 64 -> 0 <= b0 < 2 ^ 64 -> 0 <= slen < 2 ^ 64 -> 0 <= pd < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_S1L R sp o so fbo b0 slen pd) (fun _ => [])) k) = VZ_S1L R sp o so fbo b0 slen pd k.
Proof.
  intros. cbn [ev]. unfold VAL_S1L, VZ_S1L.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma ps1lu_conc fx R M sp o so fbo b0 slen pd :
  getr R (reg 2) = Z_to_bv 64 sp ->
  getr R (reg 10) = Z_to_bv 64 o ->
  getr R (reg 11) = Z_to_bv 64 so ->
  0 <= sp < 2 ^ 64 ->
  0 <= o < 2 ^ 64 ->
  0 <= so < 2 ^ 64 ->
  0 <= fbo < 2 ^ 64 ->
  0 <= b0 < 2 ^ 64 ->
  0 <= slen < 2 ^ 64 ->
  0 <= pd < 2 ^ 64 ->
  140735332483104 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 32) (32) ->
  L5.writable RSEGS M (o) (32) ->
  L5.u8_at RSEGS M (o) (fbo) ->
  0 <= fbo <= 255 ->
  L5.u8_at RSEGS M (so) (b0) ->
  0 <= b0 <= 255 ->
  1 <= (Z.land (b0) (1)) <= 1 ->
  L5.u64_at RSEGS M ((so) + 8) (slen) ->
  L5.u64_at RSEGS M ((so) + 16) (pd) ->
  4096 <= o <= 140737488355327 ->
  (o) mod 8 = 0 ->
  4096 <= so <= 140737488355327 ->
  (so) mod 8 = 0 ->
  ((o) + 0 + (32) <= (so) + 0 \/ (so) + 0 + (24) <= (o) + 0) ->
  ((sp) + -32 + (32) <= (o) + 0 \/ (o) + 0 + (32) <= (sp) + -32) ->
  ((sp) + -32 + (32) <= (so) + 0 \/ (so) + 0 + (24) <= (sp) + -32) ->
  exists fx' R' M', msteps RSEGS (st fx R 134172 M) (st fx' R' 139880 M')
    /\ (forall i, In i KS_S1L -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (134256)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 32)
    /\ getr R' (reg 10) = Z_to_bv 64 (pd)
    /\ getr R' (reg 11) = Z_to_bv 64 (slen)
    /\ getr R' (reg 12) = Z_to_bv 64 (o)
    /\ L5.u64_at RSEGS M' ((o) + 24) (0)
    /\ L5.u64_at RSEGS M' ((o) + 16) (0)
    /\ L5.u64_at RSEGS M' ((o) + 8) (0)
    /\ L5.u8_at RSEGS M' ((o) + 0) (Z.land fbo 252)
    /\ L5.u64_at RSEGS M' ((sp) - 24) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' ((sp) - 16) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' ((sp) - 8) (bv_unsigned (getr R (reg 1)))
    /\ (forall x : word, ~ ((sp) + -32 <= bv_unsigned x < (sp) + -32 + (32)) -> ~ ((o) + 0 <= bv_unsigned x < (o) + 0 + (32)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H10 H11 G2 G10 G11 G40 G41 G42 G43 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18.
  set (Vf := VAL_S1L R sp o so fbo b0 slen pd). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_S1L R sp o so fbo b0 slen pd k) by (apply VAL_VZ_S1L; lia). unfold VZ_S1L in ZA.
  assert (HR: regs_ok E PS1L.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PS1L.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PS1L.kn0). { unfold know_ok, PS1L.kn0. kn_allx ZA. }
  destruct (PS1L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PS1L.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PS1L.regs0 PS1L.regs_out 48 KS_S1L KS_S1L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PS1L.regs_out E' R' 1 Hregs) by lia. rewrite ro_S1L_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1L.regs_out E' R' 2 Hregs) by lia. rewrite ro_S1L_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1L.regs_out E' R' 10 Hregs) by lia. rewrite ro_S1L_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1L.regs_out E' R' 11 Hregs) by lia. rewrite ro_S1L_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS1L.regs_out E' R' 12 Hregs) by lia. rewrite ro_S1L_12. L5KP.wordE' ZA Hag. }
  rewrite cells_S1L in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1L.cells, PS1L.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1L.cells, PS1L.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1L.cells, PS1L.cells0. right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PS1L.cells, PS1L.cells0. right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. zc_eval ZA Hag. rewrite ?Z.mod_small; [symmetry; apply L5PA.land252_div4; lia | rewrite L5PA.MM_val; lia]. apply L5PA.land252_range; lia. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1L.cells, PS1L.cells0. right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1L.cells, PS1L.cells0. right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PS1L.cells, PS1L.cells0. right; right; right; right; right; right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1. apply Hfr. unfold PS1L.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PS2 := LibSegZ_ps2u.
Definition KS_S2 : list nat := Eval vm_compute in (BG.kept_list 48 PS2.regs0 PS2.regs_out).
Lemma KS_S2_ok : BG.kept_ok 48 PS2.regs0 PS2.regs_out KS_S2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2_1 : nth 1 PS2.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2_2 : nth 2 PS2.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2_8 : nth 8 PS2.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S2_9 : nth 9 PS2.regs_out (ELit 0) = EVar 43. Proof. vm_compute. reflexivity. Qed.
Lemma cells_S2 : SR.ps_cells PS2.ps0 = PS2.cells. Proof. reflexivity. Qed.
Definition VAL_S2 (R : bvmap 5 word) (sp : Z) (c1 : Z) (c2 : Z) (c3 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 41%nat => Z_to_bv 64 c1 | 42%nat => Z_to_bv 64 c2 | 43%nat => Z_to_bv 64 c3 | _ => getr R (reg k) end.
Definition VZ_S2 (R : bvmap 5 word) (sp : Z) (c1 : Z) (c2 : Z) (c3 : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 41%nat => c1 | 42%nat => c2 | 43%nat => c3 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_S2 R sp c1 c2 c3 : 0 <= sp < 2 ^ 64 -> 0 <= c1 < 2 ^ 64 -> 0 <= c2 < 2 ^ 64 -> 0 <= c3 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_S2 R sp c1 c2 c3) (fun _ => [])) k) = VZ_S2 R sp c1 c2 c3 k.
Proof.
  intros. cbn [ev]. unfold VAL_S2, VZ_S2.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma ps2u_conc fx R M sp c1 c2 c3 :
  getr R (reg 2) = Z_to_bv 64 (sp - 32) ->
  getr R (reg 11) = Z_to_bv 64 (0) ->
  0 <= sp < 2 ^ 64 ->
  0 <= c1 < 2 ^ 64 ->
  0 <= c2 < 2 ^ 64 ->
  0 <= c3 < 2 ^ 64 ->
  140735332483104 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.u64_at RSEGS M ((sp) - 8) (c1) ->
  L5.u64_at RSEGS M ((sp) - 16) (c2) ->
  L5.u64_at RSEGS M ((sp) - 24) (c3) ->
  exists fx' R' M', msteps RSEGS (st fx R 134256 M) (st fx' R' 134280 M')
    /\ (forall i, In i KS_S2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (c1)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp)
    /\ getr R' (reg 8) = Z_to_bv 64 (c2)
    /\ getr R' (reg 9) = Z_to_bv 64 (c3)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H11 G2 G41 G42 G43 K1 K2 K3 K4 K5.
  set (Vf := VAL_S2 R sp c1 c2 c3). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_S2 R sp c1 c2 c3 k) by (apply VAL_VZ_S2; lia). unfold VZ_S2 in ZA.
  assert (HR: regs_ok E PS2.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PS2.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PS2.kn0). { unfold know_ok, PS2.kn0. kn_allx ZA. }
  destruct (PS2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PS2.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PS2.regs0 PS2.regs_out 48 KS_S2 KS_S2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PS2.regs_out E' R' 1 Hregs) by lia. rewrite ro_S2_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2.regs_out E' R' 2 Hregs) by lia. rewrite ro_S2_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2.regs_out E' R' 8 Hregs) by lia. rewrite ro_S2_8. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS2.regs_out E' R' 9 Hregs) by lia. rewrite ro_S2_9. L5KP.wordE' ZA Hag. }
  rewrite cells_S2 in Hcells.
  split. { intros x. apply Hfr. unfold PS2.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PS3 := LibSegZ_ps3u.
Definition KS_S3 : list nat := Eval vm_compute in (BG.kept_list 48 PS3.regs0 PS3.regs_out).
Lemma KS_S3_ok : BG.kept_ok 48 PS3.regs0 PS3.regs_out KS_S3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S3_2 : nth 2 PS3.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_S3_9 : nth 9 PS3.regs_out (ELit 0) = ELit 22. Proof. vm_compute. reflexivity. Qed.
Lemma ro_S3_10 : nth 10 PS3.regs_out (ELit 0) = ELit 32. Proof. vm_compute. reflexivity. Qed.
Lemma cells_S3 : SR.ps_cells PS3.ps0 = PS3.cells. Proof. reflexivity. Qed.
Definition VAL_S3 (R : bvmap 5 word) (sp : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | _ => getr R (reg k) end.
Definition VZ_S3 (R : bvmap 5 word) (sp : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_S3 R sp : 0 <= sp < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_S3 R sp) (fun _ => [])) k) = VZ_S3 R sp k.
Proof.
  intros. cbn [ev]. unfold VAL_S3, VZ_S3.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma ps3u_conc fx R M sp :
  getr R (reg 2) = Z_to_bv 64 (sp - 32) ->
  getr R (reg 11) = Z_to_bv 64 (22) ->
  0 <= sp < 2 ^ 64 ->
  140735332483104 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  exists fx' R' M', msteps RSEGS (st fx R 134256 M) (st fx' R' 134288 M')
    /\ (forall i, In i KS_S3 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 32)
    /\ getr R' (reg 9) = Z_to_bv 64 (22)
    /\ getr R' (reg 10) = Z_to_bv 64 (32)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H11 G2 K1 K2.
  set (Vf := VAL_S3 R sp). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_S3 R sp k) by (apply VAL_VZ_S3; lia). unfold VZ_S3 in ZA.
  assert (HR: regs_ok E PS3.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PS3.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PS3.kn0). { unfold know_ok, PS3.kn0. kn_allx ZA. }
  destruct (PS3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PS3.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PS3.regs0 PS3.regs_out 48 KS_S3 KS_S3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PS3.regs_out E' R' 2 Hregs) by lia. rewrite ro_S3_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS3.regs_out E' R' 9 Hregs) by lia. rewrite ro_S3_9. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PS3.regs_out E' R' 10 Hregs) by lia. rewrite ro_S3_10. L5KP.wordE' ZA Hag. }
  rewrite cells_S3 in Hcells.
  split. { intros x. apply Hfr. unfold PS3.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PA1 := LibSegZ_e1a1u.
Definition KS_A1 : list nat := Eval vm_compute in (BG.kept_list 56 PA1.regs0 PA1.regs_out).
Lemma KS_A1_ok : BG.kept_ok 56 PA1.regs0 PA1.regs_out KS_A1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_1 : nth 1 PA1.regs_out (ELit 0) = ELit 261856. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_2 : nth 2 PA1.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_8 : nth 8 PA1.regs_out (ELit 0) = ELit 160. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_10 : nth 10 PA1.regs_out (ELit 0) = ELit 16. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A1_11 : nth 11 PA1.regs_out (ELit 0) = ELit 160. Proof. vm_compute. reflexivity. Qed.
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
Lemma e1a1u_conc fx R M csp obj :
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 10) = Z_to_bv 64 (32) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 112) (112) ->
  L5.defined M ((csp) - 112) (112) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (160) ->
  L5.defined M ((obj) - 128) (160) ->
  ((csp) + -112 + (112) <= (obj) + -128 \/ (obj) + -128 + (160) <= (csp) + -112) ->
  ((obj) + -128 + (160) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  exists fx' R' M', msteps RSEGS (st fx R 134288 M) (st fx' R' 312388 M')
    /\ (forall i, In i KS_A1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (261856)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp - 48)
    /\ getr R' (reg 8) = Z_to_bv 64 (160)
    /\ getr R' (reg 10) = Z_to_bv 64 (16)
    /\ getr R' (reg 11) = Z_to_bv 64 (160)
    /\ L5.u64_at RSEGS M' ((csp) - 48) (160)
    /\ L5.u64_at RSEGS M' ((csp) - 40) (260052)
    /\ L5.u64_at RSEGS M' ((csp) - 24) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' ((csp) - 16) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' ((csp) - 8) (134292)
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
Module PA2 := LibSegZ_e1a2u.
Definition KS_A2 : list nat := Eval vm_compute in (BG.kept_list 56 PA2.regs0 PA2.regs_out).
Lemma KS_A2_ok : BG.kept_ok 56 PA2.regs0 PA2.regs_out KS_A2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_1 : nth 1 PA2.regs_out (ELit 0) = ELit 134292. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_2 : nth 2 PA2.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_8 : nth 8 PA2.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_9 : nth 9 PA2.regs_out (ELit 0) = ELit 22. Proof. vm_compute. reflexivity. Qed.
Lemma ro_A2_10 : nth 10 PA2.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A2 : SR.ps_cells PA2.ps0 = PA2.cells. Proof. reflexivity. Qed.
Definition VAL_A2 (R : bvmap 5 word) (csp : Z) (obj : Z) (x40 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 x40 | _ => getr R (reg k) end.
Definition VZ_A2 (R : bvmap 5 word) (csp : Z) (obj : Z) (x40 : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => x40 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_A2 R csp obj x40 : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= x40 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_A2 R csp obj x40) (fun _ => [])) k) = VZ_A2 R csp obj x40 k.
Proof.
  intros. cbn [ev]. unfold VAL_A2, VZ_A2.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e1a2u_conc fx R M csp obj x40 :
  getr R (reg 2) = Z_to_bv 64 (csp - 48) ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 10) = Z_to_bv 64 (obj - 128) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= x40 < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 112) (64) ->
  L5.defined M ((csp) - 112) (64) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (160) ->
  L5.defined M ((obj) - 128) (160) ->
  ((csp) + -112 + (112) <= (obj) + -128 \/ (obj) + -128 + (160) <= (csp) + -112) ->
  ((obj) + -128 + (160) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u64_at RSEGS M ((csp) - 40) (260052) ->
  L5.u64_at RSEGS M ((csp) - 48) (160) ->
  L5.u64_at RSEGS M ((csp) - 8) (134292) ->
  L5.u64_at RSEGS M ((csp) - 16) (x40) ->
  L5.u64_at RSEGS M ((csp) - 24) (22) ->
  exists fx' R' M', msteps RSEGS (st fx R 261856 M) (st fx' R' 134308 M')
    /\ (forall i, In i KS_A2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (134292)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp)
    /\ getr R' (reg 8) = Z_to_bv 64 (obj)
    /\ getr R' (reg 9) = Z_to_bv 64 (22)
    /\ getr R' (reg 10) = Z_to_bv 64 (0)
    /\ L5KP.zeros_at M' ((obj) - 128) (160)
    /\ (forall x : word, ~ ((csp) + -112 <= bv_unsigned x < (csp) + -112 + (64)) -> ~ ((obj) + -128 <= bv_unsigned x < (obj) + -128 + (160)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18.
  set (Vf := VAL_A2 R csp obj x40). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_A2 R csp obj x40 k) by (apply VAL_VZ_A2; lia). unfold VZ_A2 in ZA.
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
  rewrite cells_A2 in Hcells.
  split. { eapply L5KP.zeros_of_KZero. apply Hcells. unfold PA2.cells, PA2.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0 Hy1. apply Hfr. unfold PA2.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PG0 := LibSegZ_e1g1u_g0.
Definition KS_G0 : list nat := Eval vm_compute in (BG.kept_list 56 PG0.regs0 PG0.regs_out).
Lemma KS_G0_ok : BG.kept_ok 56 PG0.regs0 PG0.regs_out KS_G0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G0_1 : nth 1 PG0.regs_out (ELit 0) = ELit 134312. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G0_2 : nth 2 PG0.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G0_8 : nth 8 PG0.regs_out (ELit 0) = EVar 8. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G0_9 : nth 9 PG0.regs_out (ELit 0) = EVar 9. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G0_10 : nth 10 PG0.regs_out (ELit 0) = EVar 8. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G0_11 : nth 11 PG0.regs_out (ELit 0) = EVar 9. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G0_12 : nth 12 PG0.regs_out (ELit 0) = ELit 393560. Proof. vm_compute. reflexivity. Qed.
Lemma cells_G0 : SR.ps_cells PG0.ps0 = PG0.cells. Proof. reflexivity. Qed.
Definition VAL_G0 (R : bvmap 5 word) (csp : Z) (obj : Z) (a0v : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 a0v | _ => getr R (reg k) end.
Definition VZ_G0 (R : bvmap 5 word) (csp : Z) (obj : Z) (a0v : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => a0v | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_G0 R csp obj a0v : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= a0v < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_G0 R csp obj a0v) (fun _ => [])) k) = VZ_G0 R csp obj a0v k.
Proof.
  intros. cbn [ev]. unfold VAL_G0, VZ_G0.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e1g1u_g0_conc fx R M csp obj a0v :
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 10) = Z_to_bv 64 (a0v) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= a0v < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 80) (80) ->
  L5.defined M ((csp) - 80) (80) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (160) ->
  L5.defined M ((obj) - 128) (160) ->
  ((csp) + -80 + (80) <= (obj) + -128 \/ (obj) + -128 + (160) <= (csp) + -80) ->
  ((obj) + -128 + (160) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u8_at RSEGS M ((0) + 460320) (0) ->
  L5.u8_at RSEGS M ((0) + 460321) (0) ->
  L5.writable RSEGS M ((0) + 460320) (8) ->
  L5.writable RSEGS M ((0) + 460320) (1) ->
  L5.writable RSEGS M ((0) + 460321) (1) ->
  exists fx' R' M', msteps RSEGS (st fx R 134308 M) (st fx' R' 134324 M')
    /\ (forall i, In i KS_G0 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (134312)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp)
    /\ getr R' (reg 8) = getr R (reg 8)
    /\ getr R' (reg 9) = getr R (reg 9)
    /\ getr R' (reg 10) = getr R (reg 8)
    /\ getr R' (reg 11) = getr R (reg 9)
    /\ getr R' (reg 12) = Z_to_bv 64 (393560)
    /\ L5.u8_at RSEGS M' ((0) + 460321) (1)
    /\ L5.u8_at RSEGS M' ((0) + 460320) (1)
    /\ (forall x : word, ~ ((csp) + -80 <= bv_unsigned x < (csp) + -80 + (80)) -> ~ ((0) + 460320 <= bv_unsigned x < (0) + 460320 + (1)) -> ~ ((0) + 460321 <= bv_unsigned x < (0) + 460321 + (1)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18.
  set (Vf := VAL_G0 R csp obj a0v). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_G0 R csp obj a0v k) by (apply VAL_VZ_G0; lia). unfold VZ_G0 in ZA.
  assert (HR: regs_ok E PG0.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PG0.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PG0.kn0). { unfold know_ok, PG0.kn0. kn_allx ZA. }
  destruct (PG0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PG0.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PG0.regs0 PG0.regs_out 56 KS_G0 KS_G0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PG0.regs_out E' R' 1 Hregs) by lia. rewrite ro_G0_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PG0.regs_out E' R' 2 Hregs) by lia. rewrite ro_G0_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PG0.regs_out E' R' 8 Hregs) by lia. rewrite ro_G0_8. cbn [edenot]. rewrite <- (proj1 Hag 8%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PG0.regs_out E' R' 9 Hregs) by lia. rewrite ro_G0_9. cbn [edenot]. rewrite <- (proj1 Hag 9%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PG0.regs_out E' R' 10 Hregs) by lia. rewrite ro_G0_10. cbn [edenot]. rewrite <- (proj1 Hag 8%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PG0.regs_out E' R' 11 Hregs) by lia. rewrite ro_G0_11. cbn [edenot]. rewrite <- (proj1 Hag 9%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PG0.regs_out E' R' 12 Hregs) by lia. rewrite ro_G0_12. L5KP.wordE' ZA Hag. }
  rewrite cells_G0 in Hcells.
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PG0.cells, PG0.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PG0.cells, PG0.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { intros x Hy0 Hy1 Hy2. apply Hfr. unfold PG0.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PG1 := LibSegZ_e1g1u_g1.
Definition KS_G1 : list nat := Eval vm_compute in (BG.kept_list 56 PG1.regs0 PG1.regs_out).
Lemma KS_G1_ok : BG.kept_ok 56 PG1.regs0 PG1.regs_out KS_G1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G1_1 : nth 1 PG1.regs_out (ELit 0) = ELit 134312. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G1_2 : nth 2 PG1.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G1_8 : nth 8 PG1.regs_out (ELit 0) = EVar 8. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G1_9 : nth 9 PG1.regs_out (ELit 0) = EVar 9. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G1_10 : nth 10 PG1.regs_out (ELit 0) = EVar 8. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G1_11 : nth 11 PG1.regs_out (ELit 0) = EVar 9. Proof. vm_compute. reflexivity. Qed.
Lemma ro_G1_12 : nth 12 PG1.regs_out (ELit 0) = ELit 393560. Proof. vm_compute. reflexivity. Qed.
Lemma cells_G1 : SR.ps_cells PG1.ps0 = PG1.cells. Proof. reflexivity. Qed.
Definition VAL_G1 (R : bvmap 5 word) (csp : Z) (obj : Z) (a0v : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 csp | 10%nat => Z_to_bv 64 obj | 40%nat => Z_to_bv 64 a0v | _ => getr R (reg k) end.
Definition VZ_G1 (R : bvmap 5 word) (csp : Z) (obj : Z) (a0v : Z) (k : nat) : Z :=
  match k with | 2%nat => csp | 10%nat => obj | 40%nat => a0v | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_G1 R csp obj a0v : 0 <= csp < 2 ^ 64 -> 0 <= obj < 2 ^ 64 -> 0 <= a0v < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_G1 R csp obj a0v) (fun _ => [])) k) = VZ_G1 R csp obj a0v k.
Proof.
  intros. cbn [ev]. unfold VAL_G1, VZ_G1.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma e1g1u_g1_conc fx R M csp obj a0v :
  getr R (reg 2) = Z_to_bv 64 csp ->
  getr R (reg 3) = Z_to_bv 64 (67584) ->
  getr R (reg 4) = Z_to_bv 64 (462648) ->
  getr R (reg 10) = Z_to_bv 64 (a0v) ->
  0 <= csp < 2 ^ 64 ->
  0 <= obj < 2 ^ 64 ->
  0 <= a0v < 2 ^ 64 ->
  1099511627776 <= csp <= 140737488355328 ->
  (csp) mod 16 = 0 ->
  L5.writable RSEGS M ((csp) - 80) (80) ->
  L5.defined M ((csp) - 80) (80) ->
  4224 <= obj <= 140737488355328 ->
  (obj) mod 16 = 0 ->
  L5.writable RSEGS M ((obj) - 128) (160) ->
  L5.defined M ((obj) - 128) (160) ->
  ((csp) + -80 + (80) <= (obj) + -128 \/ (obj) + -128 + (160) <= (csp) + -80) ->
  ((obj) + -128 + (160) <= (0) + 65536 \/ (0) + 65536 + (532480) <= (obj) + -128) ->
  L5.img_clear M 65536 393472 ->
  L5.img_clear M 393512 393544 ->
  L5.img_clear M 393560 393568 ->
  L5.u8_at RSEGS M ((0) + 460320) (1) ->
  L5.u8_at RSEGS M ((0) + 460321) (1) ->
  L5.writable RSEGS M ((0) + 460320) (8) ->
  L5.writable RSEGS M ((0) + 460320) (1) ->
  L5.writable RSEGS M ((0) + 460321) (1) ->
  exists fx' R' M', msteps RSEGS (st fx R 134308 M) (st fx' R' 134324 M')
    /\ (forall i, In i KS_G1 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (134312)
    /\ getr R' (reg 2) = Z_to_bv 64 (csp)
    /\ getr R' (reg 8) = getr R (reg 8)
    /\ getr R' (reg 9) = getr R (reg 9)
    /\ getr R' (reg 10) = getr R (reg 8)
    /\ getr R' (reg 11) = getr R (reg 9)
    /\ getr R' (reg 12) = Z_to_bv 64 (393560)
    /\ L5.u8_at RSEGS M' ((0) + 460320) (1)
    /\ L5.u8_at RSEGS M' ((0) + 460321) (1)
    /\ (forall x : word, ~ ((csp) + -80 <= bv_unsigned x < (csp) + -80 + (80)) -> ~ ((0) + 460320 <= bv_unsigned x < (0) + 460320 + (1)) -> ~ ((0) + 460321 <= bv_unsigned x < (0) + 460321 + (1)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H3 H4 H10 G2 G10 G40 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18.
  set (Vf := VAL_G1 R csp obj a0v). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_G1 R csp obj a0v k) by (apply VAL_VZ_G1; lia). unfold VZ_G1 in ZA.
  assert (HR: regs_ok E PG1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PG1.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PG1.kn0). { unfold know_ok, PG1.kn0. kn_allx ZA. }
  destruct (PG1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PG1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PG1.regs0 PG1.regs_out 56 KS_G1 KS_G1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PG1.regs_out E' R' 1 Hregs) by lia. rewrite ro_G1_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PG1.regs_out E' R' 2 Hregs) by lia. rewrite ro_G1_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PG1.regs_out E' R' 8 Hregs) by lia. rewrite ro_G1_8. cbn [edenot]. rewrite <- (proj1 Hag 8%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PG1.regs_out E' R' 9 Hregs) by lia. rewrite ro_G1_9. cbn [edenot]. rewrite <- (proj1 Hag 9%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PG1.regs_out E' R' 10 Hregs) by lia. rewrite ro_G1_10. cbn [edenot]. rewrite <- (proj1 Hag 8%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PG1.regs_out E' R' 11 Hregs) by lia. rewrite ro_G1_11. cbn [edenot]. rewrite <- (proj1 Hag 9%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PG1.regs_out E' R' 12 Hregs) by lia. rewrite ro_G1_12. L5KP.wordE' ZA Hag. }
  rewrite cells_G1 in Hcells.
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PG1.cells, PG1.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { eapply L5KP.u8_of_KWord1. apply Hcells. unfold PG1.cells, PG1.cells0. right; left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. lia. }
  split. { intros x Hy0 Hy1 Hy2. apply Hfr. unfold PG1.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

End L5E1U.
