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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5TobigA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5TB.
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
Module PP0 := LibSegZ_pt0.
Definition KS_P0 : list nat := Eval vm_compute in (BG.kept_list 48 PP0.regs0 PP0.regs_out).
Lemma KS_P0_ok : BG.kept_ok 48 PP0.regs0 PP0.regs_out KS_P0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P0_1 : nth 1 PP0.regs_out (ELit 0) = EVar 1. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P0_2 : nth 2 PP0.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P0_11 : nth 11 PP0.regs_out (ELit 0) = ELit 22. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P0 : SR.ps_cells PP0.ps0 = PP0.cells. Proof. reflexivity. Qed.
Definition VAL_P0 (R : bvmap 5 word) (sp : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | _ => getr R (reg k) end.
Definition VZ_P0 (R : bvmap 5 word) (sp : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P0 R sp : 0 <= sp < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P0 R sp) (fun _ => [])) k) = VZ_P0 R sp k.
Proof.
  intros. cbn [ev]. unfold VAL_P0, VZ_P0.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pt0_conc fx R M sp :
  getr R (reg 2) = Z_to_bv 64 sp ->
  getr R (reg 11) = Z_to_bv 64 (0) ->
  0 <= sp < 2 ^ 64 ->
  140735332483088 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  exists fx' R' M', msteps RSEGS (st fx R 138048 M) (st fx' R' 138124 M')
    /\ (forall i, In i KS_P0 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = getr R (reg 1)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp)
    /\ getr R' (reg 11) = Z_to_bv 64 (22)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H11 G2 K1 K2.
  set (Vf := VAL_P0 R sp). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P0 R sp k) by (apply VAL_VZ_P0; lia). unfold VZ_P0 in ZA.
  assert (HR: regs_ok E PP0.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP0.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP0.kn0). { unfold know_ok, PP0.kn0. kn_allx ZA. }
  destruct (PP0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP0.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP0.regs0 PP0.regs_out 48 KS_P0 KS_P0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP0.regs_out E' R' 1 Hregs) by lia. rewrite ro_P0_1. cbn [edenot]. rewrite <- (proj1 Hag 1%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PP0.regs_out E' R' 2 Hregs) by lia. rewrite ro_P0_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP0.regs_out E' R' 11 Hregs) by lia. rewrite ro_P0_11. L5KP.wordE' ZA Hag. }
  rewrite cells_P0 in Hcells.
  split. { intros x. apply Hfr. unfold PP0.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP1M := LibSegZ_pt1m.
Definition KS_P1M : list nat := Eval vm_compute in (BG.kept_list 48 PP1M.regs0 PP1M.regs_out).
Lemma KS_P1M_ok : BG.kept_ok 48 PP1M.regs0 PP1M.regs_out KS_P1M = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1M_1 : nth 1 PP1M.regs_out (ELit 0) = ELit 138108. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1M_2 : nth 2 PP1M.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-16)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1M_10 : nth 10 PP1M.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit 1). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1M_11 : nth 11 PP1M.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 11) (ELit (-1)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1M_12 : nth 12 PP1M.regs_out (ELit 0) = ELit 1. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1M_13 : nth 13 PP1M.regs_out (ELit 0) = EVar 12. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P1M : SR.ps_cells PP1M.ps0 = PP1M.cells. Proof. reflexivity. Qed.
Definition VAL_P1M (R : bvmap 5 word) (sp : Z) (p : Z) (n : Z) (o : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 10%nat => Z_to_bv 64 p | 11%nat => Z_to_bv 64 n | 12%nat => Z_to_bv 64 o | _ => getr R (reg k) end.
Definition VZ_P1M (R : bvmap 5 word) (sp : Z) (p : Z) (n : Z) (o : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 10%nat => p | 11%nat => n | 12%nat => o | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P1M R sp p n o : 0 <= sp < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P1M R sp p n o) (fun _ => [])) k) = VZ_P1M R sp p n o k.
Proof.
  intros. cbn [ev]. unfold VAL_P1M, VZ_P1M.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pt1m_conc fx R M sp p n o :
  getr R (reg 2) = Z_to_bv 64 sp ->
  getr R (reg 10) = Z_to_bv 64 p ->
  getr R (reg 11) = Z_to_bv 64 n ->
  getr R (reg 12) = Z_to_bv 64 o ->
  0 <= sp < 2 ^ 64 ->
  0 <= p < 2 ^ 64 ->
  0 <= n < 2 ^ 64 ->
  0 <= o < 2 ^ 64 ->
  140735332483088 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 16) (16) ->
  1 <= n <= 4999 ->
  4096 <= p <= 140737488355327 ->
  L5.u8_at RSEGS M (p) (45) ->
  ((sp) + -16 + (16) <= (p) + 0 \/ (p) + 0 + (1) <= (sp) + -16) ->
  exists fx' R' M', msteps RSEGS (st fx R 138048 M) (st fx' R' 134064 M')
    /\ (forall i, In i KS_P1M -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (138108)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 16)
    /\ getr R' (reg 10) = Z_to_bv 64 (p + 1)
    /\ getr R' (reg 11) = Z_to_bv 64 (n - 1)
    /\ getr R' (reg 12) = Z_to_bv 64 (1)
    /\ getr R' (reg 13) = Z_to_bv 64 (o)
    /\ L5.u64_at RSEGS M' ((sp) - 8) (bv_unsigned (getr R (reg 1)))
    /\ (forall x : word, ~ ((sp) + -16 <= bv_unsigned x < (sp) + -16 + (16)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H10 H11 H12 G2 G10 G11 G12 K1 K2 K3 K4 K5 K6 K7.
  set (Vf := VAL_P1M R sp p n o). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P1M R sp p n o k) by (apply VAL_VZ_P1M; lia). unfold VZ_P1M in ZA.
  assert (HR: regs_ok E PP1M.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP1M.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP1M.kn0). { unfold know_ok, PP1M.kn0. kn_allx ZA. }
  destruct (PP1M.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP1M.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP1M.regs0 PP1M.regs_out 48 KS_P1M KS_P1M_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP1M.regs_out E' R' 1 Hregs) by lia. rewrite ro_P1M_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1M.regs_out E' R' 2 Hregs) by lia. rewrite ro_P1M_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1M.regs_out E' R' 10 Hregs) by lia. rewrite ro_P1M_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1M.regs_out E' R' 11 Hregs) by lia. rewrite ro_P1M_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1M.regs_out E' R' 12 Hregs) by lia. rewrite ro_P1M_12. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1M.regs_out E' R' 13 Hregs) by lia. rewrite ro_P1M_13. L5KP.wordE' ZA Hag. }
  rewrite cells_P1M in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PP1M.cells, PP1M.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0. apply Hfr. unfold PP1M.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP1L := LibSegZ_pt1pl.
Definition KS_P1L : list nat := Eval vm_compute in (BG.kept_list 48 PP1L.regs0 PP1L.regs_out).
Lemma KS_P1L_ok : BG.kept_ok 48 PP1L.regs0 PP1L.regs_out KS_P1L = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1L_1 : nth 1 PP1L.regs_out (ELit 0) = ELit 138108. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1L_2 : nth 2 PP1L.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-16)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1L_10 : nth 10 PP1L.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1L_11 : nth 11 PP1L.regs_out (ELit 0) = EVar 11. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1L_12 : nth 12 PP1L.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1L_13 : nth 13 PP1L.regs_out (ELit 0) = EVar 12. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P1L : SR.ps_cells PP1L.ps0 = PP1L.cells. Proof. reflexivity. Qed.
Definition VAL_P1L (R : bvmap 5 word) (sp : Z) (p : Z) (n : Z) (o : Z) (c : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 10%nat => Z_to_bv 64 p | 11%nat => Z_to_bv 64 n | 12%nat => Z_to_bv 64 o | 40%nat => Z_to_bv 64 c | _ => getr R (reg k) end.
Definition VZ_P1L (R : bvmap 5 word) (sp : Z) (p : Z) (n : Z) (o : Z) (c : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 10%nat => p | 11%nat => n | 12%nat => o | 40%nat => c | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P1L R sp p n o c : 0 <= sp < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P1L R sp p n o c) (fun _ => [])) k) = VZ_P1L R sp p n o c k.
Proof.
  intros. cbn [ev]. unfold VAL_P1L, VZ_P1L.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pt1pl_conc fx R M sp p n o c :
  getr R (reg 2) = Z_to_bv 64 sp ->
  getr R (reg 10) = Z_to_bv 64 p ->
  getr R (reg 11) = Z_to_bv 64 n ->
  getr R (reg 12) = Z_to_bv 64 o ->
  0 <= sp < 2 ^ 64 ->
  0 <= p < 2 ^ 64 ->
  0 <= n < 2 ^ 64 ->
  0 <= o < 2 ^ 64 ->
  0 <= c < 2 ^ 64 ->
  140735332483088 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 16) (16) ->
  1 <= n <= 4999 ->
  4096 <= p <= 140737488355327 ->
  L5.u8_at RSEGS M (p) (c) ->
  0 <= c <= 44 ->
  ((sp) + -16 + (16) <= (p) + 0 \/ (p) + 0 + (1) <= (sp) + -16) ->
  exists fx' R' M', msteps RSEGS (st fx R 138048 M) (st fx' R' 134064 M')
    /\ (forall i, In i KS_P1L -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (138108)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 16)
    /\ getr R' (reg 10) = Z_to_bv 64 (p)
    /\ getr R' (reg 11) = Z_to_bv 64 (n)
    /\ getr R' (reg 12) = Z_to_bv 64 (0)
    /\ getr R' (reg 13) = Z_to_bv 64 (o)
    /\ L5.u64_at RSEGS M' ((sp) - 8) (bv_unsigned (getr R (reg 1)))
    /\ (forall x : word, ~ ((sp) + -16 <= bv_unsigned x < (sp) + -16 + (16)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H10 H11 H12 G2 G10 G11 G12 G40 K1 K2 K3 K4 K5 K6 K7 K8.
  set (Vf := VAL_P1L R sp p n o c). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P1L R sp p n o c k) by (apply VAL_VZ_P1L; lia). unfold VZ_P1L in ZA.
  assert (HR: regs_ok E PP1L.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP1L.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP1L.kn0). { unfold know_ok, PP1L.kn0. kn_allx ZA. }
  destruct (PP1L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP1L.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP1L.regs0 PP1L.regs_out 48 KS_P1L KS_P1L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP1L.regs_out E' R' 1 Hregs) by lia. rewrite ro_P1L_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1L.regs_out E' R' 2 Hregs) by lia. rewrite ro_P1L_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1L.regs_out E' R' 10 Hregs) by lia. rewrite ro_P1L_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1L.regs_out E' R' 11 Hregs) by lia. rewrite ro_P1L_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1L.regs_out E' R' 12 Hregs) by lia. rewrite ro_P1L_12. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1L.regs_out E' R' 13 Hregs) by lia. rewrite ro_P1L_13. L5KP.wordE' ZA Hag. }
  rewrite cells_P1L in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PP1L.cells, PP1L.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0. apply Hfr. unfold PP1L.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP1H := LibSegZ_pt1ph.
Definition KS_P1H : list nat := Eval vm_compute in (BG.kept_list 48 PP1H.regs0 PP1H.regs_out).
Lemma KS_P1H_ok : BG.kept_ok 48 PP1H.regs0 PP1H.regs_out KS_P1H = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1H_1 : nth 1 PP1H.regs_out (ELit 0) = ELit 138108. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1H_2 : nth 2 PP1H.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-16)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1H_10 : nth 10 PP1H.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1H_11 : nth 11 PP1H.regs_out (ELit 0) = EVar 11. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1H_12 : nth 12 PP1H.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P1H_13 : nth 13 PP1H.regs_out (ELit 0) = EVar 12. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P1H : SR.ps_cells PP1H.ps0 = PP1H.cells. Proof. reflexivity. Qed.
Definition VAL_P1H (R : bvmap 5 word) (sp : Z) (p : Z) (n : Z) (o : Z) (c : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 10%nat => Z_to_bv 64 p | 11%nat => Z_to_bv 64 n | 12%nat => Z_to_bv 64 o | 40%nat => Z_to_bv 64 c | _ => getr R (reg k) end.
Definition VZ_P1H (R : bvmap 5 word) (sp : Z) (p : Z) (n : Z) (o : Z) (c : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 10%nat => p | 11%nat => n | 12%nat => o | 40%nat => c | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P1H R sp p n o c : 0 <= sp < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P1H R sp p n o c) (fun _ => [])) k) = VZ_P1H R sp p n o c k.
Proof.
  intros. cbn [ev]. unfold VAL_P1H, VZ_P1H.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pt1ph_conc fx R M sp p n o c :
  getr R (reg 2) = Z_to_bv 64 sp ->
  getr R (reg 10) = Z_to_bv 64 p ->
  getr R (reg 11) = Z_to_bv 64 n ->
  getr R (reg 12) = Z_to_bv 64 o ->
  0 <= sp < 2 ^ 64 ->
  0 <= p < 2 ^ 64 ->
  0 <= n < 2 ^ 64 ->
  0 <= o < 2 ^ 64 ->
  0 <= c < 2 ^ 64 ->
  140735332483088 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 16) (16) ->
  1 <= n <= 4999 ->
  4096 <= p <= 140737488355327 ->
  L5.u8_at RSEGS M (p) (c) ->
  46 <= c <= 255 ->
  ((sp) + -16 + (16) <= (p) + 0 \/ (p) + 0 + (1) <= (sp) + -16) ->
  exists fx' R' M', msteps RSEGS (st fx R 138048 M) (st fx' R' 134064 M')
    /\ (forall i, In i KS_P1H -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (138108)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 16)
    /\ getr R' (reg 10) = Z_to_bv 64 (p)
    /\ getr R' (reg 11) = Z_to_bv 64 (n)
    /\ getr R' (reg 12) = Z_to_bv 64 (0)
    /\ getr R' (reg 13) = Z_to_bv 64 (o)
    /\ L5.u64_at RSEGS M' ((sp) - 8) (bv_unsigned (getr R (reg 1)))
    /\ (forall x : word, ~ ((sp) + -16 <= bv_unsigned x < (sp) + -16 + (16)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H10 H11 H12 G2 G10 G11 G12 G40 K1 K2 K3 K4 K5 K6 K7 K8.
  set (Vf := VAL_P1H R sp p n o c). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P1H R sp p n o c k) by (apply VAL_VZ_P1H; lia). unfold VZ_P1H in ZA.
  assert (HR: regs_ok E PP1H.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP1H.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP1H.kn0). { unfold know_ok, PP1H.kn0. kn_allx ZA. }
  destruct (PP1H.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP1H.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP1H.regs0 PP1H.regs_out 48 KS_P1H KS_P1H_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP1H.regs_out E' R' 1 Hregs) by lia. rewrite ro_P1H_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1H.regs_out E' R' 2 Hregs) by lia. rewrite ro_P1H_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1H.regs_out E' R' 10 Hregs) by lia. rewrite ro_P1H_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1H.regs_out E' R' 11 Hregs) by lia. rewrite ro_P1H_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1H.regs_out E' R' 12 Hregs) by lia. rewrite ro_P1H_12. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP1H.regs_out E' R' 13 Hregs) by lia. rewrite ro_P1H_13. L5KP.wordE' ZA Hag. }
  rewrite cells_P1H in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PP1H.cells, PP1H.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0. apply Hfr. unfold PP1H.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PP2 := LibSegZ_pt2.
Definition KS_P2 : list nat := Eval vm_compute in (BG.kept_list 48 PP2.regs0 PP2.regs_out).
Lemma KS_P2_ok : BG.kept_ok 48 PP2.regs0 PP2.regs_out KS_P2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2_1 : nth 1 PP2.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2_2 : nth 2 PP2.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_P2_11 : nth 11 PP2.regs_out (ELit 0) = EVar 11. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P2 : SR.ps_cells PP2.ps0 = PP2.cells. Proof. reflexivity. Qed.
Definition VAL_P2 (R : bvmap 5 word) (sp : Z) (ec : Z) (c1 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 11%nat => Z_to_bv 64 ec | 41%nat => Z_to_bv 64 c1 | _ => getr R (reg k) end.
Definition VZ_P2 (R : bvmap 5 word) (sp : Z) (ec : Z) (c1 : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 11%nat => ec | 41%nat => c1 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_P2 R sp ec c1 : 0 <= sp < 2 ^ 64 -> 0 <= ec < 2 ^ 64 -> 0 <= c1 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_P2 R sp ec c1) (fun _ => [])) k) = VZ_P2 R sp ec c1 k.
Proof.
  intros. cbn [ev]. unfold VAL_P2, VZ_P2.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma pt2_conc fx R M sp ec c1 :
  getr R (reg 2) = Z_to_bv 64 (sp - 16) ->
  getr R (reg 11) = Z_to_bv 64 ec ->
  0 <= sp < 2 ^ 64 ->
  0 <= ec < 2 ^ 64 ->
  0 <= c1 < 2 ^ 64 ->
  140735332483088 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.u64_at RSEGS M ((sp) - 8) (c1) ->
  0 <= ec <= 22 ->
  exists fx' R' M', msteps RSEGS (st fx R 138108 M) (st fx' R' 138124 M')
    /\ (forall i, In i KS_P2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (c1)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp)
    /\ getr R' (reg 11) = Z_to_bv 64 (ec)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H11 G2 G11 G41 K1 K2 K3 K4.
  set (Vf := VAL_P2 R sp ec c1). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_P2 R sp ec c1 k) by (apply VAL_VZ_P2; lia). unfold VZ_P2 in ZA.
  assert (HR: regs_ok E PP2.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP2.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PP2.kn0). { unfold know_ok, PP2.kn0. kn_allx ZA. }
  destruct (PP2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PP2.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP2.regs0 PP2.regs_out 48 KS_P2 KS_P2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP2.regs_out E' R' 1 Hregs) by lia. rewrite ro_P2_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2.regs_out E' R' 2 Hregs) by lia. rewrite ro_P2_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PP2.regs_out E' R' 11 Hregs) by lia. rewrite ro_P2_11. L5KP.wordE' ZA Hag. }
  rewrite cells_P2 in Hcells.
  split. { intros x. apply Hfr. unfold PP2.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PQ0 := LibSegZ_qt0.
Definition KS_Q0 : list nat := Eval vm_compute in (BG.kept_list 48 PQ0.regs0 PQ0.regs_out).
Lemma KS_Q0_ok : BG.kept_ok 48 PQ0.regs0 PQ0.regs_out KS_Q0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q0_1 : nth 1 PQ0.regs_out (ELit 0) = EVar 1. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q0_2 : nth 2 PQ0.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q0_11 : nth 11 PQ0.regs_out (ELit 0) = ELit 22. Proof. vm_compute. reflexivity. Qed.
Lemma cells_Q0 : SR.ps_cells PQ0.ps0 = PQ0.cells. Proof. reflexivity. Qed.
Definition VAL_Q0 (R : bvmap 5 word) (sp : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | _ => getr R (reg k) end.
Definition VZ_Q0 (R : bvmap 5 word) (sp : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_Q0 R sp : 0 <= sp < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_Q0 R sp) (fun _ => [])) k) = VZ_Q0 R sp k.
Proof.
  intros. cbn [ev]. unfold VAL_Q0, VZ_Q0.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma qt0_conc fx R M sp :
  getr R (reg 2) = Z_to_bv 64 sp ->
  getr R (reg 11) = Z_to_bv 64 (0) ->
  0 <= sp < 2 ^ 64 ->
  140735332483088 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  exists fx' R' M', msteps RSEGS (st fx R 133980 M) (st fx' R' 134052 M')
    /\ (forall i, In i KS_Q0 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = getr R (reg 1)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp)
    /\ getr R' (reg 11) = Z_to_bv 64 (22)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H11 G2 K1 K2.
  set (Vf := VAL_Q0 R sp). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_Q0 R sp k) by (apply VAL_VZ_Q0; lia). unfold VZ_Q0 in ZA.
  assert (HR: regs_ok E PQ0.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PQ0.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PQ0.kn0). { unfold know_ok, PQ0.kn0. kn_allx ZA. }
  destruct (PQ0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PQ0.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PQ0.regs0 PQ0.regs_out 48 KS_Q0 KS_Q0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PQ0.regs_out E' R' 1 Hregs) by lia. rewrite ro_Q0_1. cbn [edenot]. rewrite <- (proj1 Hag 1%nat) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PQ0.regs_out E' R' 2 Hregs) by lia. rewrite ro_Q0_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ0.regs_out E' R' 11 Hregs) by lia. rewrite ro_Q0_11. L5KP.wordE' ZA Hag. }
  rewrite cells_Q0 in Hcells.
  split. { intros x. apply Hfr. unfold PQ0.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PQ1M := LibSegZ_qt1m.
Definition KS_Q1M : list nat := Eval vm_compute in (BG.kept_list 48 PQ1M.regs0 PQ1M.regs_out).
Lemma KS_Q1M_ok : BG.kept_ok 48 PQ1M.regs0 PQ1M.regs_out KS_Q1M = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1M_1 : nth 1 PQ1M.regs_out (ELit 0) = ELit 134036. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1M_2 : nth 2 PQ1M.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-16)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1M_10 : nth 10 PQ1M.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 10) (ELit 1). Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1M_11 : nth 11 PQ1M.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 11) (ELit (-1)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1M_12 : nth 12 PQ1M.regs_out (ELit 0) = ELit 1. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1M_13 : nth 13 PQ1M.regs_out (ELit 0) = EVar 12. Proof. vm_compute. reflexivity. Qed.
Lemma cells_Q1M : SR.ps_cells PQ1M.ps0 = PQ1M.cells. Proof. reflexivity. Qed.
Definition VAL_Q1M (R : bvmap 5 word) (sp : Z) (p : Z) (n : Z) (o : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 10%nat => Z_to_bv 64 p | 11%nat => Z_to_bv 64 n | 12%nat => Z_to_bv 64 o | _ => getr R (reg k) end.
Definition VZ_Q1M (R : bvmap 5 word) (sp : Z) (p : Z) (n : Z) (o : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 10%nat => p | 11%nat => n | 12%nat => o | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_Q1M R sp p n o : 0 <= sp < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_Q1M R sp p n o) (fun _ => [])) k) = VZ_Q1M R sp p n o k.
Proof.
  intros. cbn [ev]. unfold VAL_Q1M, VZ_Q1M.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma qt1m_conc fx R M sp p n o :
  getr R (reg 2) = Z_to_bv 64 sp ->
  getr R (reg 10) = Z_to_bv 64 p ->
  getr R (reg 11) = Z_to_bv 64 n ->
  getr R (reg 12) = Z_to_bv 64 o ->
  0 <= sp < 2 ^ 64 ->
  0 <= p < 2 ^ 64 ->
  0 <= n < 2 ^ 64 ->
  0 <= o < 2 ^ 64 ->
  140735332483088 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 16) (16) ->
  1 <= n <= 4999 ->
  4096 <= p <= 140737488355327 ->
  L5.u8_at RSEGS M (p) (45) ->
  ((sp) + -16 + (16) <= (p) + 0 \/ (p) + 0 + (1) <= (sp) + -16) ->
  exists fx' R' M', msteps RSEGS (st fx R 133980 M) (st fx' R' 134064 M')
    /\ (forall i, In i KS_Q1M -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (134036)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 16)
    /\ getr R' (reg 10) = Z_to_bv 64 (p + 1)
    /\ getr R' (reg 11) = Z_to_bv 64 (n - 1)
    /\ getr R' (reg 12) = Z_to_bv 64 (1)
    /\ getr R' (reg 13) = Z_to_bv 64 (o)
    /\ L5.u64_at RSEGS M' ((sp) - 8) (bv_unsigned (getr R (reg 1)))
    /\ (forall x : word, ~ ((sp) + -16 <= bv_unsigned x < (sp) + -16 + (16)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H10 H11 H12 G2 G10 G11 G12 K1 K2 K3 K4 K5 K6 K7.
  set (Vf := VAL_Q1M R sp p n o). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_Q1M R sp p n o k) by (apply VAL_VZ_Q1M; lia). unfold VZ_Q1M in ZA.
  assert (HR: regs_ok E PQ1M.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PQ1M.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PQ1M.kn0). { unfold know_ok, PQ1M.kn0. kn_allx ZA. }
  destruct (PQ1M.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PQ1M.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PQ1M.regs0 PQ1M.regs_out 48 KS_Q1M KS_Q1M_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PQ1M.regs_out E' R' 1 Hregs) by lia. rewrite ro_Q1M_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1M.regs_out E' R' 2 Hregs) by lia. rewrite ro_Q1M_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1M.regs_out E' R' 10 Hregs) by lia. rewrite ro_Q1M_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1M.regs_out E' R' 11 Hregs) by lia. rewrite ro_Q1M_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1M.regs_out E' R' 12 Hregs) by lia. rewrite ro_Q1M_12. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1M.regs_out E' R' 13 Hregs) by lia. rewrite ro_Q1M_13. L5KP.wordE' ZA Hag. }
  rewrite cells_Q1M in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PQ1M.cells, PQ1M.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0. apply Hfr. unfold PQ1M.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PQ1L := LibSegZ_qt1pl.
Definition KS_Q1L : list nat := Eval vm_compute in (BG.kept_list 48 PQ1L.regs0 PQ1L.regs_out).
Lemma KS_Q1L_ok : BG.kept_ok 48 PQ1L.regs0 PQ1L.regs_out KS_Q1L = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1L_1 : nth 1 PQ1L.regs_out (ELit 0) = ELit 134036. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1L_2 : nth 2 PQ1L.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-16)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1L_10 : nth 10 PQ1L.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1L_11 : nth 11 PQ1L.regs_out (ELit 0) = EVar 11. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1L_12 : nth 12 PQ1L.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1L_13 : nth 13 PQ1L.regs_out (ELit 0) = EVar 12. Proof. vm_compute. reflexivity. Qed.
Lemma cells_Q1L : SR.ps_cells PQ1L.ps0 = PQ1L.cells. Proof. reflexivity. Qed.
Definition VAL_Q1L (R : bvmap 5 word) (sp : Z) (p : Z) (n : Z) (o : Z) (c : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 10%nat => Z_to_bv 64 p | 11%nat => Z_to_bv 64 n | 12%nat => Z_to_bv 64 o | 40%nat => Z_to_bv 64 c | _ => getr R (reg k) end.
Definition VZ_Q1L (R : bvmap 5 word) (sp : Z) (p : Z) (n : Z) (o : Z) (c : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 10%nat => p | 11%nat => n | 12%nat => o | 40%nat => c | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_Q1L R sp p n o c : 0 <= sp < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_Q1L R sp p n o c) (fun _ => [])) k) = VZ_Q1L R sp p n o c k.
Proof.
  intros. cbn [ev]. unfold VAL_Q1L, VZ_Q1L.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma qt1pl_conc fx R M sp p n o c :
  getr R (reg 2) = Z_to_bv 64 sp ->
  getr R (reg 10) = Z_to_bv 64 p ->
  getr R (reg 11) = Z_to_bv 64 n ->
  getr R (reg 12) = Z_to_bv 64 o ->
  0 <= sp < 2 ^ 64 ->
  0 <= p < 2 ^ 64 ->
  0 <= n < 2 ^ 64 ->
  0 <= o < 2 ^ 64 ->
  0 <= c < 2 ^ 64 ->
  140735332483088 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 16) (16) ->
  1 <= n <= 4999 ->
  4096 <= p <= 140737488355327 ->
  L5.u8_at RSEGS M (p) (c) ->
  0 <= c <= 44 ->
  ((sp) + -16 + (16) <= (p) + 0 \/ (p) + 0 + (1) <= (sp) + -16) ->
  exists fx' R' M', msteps RSEGS (st fx R 133980 M) (st fx' R' 134064 M')
    /\ (forall i, In i KS_Q1L -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (134036)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 16)
    /\ getr R' (reg 10) = Z_to_bv 64 (p)
    /\ getr R' (reg 11) = Z_to_bv 64 (n)
    /\ getr R' (reg 12) = Z_to_bv 64 (0)
    /\ getr R' (reg 13) = Z_to_bv 64 (o)
    /\ L5.u64_at RSEGS M' ((sp) - 8) (bv_unsigned (getr R (reg 1)))
    /\ (forall x : word, ~ ((sp) + -16 <= bv_unsigned x < (sp) + -16 + (16)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H10 H11 H12 G2 G10 G11 G12 G40 K1 K2 K3 K4 K5 K6 K7 K8.
  set (Vf := VAL_Q1L R sp p n o c). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_Q1L R sp p n o c k) by (apply VAL_VZ_Q1L; lia). unfold VZ_Q1L in ZA.
  assert (HR: regs_ok E PQ1L.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PQ1L.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PQ1L.kn0). { unfold know_ok, PQ1L.kn0. kn_allx ZA. }
  destruct (PQ1L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PQ1L.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PQ1L.regs0 PQ1L.regs_out 48 KS_Q1L KS_Q1L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PQ1L.regs_out E' R' 1 Hregs) by lia. rewrite ro_Q1L_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1L.regs_out E' R' 2 Hregs) by lia. rewrite ro_Q1L_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1L.regs_out E' R' 10 Hregs) by lia. rewrite ro_Q1L_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1L.regs_out E' R' 11 Hregs) by lia. rewrite ro_Q1L_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1L.regs_out E' R' 12 Hregs) by lia. rewrite ro_Q1L_12. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1L.regs_out E' R' 13 Hregs) by lia. rewrite ro_Q1L_13. L5KP.wordE' ZA Hag. }
  rewrite cells_Q1L in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PQ1L.cells, PQ1L.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0. apply Hfr. unfold PQ1L.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PQ1H := LibSegZ_qt1ph.
Definition KS_Q1H : list nat := Eval vm_compute in (BG.kept_list 48 PQ1H.regs0 PQ1H.regs_out).
Lemma KS_Q1H_ok : BG.kept_ok 48 PQ1H.regs0 PQ1H.regs_out KS_Q1H = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1H_1 : nth 1 PQ1H.regs_out (ELit 0) = ELit 134036. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1H_2 : nth 2 PQ1H.regs_out (ELit 0) = EAlu Instr.ALU_ADD (EVar 2) (ELit (-16)). Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1H_10 : nth 10 PQ1H.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1H_11 : nth 11 PQ1H.regs_out (ELit 0) = EVar 11. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1H_12 : nth 12 PQ1H.regs_out (ELit 0) = ELit 0. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q1H_13 : nth 13 PQ1H.regs_out (ELit 0) = EVar 12. Proof. vm_compute. reflexivity. Qed.
Lemma cells_Q1H : SR.ps_cells PQ1H.ps0 = PQ1H.cells. Proof. reflexivity. Qed.
Definition VAL_Q1H (R : bvmap 5 word) (sp : Z) (p : Z) (n : Z) (o : Z) (c : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 10%nat => Z_to_bv 64 p | 11%nat => Z_to_bv 64 n | 12%nat => Z_to_bv 64 o | 40%nat => Z_to_bv 64 c | _ => getr R (reg k) end.
Definition VZ_Q1H (R : bvmap 5 word) (sp : Z) (p : Z) (n : Z) (o : Z) (c : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 10%nat => p | 11%nat => n | 12%nat => o | 40%nat => c | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_Q1H R sp p n o c : 0 <= sp < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_Q1H R sp p n o c) (fun _ => [])) k) = VZ_Q1H R sp p n o c k.
Proof.
  intros. cbn [ev]. unfold VAL_Q1H, VZ_Q1H.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma qt1ph_conc fx R M sp p n o c :
  getr R (reg 2) = Z_to_bv 64 sp ->
  getr R (reg 10) = Z_to_bv 64 p ->
  getr R (reg 11) = Z_to_bv 64 n ->
  getr R (reg 12) = Z_to_bv 64 o ->
  0 <= sp < 2 ^ 64 ->
  0 <= p < 2 ^ 64 ->
  0 <= n < 2 ^ 64 ->
  0 <= o < 2 ^ 64 ->
  0 <= c < 2 ^ 64 ->
  140735332483088 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.writable RSEGS M ((sp) - 16) (16) ->
  1 <= n <= 4999 ->
  4096 <= p <= 140737488355327 ->
  L5.u8_at RSEGS M (p) (c) ->
  46 <= c <= 255 ->
  ((sp) + -16 + (16) <= (p) + 0 \/ (p) + 0 + (1) <= (sp) + -16) ->
  exists fx' R' M', msteps RSEGS (st fx R 133980 M) (st fx' R' 134064 M')
    /\ (forall i, In i KS_Q1H -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (134036)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 16)
    /\ getr R' (reg 10) = Z_to_bv 64 (p)
    /\ getr R' (reg 11) = Z_to_bv 64 (n)
    /\ getr R' (reg 12) = Z_to_bv 64 (0)
    /\ getr R' (reg 13) = Z_to_bv 64 (o)
    /\ L5.u64_at RSEGS M' ((sp) - 8) (bv_unsigned (getr R (reg 1)))
    /\ (forall x : word, ~ ((sp) + -16 <= bv_unsigned x < (sp) + -16 + (16)) -> M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H10 H11 H12 G2 G10 G11 G12 G40 K1 K2 K3 K4 K5 K6 K7 K8.
  set (Vf := VAL_Q1H R sp p n o c). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_Q1H R sp p n o c k) by (apply VAL_VZ_Q1H; lia). unfold VZ_Q1H in ZA.
  assert (HR: regs_ok E PQ1H.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PQ1H.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PQ1H.kn0). { unfold know_ok, PQ1H.kn0. kn_allx ZA. }
  destruct (PQ1H.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PQ1H.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PQ1H.regs0 PQ1H.regs_out 48 KS_Q1H KS_Q1H_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PQ1H.regs_out E' R' 1 Hregs) by lia. rewrite ro_Q1H_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1H.regs_out E' R' 2 Hregs) by lia. rewrite ro_Q1H_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1H.regs_out E' R' 10 Hregs) by lia. rewrite ro_Q1H_10. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1H.regs_out E' R' 11 Hregs) by lia. rewrite ro_Q1H_11. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1H.regs_out E' R' 12 Hregs) by lia. rewrite ro_Q1H_12. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ1H.regs_out E' R' 13 Hregs) by lia. rewrite ro_Q1H_13. L5KP.wordE' ZA Hag. }
  rewrite cells_Q1H in Hcells.
  split. { eapply L5KP.u64_of_KWord8. apply Hcells. unfold PQ1H.cells, PQ1H.cells0. left; reflexivity. L5KP.evalE' ZA Hag. L5KP.evalE' ZA Hag. }
  split. { intros x Hy0. apply Hfr. unfold PQ1H.F0. L5KP.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Module PQ2 := LibSegZ_qt2.
Definition KS_Q2 : list nat := Eval vm_compute in (BG.kept_list 48 PQ2.regs0 PQ2.regs_out).
Lemma KS_Q2_ok : BG.kept_ok 48 PQ2.regs0 PQ2.regs_out KS_Q2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q2_1 : nth 1 PQ2.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q2_2 : nth 2 PQ2.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma ro_Q2_11 : nth 11 PQ2.regs_out (ELit 0) = EVar 11. Proof. vm_compute. reflexivity. Qed.
Lemma cells_Q2 : SR.ps_cells PQ2.ps0 = PQ2.cells. Proof. reflexivity. Qed.
Definition VAL_Q2 (R : bvmap 5 word) (sp : Z) (ec : Z) (c1 : Z) (k : nat) : word :=
  match k with | 2%nat => Z_to_bv 64 sp | 11%nat => Z_to_bv 64 ec | 41%nat => Z_to_bv 64 c1 | _ => getr R (reg k) end.
Definition VZ_Q2 (R : bvmap 5 word) (sp : Z) (ec : Z) (c1 : Z) (k : nat) : Z :=
  match k with | 2%nat => sp | 11%nat => ec | 41%nat => c1 | _ => bv_unsigned (getr R (reg k)) end.
Lemma VAL_VZ_Q2 R sp ec c1 : 0 <= sp < 2 ^ 64 -> 0 <= ec < 2 ^ 64 -> 0 <= c1 < 2 ^ 64 ->
  forall k, bv_unsigned (ev (Env (VAL_Q2 R sp ec c1) (fun _ => [])) k) = VZ_Q2 R sp ec c1 k.
Proof.
  intros. cbn [ev]. unfold VAL_Q2, VZ_Q2.
  repeat (lazymatch goal with |- bv_unsigned (match ?k with _ => _ end) = _ => destruct k as [|k] | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.
Lemma qt2_conc fx R M sp ec c1 :
  getr R (reg 2) = Z_to_bv 64 (sp - 16) ->
  getr R (reg 11) = Z_to_bv 64 ec ->
  0 <= sp < 2 ^ 64 ->
  0 <= ec < 2 ^ 64 ->
  0 <= c1 < 2 ^ 64 ->
  140735332483088 <= sp <= 140737488355328 ->
  (sp) mod 16 = 0 ->
  L5.u64_at RSEGS M ((sp) - 8) (c1) ->
  0 <= ec <= 22 ->
  exists fx' R' M', msteps RSEGS (st fx R 134036 M) (st fx' R' 134052 M')
    /\ (forall i, In i KS_Q2 -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 1) = Z_to_bv 64 (c1)
    /\ getr R' (reg 2) = Z_to_bv 64 (sp)
    /\ getr R' (reg 11) = Z_to_bv 64 (ec)
    /\ (forall x : word, M' x = M x)
    /\ mem_grows M M'.
Proof.
  intros H2 H11 G2 G11 G41 K1 K2 K3 K4.
  set (Vf := VAL_Q2 R sp ec c1). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ_Q2 R sp ec c1 k) by (apply VAL_VZ_Q2; lia). unfold VZ_Q2 in ZA.
  assert (HR: regs_ok E PQ2.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PQ2.regs0 nth]. repeat split; L5KP.slot ZA. }
  assert (HK: know_ok RSEGS E M PQ2.kn0). { unfold know_ok, PQ2.kn0. kn_allx ZA. }
  destruct (PQ2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5KP.nth_error_single in Hnth. subst ps0. change PQ2.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PQ2.regs0 PQ2.regs_out 48 KS_Q2 KS_Q2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PQ2.regs_out E' R' 1 Hregs) by lia. rewrite ro_Q2_1. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ2.regs_out E' R' 2 Hregs) by lia. rewrite ro_Q2_2. L5KP.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PQ2.regs_out E' R' 11 Hregs) by lia. rewrite ro_Q2_11. L5KP.wordE' ZA Hag. }
  rewrite cells_Q2 in Hcells.
  split. { intros x. apply Hfr. unfold PQ2.F0. apply L5KP.outside_nil_e. } exact Hgr.
Qed.

End L5TB.
