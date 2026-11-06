(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound
     Src0PlanKit BigLinkGlue BigLinkShl L5Defs L5Core.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5KS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition IMG_HI : Z := 0x91000.

Lemma rdn_defined M (a : Z) (w : nat) bs :
  rdn RSEGS M (Z_to_bv 64 a) w = Some bs -> IMG_HI <= a -> a + Z.of_nat w <= 2 ^ 64 -> L5.defined M a (Z.of_nat w).
Proof.
  intros Hr Hlo Hhi i Hi. unfold IMG_HI in Hlo.
  apply (APS.rdn_bytes_some RSEGS A0 src0_in_hull M (Z_to_bv 64 a) w bs Hr).
  - rewrite !BG.unsigned_lit by lia. lia.
  - unfold APS.in_hull. cbn [APC.img_lo APC.img_hi A0]. rewrite BG.unsigned_lit by lia.
    apply Bool.andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

Lemma u64_at_defined M a v : BG.u64_at M a v -> IMG_HI <= a -> a + 8 <= 2 ^ 64 -> L5.defined M a 8.
Proof. intros Hu Hlo Hhi. exact (rdn_defined M a 8%nat _ Hu Hlo Hhi). Qed.

(* [comment removed for export] *)
Definition IMG_LO : Z := 0x10000.
Lemma hull_lo_eq : L5.hull_lo RSEGS = IMG_LO. Proof. vm_compute. reflexivity. Qed.
Lemma hull_hi_eq : L5.hull_hi RSEGS = IMG_HI. Proof. vm_compute. reflexivity. Qed.
Lemma hull_apart_iff a n : L5.hull_apart RSEGS a n <-> (a + n <= 0x10000 \/ 0x91000 <= a).
Proof. unfold L5.hull_apart. rewrite hull_lo_eq, hull_hi_eq. unfold IMG_LO, IMG_HI. tauto. Qed.
Lemma hull_apart_of a n : (a + n <= 0x10000 \/ 0x91000 <= a) -> L5.hull_apart RSEGS a n.
Proof. apply hull_apart_iff. Qed.
Lemma hull_apart_lit a n : L5.hull_apart RSEGS a n -> (a + n <= 0x10000 \/ 0x91000 <= a).
Proof. apply hull_apart_iff. Qed.

Lemma rdn_defined2 M (a : Z) (w : nat) bs :
  rdn RSEGS M (Z_to_bv 64 a) w = Some bs -> 0 <= a -> (a + Z.of_nat w <= 0x10000 \/ 0x91000 <= a) -> a + Z.of_nat w <= 2 ^ 64 ->
  L5.defined M a (Z.of_nat w).
Proof.
  intros Hr Ha Hap Hhi i Hi.
  apply (APS.rdn_bytes_some RSEGS A0 src0_in_hull M (Z_to_bv 64 a) w bs Hr).
  - rewrite !BG.unsigned_lit by lia. lia.
  - unfold APS.in_hull. cbn [APC.img_lo APC.img_hi A0]. rewrite BG.unsigned_lit by lia.
    destruct Hap as [Hb|Hb].
    + apply Bool.andb_false_iff. left. apply Z.leb_gt. lia.
    + apply Bool.andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
Lemma u64_at_defined2 M a v : BG.u64_at M a v -> 0 <= a -> (a + 8 <= 0x10000 \/ 0x91000 <= a) -> a + 8 <= 2 ^ 64 -> L5.defined M a 8.
Proof. intros Hu Ha Hap Hhi. exact (rdn_defined2 M a 8%nat _ Hu Ha Hap Hhi). Qed.
Lemma u64_at_defined_hull M a v : BG.u64_at M a v -> 0 <= a -> L5.hull_apart RSEGS a 8 -> a + 8 <= 2 ^ 64 -> L5.defined M a 8.
Proof. intros Hu Ha Hap Hhi. apply hull_apart_lit in Hap. exact (rdn_defined2 M a 8%nat _ Hu Ha Hap Hhi). Qed.

(* [comment removed for export] *)
Lemma limbs_at_defined_hull M q ws : L5.limbs_at RSEGS M q ws -> 0 <= q -> L5.hull_apart RSEGS q (8 * Z.of_nat (length ws)) ->
  q + 8 * Z.of_nat (length ws) <= 2 ^ 64 -> L5.defined M q (8 * Z.of_nat (length ws)).
Proof.
  intros HL Hq Hap Hhi i Hi. apply hull_apart_lit in Hap.
  pose proof (Z.div_mod i 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as MB.
  assert (Hk: (Z.to_nat (i / 8) < length ws)%nat). { apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia). apply Z.div_lt_upper_bound; lia. }
  pose proof (HL (Z.to_nat (i / 8)) Hk) as U. rewrite Z2Nat.id in U by (apply Z.div_pos; lia).
  pose proof (Z.mul_div_le i 8 ltac:(lia)) as ML.
  pose proof (u64_at_defined2 M _ _ U ltac:(apply Z.add_nonneg_nonneg; [lia|apply Z.mul_nonneg_nonneg; [lia|apply Z.div_pos; lia]]) ltac:(lia) ltac:(lia)) as D.
  specialize (D (i mod 8) ltac:(lia)). replace (q + 8 * (i / 8) + i mod 8) with (q + i) in D by lia. exact D.
Qed.
Lemma u8_at_defined M a b : BG.u8_at M a b -> IMG_HI <= a -> a + 1 <= 2 ^ 64 -> L5.defined M a 1.
Proof. intros Hu Hlo Hhi. exact (rdn_defined M a 1%nat _ Hu Hlo Hhi). Qed.

(* [comment removed for export] *)
Lemma limbs_at_defined M q ws : L5.limbs_at RSEGS M q ws -> IMG_HI <= q -> q + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  L5.defined M q (8 * Z.of_nat (length ws)).
Proof.
  intros HL Hlo Hhi i Hi. unfold IMG_HI in Hlo.
  pose proof (Z.div_mod i 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as MB.
  assert (Hk: (Z.to_nat (i / 8) < length ws)%nat). { apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia). apply Z.div_lt_upper_bound; lia. }
  pose proof (HL (Z.to_nat (i / 8)) Hk) as U. rewrite Z2Nat.id in U by (apply Z.div_pos; lia).
  pose proof (u64_at_defined M _ _ U ltac:(unfold IMG_HI; lia) ltac:(pose proof (Z.mul_div_le i 8); lia)) as D.
  specialize (D (i mod 8) ltac:(lia)). replace (q + 8 * (i / 8) + i mod 8) with (q + i) in D by lia. exact D.
Qed.

(* [comment removed for export] *)
Lemma limbs_of_defined M q : forall (k : nat), L5.defined M q (8 * Z.of_nat k) -> 0 <= q -> q + 8 * Z.of_nat k <= 2 ^ 64 ->
  exists ws, length ws = k /\ Forall (fun w => 0 <= w < 2 ^ 64) ws /\ L5.limbs_at RSEGS M q ws.
Proof.
  induction k as [|k IH]; intros D Hq Hk.
  - exists []. split. reflexivity. split. constructor. apply L5C.limbs_at_nil.
  - destruct (IH ltac:(eapply L5.defined_sub; [exact D|lia|lia]) Hq ltac:(lia)) as (ws & L & R & LA).
    destruct (BSHL.defined_word M (q + 8 * Z.of_nat k) ltac:(eapply L5.defined_sub; [exact D|lia|lia]) ltac:(lia) ltac:(lia)) as (w & Rw & Uw).
    exists (ws ++ [w]). split. rewrite length_app; cbn; lia. split. apply Forall_app; split; [exact R|constructor; [lia|constructor]].
    apply L5C.limbs_at_app. exact LA. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth]. rewrite L.
    replace (q + 8 * Z.of_nat k + 8 * Z.of_nat 0) with (q + 8 * Z.of_nat k) by lia. exact Uw.
Qed.

(* [comment removed for export] *)
Lemma header_writable M o fb (x8 x16 x24 : Z) :
  BG.u8_at M o fb -> L5.defined M (o + 1) 7 -> BG.u64_at M (o + 8) x8 -> BG.u64_at M (o + 16) x16 -> BG.u64_at M (o + 24) x24 ->
  IMG_HI <= o -> o + 32 <= 2 ^ 64 -> L5.writable RSEGS M o 32.
Proof.
  intros H0 D1 H8 H16 H24 Hlo Hhi. apply L5C.writable_of_defined; [|unfold IMG_HI in Hlo; lia|lia].
  replace 32 with (1 + (7 + (8 + (8 + 8)))) by lia.
  apply L5C.defined_app; [eapply u8_at_defined; eauto; lia| |lia].
  apply L5C.defined_app; [exact D1| |lia].
  replace (o + 1 + 7) with (o + 8) by lia.
  apply L5C.defined_app; [eapply u64_at_defined; eauto; lia| |lia].
  replace (o + 8 + 8) with (o + 16) by lia.
  apply L5C.defined_app; [eapply u64_at_defined; eauto; lia| |lia].
  replace (o + 16 + 8) with (o + 24) by lia. eapply u64_at_defined; eauto; lia.
Qed.
End L5KS.
