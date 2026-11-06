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
     Src0_code_22348_22f60 BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkDq BigLinkReduce L5Defs L5Kn L5Core L5Words L5Reduce L5ReduceG.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5Shr.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5SHR.
Import L5W.
Abbreviation RSEGS := Plain.M.loaded_segments.
Module PAi := LibSegZ_srAi. Module PAd := LibSegZ_srAd. Module PI := LibSegZ_srI. Module PL := LibSegZ_srL. Module PE := LibSegZ_srE.
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition SHR : Z := 0x22b98.
Definition LHEAD : Z := 0x22c40. Definition AFTER_REDUCE : Z := 0x22c74. Definition RET : Z := 0x22ca0.
Definition FRAME : Z := 48.
End SCFG_1.


Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Section SCFG_2.
Context {SCFG_P : ScfgP}.

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shr_post (M M' : word -> option byte) (R R' : bvmap 5 word) (o sp : Z) (b : L5.bigobj) (rw : list Z) (st' : L5.bstore) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 o /\
  length rw = L5.bo_len b /\ words_ok rw /\
  let n' := rlen rw in
  let fb' := if Nat.eqb n' 0 then Z.land (L5.bo_fb b) 253 else L5.bo_fb b in
  L5.big_at RSEGS M' o (L5.BO fb' n' st') /\ L5.limbs_at RSEGS M' (L5.bo_data o b) rw /\
  match L5.bo_st b, st' with
  | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
  | L5.BInl _ _, L5.BInl _ _ => True
  | _, _ => False end /\
  (forall a : word, ~ (sp - 48 <= bv_unsigned a < sp) -> ~ (o <= bv_unsigned a < o + 16) ->
                     ~ (L5.bo_data o b <= bv_unsigned a < L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b)) -> M' a = M a) /\
  mem_grows M M'.

Definition shr_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (o sp r k : Z) (b : L5.bigobj) (ws : list Z),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 k -> 1 <= k <= 63 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 sp ->
    sp mod 16 = 0 -> 2 ^ 24 <= sp -> sp <= o -> o + 32 <= 2 ^ 47 -> o mod 8 = 0 ->
    L5.defined M (sp - 48) 48 -> L5.defined M o 32 ->
    L5.big_at RSEGS M o b -> (1 <= L5.bo_len b <= 300)%nat ->
    L5.limbs_at RSEGS M (L5.bo_data o b) ws -> length ws = L5.bo_len b -> words_ok ws ->
    L5.defined M (L5.bo_data o b) (8 * L5.bo_cap b) ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> q + 8 * cap <= sp - 48) ->
    (forall (fx' : FPState) R' M' rw st', shr_post M M' R R' o sp b rw st' -> srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model) K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx) R SHR M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_22b68 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R 0x22ca0 M) (st fx R r M).
Proof. intros H1 Hr He. apply (BRED.ret_to fx R M 0x22ca0 W_22ca0 r F_22ca0 eq_refl D_22ca0 H1 Hr He). Qed.
Lemma word_self (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. apply BG.word_of_unsigned. reflexivity. Qed.
Lemma word_range (w : word) : 0 <= bv_unsigned w < 2 ^ 64. Proof. apply (BL.bvu_range w). Qed.
Lemma writable_of_defined M a n : L5.defined M a n -> 0 <= a -> a + n <= 2 ^ 64 -> L5.writable RSEGS M a n.
Proof. apply (L5C.writable_of_defined RSEGS). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition U (R : bvmap 5 word) (j : nat) : Z := bv_unsigned (getr R (reg j)).
Definition VAL (R0 R : bvmap 5 word) (sp o k n fb d i w v1 : Z) (j : nat) : word :=
  match j with
  | 2%nat => Z_to_bv 64 sp
  | 33%nat => Z_to_bv 64 o | 34%nat => Z_to_bv 64 k | 35%nat => Z_to_bv 64 n | 36%nat => Z_to_bv 64 fb | 37%nat => Z_to_bv 64 d
  | 39%nat => Z_to_bv 64 i | 40%nat => Z_to_bv 64 w | 41%nat => Z_to_bv 64 v1 | 42%nat => getr R (reg 1)
  | 43%nat => getr R0 (reg 1) | 44%nat => getr R0 (reg 8) | 47%nat => getr R0 (reg 9) | 38%nat => getr R0 (reg 18) | 32%nat => getr R0 (reg 19)
  | 45%nat => Z_to_bv 64 (64 - k)
  | _ => getr R (reg j)
  end.
Definition VZ (R0 R : bvmap 5 word) (sp o k n fb d i w v1 : Z) (j : nat) : Z :=
  match j with
  | 2%nat => sp
  | 33%nat => o | 34%nat => k | 35%nat => n | 36%nat => fb | 37%nat => d | 39%nat => i | 40%nat => w | 41%nat => v1 | 42%nat => U R 1
  | 43%nat => U R0 1 | 44%nat => U R0 8 | 47%nat => U R0 9 | 38%nat => U R0 18 | 32%nat => U R0 19
  | 45%nat => 64 - k
  | _ => U R j
  end.
Lemma VAL_VZ R0 R sp o k n fb d i w v1 :
  0 <= sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= k <= 64 -> 0 <= n < 2 ^ 62 -> 0 <= fb < 256 -> 0 <= d < 2 ^ 64 -> 0 <= i < 2 ^ 62 ->
  0 <= w < 2 ^ 64 -> 0 <= v1 < 2 ^ 64 ->
  forall j, bv_unsigned (ev (Env (VAL R0 R sp o k n fb d i w v1) (fun _ => [])) j) = VZ R0 R sp o k n fb d i w v1 j.
Proof.
  intros until j. cbn [ev]. unfold VAL, VZ, U.
  repeat (lazymatch goal with
          | |- bv_unsigned (match j with _ => _ end) = _ => destruct j as [|j]
          | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.

Definition saved (M : word -> option byte) (sp : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (U R0 1) /\ L5.u64_at RSEGS M (sp - 16) (U R0 8) /\ L5.u64_at RSEGS M (sp - 24) (U R0 9) /\
  L5.u64_at RSEGS M (sp - 32) (U R0 18) /\ L5.u64_at RSEGS M (sp - 40) (U R0 19).
Definition spok (sp : Z) : Prop := sp mod 16 = 0 /\ 1048624 <= sp <= 140737488355328.
Definition at_ret (R0 R' : bvmap 5 word) (sp o : Z) : Prop :=
  getr R' (reg 1) = getr R0 (reg 1) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = getr R0 (reg 8) /\ getr R' (reg 9) = getr R0 (reg 9) /\
  getr R' (reg 18) = getr R0 (reg 18) /\ getr R' (reg 19) = getr R0 (reg 19) /\ getr R' (reg 10) = Z_to_bv 64 o.
(* [comment removed for export] *)
Definition at_head (R : bvmap 5 word) (sp o k d : Z) (n i : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 48) /\ getr R (reg 8) = Z_to_bv 64 o /\ getr R (reg 9) = Z_to_bv 64 k /\
  getr R (reg 10) = Z_to_bv 64 (Z.of_nat i) /\ getr R (reg 11) = Z_to_bv 64 (Z.of_nat n) /\ getr R (reg 12) = Z_to_bv 64 (Z.of_nat n - 1) /\
  getr R (reg 13) = Z_to_bv 64 (64 - k) /\ getr R (reg 19) = Z_to_bv 64 (d + 8 * Z.of_nat i).
Definition at_reduce (R : bvmap 5 word) (sp o : Z) : Prop :=
  getr R (reg 1) = Z_to_bv 64 AFTER_REDUCE /\ getr R (reg 2) = Z_to_bv 64 (sp - 48) /\ getr R (reg 8) = Z_to_bv 64 o /\ getr R (reg 10) = Z_to_bv 64 o.
Definition cs_pass : list nat := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KSA : list nat := Eval vm_compute in (BG.kept_list 48 PAi.regs0 PAi.regs_out0).
Lemma KSAi_ok : BG.kept_ok 48 PAi.regs0 PAi.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSAd_ok : BG.kept_ok 48 PAd.regs0 PAd.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.
Definition KSI : list nat := Eval vm_compute in (BG.kept_list 48 PI.regs0 PI.regs_out0).
Lemma KSI_ok : BG.kept_ok 48 PI.regs0 PI.regs_out0 KSI = true. Proof. vm_compute. reflexivity. Qed.
Definition KSL : list nat := Eval vm_compute in (BG.kept_list 48 PL.regs0 PL.regs_out0).
Lemma KSL_ok : BG.kept_ok 48 PL.regs0 PL.regs_out0 KSL = true. Proof. vm_compute. reflexivity. Qed.
Definition KSE : list nat := Eval vm_compute in (BG.kept_list 48 PE.regs0 PE.regs_out0).
Lemma KSE_ok : BG.kept_ok 48 PE.regs0 PE.regs_out0 KSE = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition KSLOOP : list nat := [2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srAi_conc fx R M (sp o k n fb v1 : Z) :
  spok sp -> L5.writable RSEGS M (sp - 48) 48 -> sp <= o -> o + 32 <= 2 ^ 47 -> o mod 8 = 0 ->
  L5.u8_at RSEGS M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = false -> L5.u64_at RSEGS M (o + 8) n -> 1 <= n <= 300 -> 1 <= k <= 63 ->
  L5.u64_at RSEGS M (o + 24) v1 -> 0 <= v1 < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 k ->
  exists fx' R' M', msteps RSEGS (st fx R SHR M) (st fx' R' LHEAD M')
    /\ (forall x, In x KSA -> getr R' (reg x) = getr R (reg x)) /\ at_head R' sp o k (o + 16) (Z.to_nat n) 0 /\ saved M' sp R
    /\ (forall a : word, ~ (sp - 48 <= bv_unsigned a < sp) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW Sap Ohi O8 O0 Hfb Hb0 On Hn Hk O24 Hv1 H2 H10 H11.
  set (Vf := VAL R R sp o k n fb 0 0 0 v1). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R R sp o k n fb 0 0 0 v1 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PAi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAi.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PAi.kn0). { unfold know_ok, PAi.kn0. L5K.kn_all ZA. }
  destruct (PAi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PAi.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PAi.regs0 PAi.regs_out0 48 KSA KSAi_ok HR Hag Hregs j Hj). }
  split. { unfold at_head. rewrite Z2Nat.id by lia. repeat split; rewrite (BG.out_reg PAi.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAi.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  change (SR.ps_cells PAi.ps0) with PAi.cells0 in Hcells. unfold PAi.cells0 in Hcells.
  split. { unfold saved, U. repeat split.
    all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PAi.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

Lemma srAd_conc fx R M (sp o k n fb d : Z) :
  spok sp -> L5.writable RSEGS M (sp - 48) 48 -> sp <= o -> o + 32 <= 2 ^ 47 -> o mod 8 = 0 ->
  L5.u8_at RSEGS M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = true -> L5.u64_at RSEGS M (o + 8) n -> 1 <= n <= 300 -> 1 <= k <= 63 ->
  L5.u64_at RSEGS M (o + 24) d -> 4096 <= d -> d + 8 * n <= 2 ^ 47 -> d mod 8 = 0 ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 k ->
  exists fx' R' M', msteps RSEGS (st fx R SHR M) (st fx' R' LHEAD M')
    /\ (forall x, In x KSA -> getr R' (reg x) = getr R (reg x)) /\ at_head R' sp o k d (Z.to_nat n) 0 /\ saved M' sp R
    /\ (forall a : word, ~ (sp - 48 <= bv_unsigned a < sp) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW Sap Ohi O8 O0 Hfb Hb0 On Hn Hk O24 Dlo Dhi D8 H2 H10 H11.
  set (Vf := VAL R R sp o k n fb d 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R R sp o k n fb d 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PAd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAd.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PAd.kn0). { unfold know_ok, PAd.kn0. L5K.kn_all ZA. }
  destruct (PAd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PAd.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PAd.regs0 PAd.regs_out0 48 KSA KSAd_ok HR Hag Hregs j Hj). }
  split. { unfold at_head. rewrite Z2Nat.id by lia. repeat split; rewrite (BG.out_reg PAd.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAd.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  change (SR.ps_cells PAd.ps0) with PAd.cells0 in Hcells. unfold PAd.cells0 in Hcells.
  split. { unfold saved, U. repeat split.
    all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PAd.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srI_conc fx (R0 R : bvmap 5 word) M (sp o k d w : Z) (n i : nat) :
  at_head R sp o k d n i -> (i + 1 < n)%nat -> (n <= 300)%nat -> 1 <= k <= 63 -> 0 <= sp - 48 -> sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  4096 <= d -> d + 8 * Z.of_nat n <= 2 ^ 47 -> d mod 8 = 0 ->
  L5.writable RSEGS M (d + 8 * Z.of_nat i) 8 -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) w -> 0 <= w < 2 ^ 64 -> L5.defined M (d + 8 * Z.of_nat i + 8) 8 ->
  exists fx' R' M', msteps RSEGS (st fx R LHEAD M) (st fx' R' LHEAD M')
    /\ (forall x, In x KSI -> getr R' (reg x) = getr R (reg x)) /\ at_head R' sp o k d n (S i)
    /\ (exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at RSEGS M' (d + 8 * Z.of_nat i) v)
    /\ (forall a : word, ~ (d + 8 * Z.of_nat i <= bv_unsigned a < d + 8 * Z.of_nat i + 8) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros (A2 & A8 & A9 & A10 & A11 & A12 & A13 & A19) Hi Hn Hk Hs1 Hs2 Ho Dlo Dhi D8 DW Xw Hw DD.
  set (Vf := VAL R0 R sp o k (Z.of_nat n) 0 d (Z.of_nat i) w 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp o k (Z.of_nat n) 0 d (Z.of_nat i) w 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PI.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PI.kn0). { unfold know_ok, PI.kn0. L5K.kn_all ZA. }
  destruct (PI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PI.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PI.regs0 PI.regs_out0 48 KSI KSI_ok HR Hag Hregs j Hj). }
  split. { unfold at_head. repeat split; rewrite (BG.out_reg PI.regs_out0 E' R' _ Hregs) by lia; cbn [nth PI.regs_out0];
           try replace (Z.of_nat (S i)) with (Z.of_nat i + 1) by lia; L5K.wordE' ZA Hag. }
  change (SR.ps_cells PI.ps0) with PI.cells0 in Hcells. unfold PI.cells0 in Hcells.
  split. { rewrite <- (Z.add_0_r (d + 8 * Z.of_nat i)). eapply (L5K.u64_of_KWord8_ex RSEGS E' M'). apply Hcells. left; reflexivity. L5K.evalE' ZA Hag. }
  split. { intros x Hx. apply Hfr. unfold PI.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

Lemma srL_conc fx (R0 R : bvmap 5 word) M (sp o k d w : Z) (n i : nat) :
  at_head R sp o k d n i -> (i + 1 = n)%nat -> (n <= 300)%nat -> 1 <= k <= 63 -> 0 <= sp - 48 -> sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  4096 <= d -> d + 8 * Z.of_nat n <= 2 ^ 47 -> d mod 8 = 0 ->
  L5.writable RSEGS M (d + 8 * Z.of_nat i) 8 -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) w -> 0 <= w < 2 ^ 64 ->
  exists fx' R' M', msteps RSEGS (st fx R LHEAD M) (st fx' R' L5RED.REDUCE M')
    /\ (forall x, In x KSL -> getr R' (reg x) = getr R (reg x)) /\ at_reduce R' sp o
    /\ (exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at RSEGS M' (d + 8 * Z.of_nat i) v)
    /\ (forall a : word, ~ (d + 8 * Z.of_nat i <= bv_unsigned a < d + 8 * Z.of_nat i + 8) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros (A2 & A8 & A9 & A10 & A11 & A12 & A13 & A19) Hi Hn Hk Hs1 Hs2 Ho Dlo Dhi D8 DW Xw Hw.
  set (Vf := VAL R0 R sp o k (Z.of_nat n) 0 d (Z.of_nat i) w 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp o k (Z.of_nat n) 0 d (Z.of_nat i) w 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PL.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PL.kn0). { unfold know_ok, PL.kn0. L5K.kn_all ZA. }
  destruct (PL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PL.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PL.regs0 PL.regs_out0 48 KSL KSL_ok HR Hag Hregs j Hj). }
  split. { unfold at_reduce, AFTER_REDUCE. repeat split; rewrite (BG.out_reg PL.regs_out0 E' R' _ Hregs) by lia; cbn [nth PL.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  change (SR.ps_cells PL.ps0) with PL.cells0 in Hcells. unfold PL.cells0 in Hcells.
  split. { rewrite <- (Z.add_0_r (d + 8 * Z.of_nat i)). eapply (L5K.u64_of_KWord8_ex RSEGS E' M'). apply Hcells. left; reflexivity. L5K.evalE' ZA Hag. }
  split. { intros x Hx. apply Hfr. unfold PL.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma srE_conc fx (R0 R : bvmap 5 word) M (sp o : Z) :
  spok sp -> L5.writable RSEGS M (sp - 48) 48 -> saved M sp R0 -> 0 <= o < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 48) -> getr R (reg 8) = Z_to_bv 64 o ->
  exists fx' R' M', msteps RSEGS (st fx R AFTER_REDUCE M) (st fx' R' RET M')
    /\ (forall x, In x KSE -> getr R' (reg x) = getr R (reg x)) /\ at_ret R0 R' sp o /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW SV Ho H2 H8. pose proof SV as (Q1 & Q2 & Q3 & Q4 & Q5). unfold U in *.
  set (Vf := VAL R0 R sp o 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp o 0 0 0 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PE.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PE.kn0). { unfold know_ok, PE.kn0. L5K.kn_all ZA. }
  destruct (PE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PE.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PE.regs0 PE.regs_out0 48 KSE KSE_ok HR Hag Hregs j Hj). }
  split. { unfold at_ret. repeat split; rewrite (BG.out_reg PE.regs_out0 E' R' _ Hregs) by lia; cbn [nth PE.regs_out0 edenot];
           first [reflexivity | rewrite <- (proj1 Hag) by lia; reflexivity | L5K.wordE' ZA Hag]. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sloop (m : nat) : forall fx (R0 R : bvmap 5 word) M (sp o k d : Z) (n i : nat) (wsi : list Z) (ws : list Z),
  (m = n - i)%nat -> at_head R sp o k d n i -> (i < n)%nat -> (1 <= n <= 300)%nat -> 1 <= k <= 63 ->
  0 <= sp - 48 -> sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 4096 <= d -> d + 8 * Z.of_nat n <= 2 ^ 47 -> d mod 8 = 0 ->
  L5.writable RSEGS M d (8 * Z.of_nat n) -> L5.defined M d (8 * Z.of_nat n) ->
  length wsi = i -> words_ok wsi -> L5.limbs_at RSEGS M d wsi ->
  length ws = n -> words_ok ws -> (forall j, (i <= j < n)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat j) (nth_w ws j)) ->
  exists fx' R' M' (rw : list Z), msteps RSEGS (st fx R LHEAD M) (st fx' R' L5RED.REDUCE M')
    /\ (forall x, In x KSLOOP -> getr R' (reg x) = getr R (reg x)) /\ at_reduce R' sp o
    /\ length rw = n /\ words_ok rw /\ L5.limbs_at RSEGS M' d rw
    /\ (forall a : word, ~ (d <= bv_unsigned a < d + 8 * Z.of_nat n) -> M' a = M a) /\ mem_grows M M'.
Proof.
  induction m as [|m IH]; intros fx R0 R M sp o k d n i wsi ws Hm AT Hi Hn Hk Hs1 Hs2 Ho Dlo Dhi D8 DW DD WL WO WS WSL WSO WSR. lia.
  pose proof (words_ok_nth ws i WSO) as Wi. pose proof (WSR i ltac:(lia)) as Xi.
  destruct (Nat.eq_dec (i + 1) n) as [Hlast | Hmore].
  - destruct (srL_conc fx R0 R M sp o k d (nth_w ws i) n i AT Hlast ltac:(lia) Hk Hs1 Hs2 Ho Dlo Dhi D8 ltac:(eapply L5.writable_sub; [exact DW|lia|lia]) Xi Wi)
      as (fx1 & R1 & M1 & MS1 & K1 & AT1 & (v & Rv & Xv) & FR1 & G1).
    exists fx1, R1, M1, (wsi ++ [v]). split. exact MS1.
    split. { intros x Hx. apply K1. apply (L5K.incl_b KSLOOP KSL ltac:(vm_compute; reflexivity)). exact Hx. }
    split. exact AT1.
    split. { rewrite length_app, WL. cbn. lia. } split. { apply words_ok_app. exact WO. constructor. lia. constructor. }
    split. { intros j Hj. rewrite length_app, WL in Hj. cbn in Hj. destruct (Nat.eq_dec j i) as [->|NE].
             - rewrite app_nth2 by lia. rewrite WL, Nat.sub_diag. cbn. exact Xv.
             - rewrite app_nth1 by lia. eapply (L5K.u64_at_keep RSEGS M M1). exact FR1. lia. lia. lia. apply WS. lia. }
    split. { intros a Ha. apply FR1. lia. } exact G1.
  - destruct (srI_conc fx R0 R M sp o k d (nth_w ws i) n i AT ltac:(lia) ltac:(lia) Hk Hs1 Hs2 Ho Dlo Dhi D8 ltac:(eapply L5.writable_sub; [exact DW|lia|lia]) Xi Wi
                ltac:(eapply L5.defined_sub; [exact DD|lia|lia])) as (fx1 & R1 & M1 & MS1 & K1 & AT1 & (v & Rv & Xv) & FR1 & G1).
    assert (WS1: L5.limbs_at RSEGS M1 d (wsi ++ [v])).
    { intros j Hj. rewrite length_app, WL in Hj. cbn in Hj. destruct (Nat.eq_dec j i) as [->|NE].
      - rewrite app_nth2 by lia. rewrite WL, Nat.sub_diag. cbn. exact Xv.
      - rewrite app_nth1 by lia. eapply (L5K.u64_at_keep RSEGS M M1). exact FR1. lia. lia. lia. apply WS. lia. }
    destruct (IH fx1 R0 R1 M1 sp o k d n (S i) (wsi ++ [v]) ws ltac:(lia) AT1 ltac:(lia) Hn Hk Hs1 Hs2 Ho Dlo Dhi D8
                 ltac:(eapply L5.writable_grows; eauto) ltac:(eapply L5.defined_grows; eauto)
                 ltac:(rewrite length_app, WL; cbn; lia) ltac:(apply words_ok_app; [exact WO | constructor; [lia | constructor]]) WS1 WSL WSO
                 ltac:(intros j Hj; eapply (L5K.u64_at_keep RSEGS M M1); [exact FR1 | lia | lia | lia | apply WSR; lia]))
      as (fx' & R' & M' & rw & MS & K & AT' & RL & RO & RS & FR & G).
    exists fx', R', M', rw. split. eapply msteps_trans; eauto.
    split. { intros x Hx. rewrite (K x Hx). apply K1. apply (L5K.incl_b KSLOOP KSI ltac:(vm_compute; reflexivity)). exact Hx. }
    split. exact AT'. split. exact RL. split. exact RO. split. exact RS.
    split. { intros a Ha. rewrite (FR a Ha). apply FR1. lia. } eapply mem_grows_trans; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma r1 : (1%bv : bv 5) = reg 1. Proof. apply bv_eq; reflexivity. Qed.
Lemma r2 : (2%bv : bv 5) = reg 2. Proof. apply bv_eq; reflexivity. Qed.
Lemma r10 : (10%bv : bv 5) = reg 10. Proof. apply bv_eq; reflexivity. Qed.
Lemma r11 : (11%bv : bv 5) = reg 11. Proof. apply bv_eq; reflexivity. Qed.
Definition cs_all : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma preserved_by_index (R R' : bvmap 5 word) : (forall i, In i cs_all -> getr R' (reg i) = getr R (reg i)) -> regs_preserved R R'.
Proof.
  intros K x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply K.
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.
Lemma preserved_of_ret (R R' : bvmap 5 word) sp o :
  getr R (reg 2) = Z_to_bv 64 sp -> at_ret R R' sp o -> (forall i, In i cs_pass -> getr R' (reg i) = getr R (reg i)) ->
  regs_preserved R R'.
Proof.
  intros H2 (T1 & T2 & T8 & T9 & T18 & T19 & _) K. apply preserved_by_index. intros i Hi. cbn in Hi.
  repeat (destruct Hi as [<-|Hi]; [first [rewrite T2, H2; reflexivity | assumption | apply K; cbn; tauto] |]). destruct Hi.
Qed.
Lemma pass_of_preserved R R' : regs_preserved R R' -> forall i, In i cs_pass -> getr R' (reg i) = getr R (reg i).
Proof.
  intros RP i Hi. apply RP. unfold callee_saved_idx. cbn in Hi.
  repeat (destruct Hi as [<-|Hi]; [cbn; tauto|]). destruct Hi.
Qed.
Lemma u64_at_agree1 M M' a v : (forall i, a <= i < a + 8 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v.
Proof. intros HA Ha H8 Hu. eapply (L5C.u64_at_agree RSEGS M M'). intros i Hi. apply HA. exact Hi. lia. lia. exact Hu. Qed.
Lemma two_words (l : list Z) : length l = 2%nat -> l = [nth_w l 0; nth_w l 1].
Proof. intros H. destruct l as [|a [|b [|c l]]]; cbn in H; try lia. reflexivity. Qed.
Lemma one_word (l : list Z) : length l = 1%nat -> l = [nth_w l 0].
Proof. intros H. destruct l as [|a [|b l]]; cbn in H; try lia. reflexivity. Qed.

Theorem shr_ok : shr_spec.
Proof.
  intros fx R M model K o sp r k b ws Mh Ml H10 H11 Hk H1 RA H2 A16 SLO Aso Ohi Ao DEF DEFo OB Hn WS WL WO DEFd BLO KONT.
  pose proof RA as [Hr He]. rewrite r10 in H10. rewrite r11 in H11. rewrite r1 in H1. rewrite r2 in H2.
  assert (SP: spok sp). { split. exact A16. lia. }
  assert (WR48: L5.writable RSEGS M (sp - 48) 48) by (apply writable_of_defined; [exact DEF|lia|lia]).
  destruct b as [fb len sto]. pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_cap L5.bo_data] in *.
  set (dd := L5.bo_data o (L5.BO fb len sto)) in *. set (cc := L5.bo_cap (L5.BO fb len sto)) in *.
  assert (DFACTS: Z.of_nat len <= cc /\ 4096 <= dd /\ dd + 8 * cc <= 2 ^ 47 /\ dd mod 8 = 0 /\ (dd + 8 * cc <= sp - 48 \/ dd = o + 16)).
  { subst dd cc. destruct sto as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_cap L5.bo_st L5.bo_len].
    - destruct OST as (_ & _ & _ & Hl2 & _). split. lia. split. lia. split. lia. split. rewrite <- Zplus_mod_idemp_l, Ao. reflexivity. right; reflexivity.
    - destruct OST as (B0 & O16 & O24 & Hlc & Hc & Q8 & QLO & QHI & HAP). split. exact Hlc. split. exact QLO. split. exact QHI. split. exact Q8. left. apply BLO. reflexivity. }
  destruct DFACTS as (LC & DLO & DHI & D8 & DAP).
  (* [comment removed for export] *)
  assert (ENTRY: exists fx1 R1 M1, msteps RSEGS (st fx R SHR M) (st fx1 R1 LHEAD M1)
      /\ (forall x, In x KSA -> getr R1 (reg x) = getr R (reg x)) /\ at_head R1 sp o k dd len 0 /\ saved M1 sp R
      /\ (forall a : word, ~ (sp - 48 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1).
  { subst dd cc. destruct sto as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_cap L5.bo_st L5.bo_len] in *.
    - destruct OST as (B0 & O16 & O24 & Hl2 & R0' & R1').
      destruct (srAi_conc fx R M sp o k (Z.of_nat len) fb v1 SP WR48 Aso Ohi Ao O0 Hfb B0 O8 ltac:(lia) Hk O24 R1' H2 H10 H11) as (fx1 & R1 & M1 & X).
      rewrite Nat2Z.id in X. exists fx1, R1, M1. exact X.
    - destruct OST as (B0 & O16 & O24 & Hlc & Hc & Q8 & QLO & QHI & HAP).
      destruct (srAd_conc fx R M sp o k (Z.of_nat len) fb q SP WR48 Aso Ohi Ao O0 Hfb B0 O8 ltac:(lia) Hk O24 QLO ltac:(lia) Q8 H2 H10 H11) as (fx1 & R1 & M1 & X).
      rewrite Nat2Z.id in X. exists fx1, R1, M1. exact X. }
  destruct ENTRY as (fx1 & R1 & M1 & MS1 & K1 & AT1 & SV1 & FR1 & G1).
  assert (FR1z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 48 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hna. apply FR1. rewrite BG.unsigned_lit by lia. exact Hna. }
  assert (DNS: forall i, dd <= i < dd + 8 * cc -> ~ (sp - 48 <= i < sp)). { intros i Hi. destruct DAP; lia. }
  assert (WS1: forall j, (0 <= j < len)%nat -> L5.u64_at RSEGS M1 (dd + 8 * Z.of_nat j) (nth_w ws j)).
  { intros j Hj. eapply u64_at_agree1. intros i Hi. apply FR1z. lia. apply DNS. lia. lia. lia. apply WS. lia. }
  (* [comment removed for export] *)
  destruct (sloop (len - 0) fx1 R R1 M1 sp o k dd len 0 [] ws ltac:(lia) AT1 ltac:(lia) Hn Hk ltac:(lia) ltac:(lia) ltac:(lia) DLO ltac:(lia) D8
              ltac:(eapply L5.writable_grows; [exact G1 | apply writable_of_defined; [eapply L5.defined_sub; [exact DEFd|lia|lia] | lia | lia]])
              ltac:(eapply L5.defined_grows; [exact G1 | eapply L5.defined_sub; [exact DEFd|lia|lia]])
              eq_refl ltac:(constructor) ltac:(intros j Hj; cbn in Hj; lia) WL WO WS1)
    as (fx2 & R2 & M2 & rw & MS2 & K2 & (C1 & C2 & C8 & C10) & RWL & RWO & LIMBS2 & FR2 & G2).
  assert (FR2z: forall a, 0 <= a < 2 ^ 64 -> ~ (dd <= a < dd + 8 * Z.of_nat len) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hna. apply FR2. rewrite BG.unsigned_lit by lia. exact Hna. }
  (* [comment removed for export] *)
  set (st2 := match sto with L5.BDyn c q => L5.BDyn c q | L5.BInl v0 v1 => L5.BInl (nth_w rw 0) (if Nat.eqb len 2 then nth_w rw 1 else v1) end).
  assert (OB2: L5.big_at RSEGS M2 o (L5.BO fb len st2)).
  { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
    assert (HDR: forall a v, o <= a -> a + 8 <= o + 16 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M2 a v).
    { intros a v X Y Hu. eapply u64_at_agree1. intros i Hi. rewrite FR2z. apply FR1z. lia. lia. lia. destruct DAP; lia. lia. lia. exact Hu. }
    split. { eapply (L5C.u8_at_agree RSEGS M M2). intros i Hi. rewrite FR2z. apply FR1z. lia. lia. lia. destruct DAP; lia. lia. lia. exact O0. }
    split. exact Hfb. split. { apply HDR. lia. lia. exact O8. }
    subst st2 dd cc. destruct sto as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_cap L5.bo_st L5.bo_len] in *.
    - destruct OST as (B0 & O16 & O24 & Hl2 & R0' & R1'). split. exact B0.
      pose proof (words_ok_nth rw 0 RWO). pose proof (words_ok_nth rw 1 RWO).
      split. { replace (o + 16) with (o + 16 + 8 * Z.of_nat 0) by lia. apply LIMBS2. lia. }
      split. { destruct (Nat.eqb_spec len 2). replace (o + 24) with (o + 16 + 8 * Z.of_nat 1) by lia. apply LIMBS2. lia.
               eapply u64_at_agree1. intros i Hi. rewrite FR2z. apply FR1z. lia. lia. lia. lia. lia. lia. exact O24. }
      split. exact Hl2. split. lia. destruct (Nat.eqb len 2); lia.
    - destruct OST as (B0 & O16 & O24 & Hlc & Hc & Q8 & QLO & QHI & HAP). pose proof (BLO cap q eq_refl) as QB. split. exact B0.
      split. { eapply u64_at_agree1. intros i Hi. rewrite FR2z. apply FR1z. lia. lia. lia. lia. lia. lia. exact O16. }
      split. { eapply u64_at_agree1. intros i Hi. rewrite FR2z. apply FR1z. lia. lia. lia. lia. lia. lia. exact O24. }
      repeat split; first [assumption | lia]. }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. eapply msteps_trans. exact MS1. exact MS2.
  eapply (L5REDG.reduce_ok fx2 R2 M2 model K o AFTER_REDUCE (L5.BO fb len st2) rw Mh Ml).
  + rewrite r10. exact C10. + rewrite r1. exact C1. + split. unfold AFTER_REDUCE. lia. reflexivity.
  + exact OB2. + exact Ao. + lia. + lia.
  + eapply L5.writable_grows. eapply mem_grows_trans. exact G1. exact G2. apply writable_of_defined. eapply L5.defined_sub. exact DEFo. lia. lia. lia. lia.
  + replace (L5.bo_data o (L5.BO fb len st2)) with dd by (subst st2 dd; destruct sto; reflexivity).
    replace (L5.bo_cap (L5.BO fb len st2)) with cc by (subst st2 cc; destruct sto; reflexivity).
    eapply L5.defined_grows. eapply mem_grows_trans. exact G1. exact G2. exact DEFd.
  + replace (L5.bo_data o (L5.BO fb len st2)) with dd by (subst st2 dd; destruct sto; reflexivity). exact LIMBS2.
  + exact RWL. + exact RWO.
  + intros cap q Hst. left. subst st2. destruct sto; [discriminate|]. inversion Hst; subst. specialize (BLO _ _ eq_refl). cbn in dd, cc. lia.
  + (* [comment removed for export] *)
    intros fx3 R3 M3 (OB3 & RP3 & B10 & FR3 & G3). cbn [L5.bo_fb L5.bo_st] in OB3.
    assert (FR3z: forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 16) -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
    { intros a Ha Hna. apply FR3. intros rg [<-|[]]. unfold L5.in_rng. cbn. rewrite BG.unsigned_lit by lia. lia. }
    assert (E2: getr R3 (reg 2) = Z_to_bv 64 (sp - 48)). { rewrite <- r2, (RP3 2%bv ltac:(cbn; tauto)), r2. exact C2. }
    assert (E8: getr R3 (reg 8) = Z_to_bv 64 o). { rewrite (RP3 (reg 8) ltac:(cbn; tauto)). exact C8. }
    assert (CH: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 48 <= a < sp) -> ~ (o <= a < o + 16) -> ~ (dd <= a < dd + 8 * Z.of_nat len) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha X Y W. rewrite FR3z by lia. rewrite FR2z by lia. apply FR1z; lia. }
    assert (SV3: saved M3 sp R).
    { destruct SV1 as (S1 & S2 & S3 & S4 & S5).
      repeat split; (eapply u64_at_agree1; [intros i Hi; rewrite FR3z by lia; apply FR2z; [lia | intros C; apply (DNS i); lia] | lia | lia | assumption]). }
    assert (G03: mem_grows M M3). { eapply mem_grows_trans. exact G1. eapply mem_grows_trans. exact G2. exact G3. }
    destruct (srE_conc fx3 R R3 M3 sp o SP ltac:(eapply L5.writable_grows; [exact G03 | exact WR48]) SV3 ltac:(lia) E2 E8) as (fx4 & R4 & M4 & MS4 & K4 & RET4 & MM4 & G4).
    pose proof RET4 as (T1 & T2 & T8 & T9 & T18 & T19 & T10).
    pose proof (ret_22b68 fx4 R4 M4 r ltac:(rewrite T1; exact H1) Hr He) as MS5.
    unfold L5RED.cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. eapply msteps_trans. exact MS4. exact MS5.
    apply (KONT fx4 R4 M4 rw st2).
    unfold shr_post. cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data].
    split. { apply (preserved_of_ret R R4 sp o H2 RET4). intros i Hi. rewrite (K4 i) by (apply (L5K.incl_b cs_pass KSE ltac:(vm_compute; reflexivity)); exact Hi).
             rewrite (pass_of_preserved R2 R3 RP3 i Hi). rewrite (K2 i) by (apply (L5K.incl_b cs_pass KSLOOP ltac:(vm_compute; reflexivity)); exact Hi).
             apply K1. apply (L5K.incl_b cs_pass KSA ltac:(vm_compute; reflexivity)). exact Hi. }
    split. { rewrite r10. exact T10. }
    split. exact RWL. split. exact RWO.
    split. { eapply (L5C.big_at_agree RSEGS M3 M4). intros i Hi. apply MM4. lia. lia. exact OB3. }
    split. { fold dd. intros j Hj. eapply u64_at_agree1. intros i Hi. rewrite MM4. apply FR3z. lia. rewrite RWL in Hj. pose proof (DNS i). destruct DAP; lia. lia. rewrite RWL in Hj; lia. apply LIMBS2. exact Hj. }
    split. { subst st2. destruct sto; [exact I | split; reflexivity]. }
    split. { intros a X Y W. fold dd in W. rewrite MM4. pose proof (word_range a).
             rewrite (word_self a). apply CH; lia. }
    eapply mem_grows_trans. exact G03. exact G4.
Qed.
End SCFG_2.


End L5SHR.
