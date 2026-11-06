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
     Src0_code_22348_22f60 BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkDq BigLinkReduce L5Defs L5Kn
     L5Core L5CoreSpecs L5Words L5Reduce L5ReduceG.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsOps.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5Shl.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5SHL.
Import L5CS.
Module PA := LibSegZ_shA. Module PA0 := LibSegZ_shA0. Module PBd := LibSegZ_shBd. Module PBi := LibSegZ_shBi.
Module PI := LibSegZ_shI. Module PR := LibSegZ_shR. Module PE := LibSegZ_shE.
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition SHL : Z := 0x22894.
Definition AFTER_RESIZE : Z := 0x22940. Definition LHEAD : Z := 0x22994. Definition LDONE : Z := 0x229bc.
Definition AFTER_REDUCE : Z := 0x229c4. Definition RET : Z := 0x229e0.
Definition SHL_SCR : Z := 48 + RESIZE_SCR.
Definition MAXW : Z := 18446744073709551615.
End SCFG_1.


Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Import L5W.
Section SCFG_2.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Definition shl_result (ws : list Z) (k : Z) : list Z := if k =? 0 then ws else shl_words ws k.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition apart (x lx y ly : Z) : Prop := x + lx <= y \/ y + ly <= x.

Definition shl_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o sp k : Z) (b : L5.bigobj) (ws : list Z) (g : growth) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 o /\
  let r := shl_result ws k in
  let m := length r in
  let n' := rlen r in
  let fbg := match g with Same => L5.bo_fb b | Grown _ _ => Z.lor (L5.bo_fb b) 1 end in
  let fb' := if Nat.eqb n' 0 then Z.land fbg 253 else fbg in
  exists st',
    L5.big_at RSEGS M' o (L5.BO fb' n' st') /\ L5C.obj_limbs RSEGS M' (L5.BO fb' m st') r /\ (n' <= m)%nat /\
    match g with
    | Same => (L5.bo_dyn b = true \/ (m <= 2)%nat) /\ LB' = LB /\ cr' = cr
              /\ match L5.bo_st b, st' with
                 | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
                 | L5.BInl _ _, L5.BInl _ _ => True
                 | _, _ => False end
              /\ L5C.hpres L LB sp SHL_SCR [(o, 32); (L5.bo_data o b, 8 * Z.of_nat m)] M M'
    | Grown A cap => L5.bo_dyn b = false /\ (3 <= m)%nat /\ cap = round_up (Z.of_nat m) /\ LB' = (A, 8 * cap) :: LB /\ cr' = debit L cr (8 * cap)
              /\ L5C.fresh_block L LB M' A (8 * cap) /\ st' = L5.BDyn cap A
              /\ L5C.hpres L LB sp SHL_SCR [(o, 32)] M M'
    end.

Definition shl_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o sp r k : Z) (b : L5.bigobj) (ws : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 k -> 0 <= k <= 63 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp SHL_SCR ->
    L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> (1 <= L5.bo_len b <= 300)%nat ->
    o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.defined M o 32 ->
    (L5.bo_dyn b = true -> Z.of_nat (L5.bo_len b) + 1 <= L5.bo_cap b) ->
    (1 <= k -> L5.bo_len b = 2%nat -> L5.bo_dyn b = false -> credit_ok L cr (8 * round_up 3)) ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        shl_post L LB cr M M' R R' o sp k b ws g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R SHL M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mask_range k : 0 <= k <= 63 -> 0 <= 2 ^ k - 1 < 2 ^ 64.
Proof. intros Hk. split. pose proof (Z.pow_pos_nonneg 2 k); lia. pose proof (Z.pow_le_mono_r 2 k 63); lia. Qed.
Lemma pow_k_pos k : 0 <= k -> 0 < 2 ^ k. Proof. intros; apply Z.pow_pos_nonneg; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_228a8 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R 0x229e0 M) (st fx R r M).
Proof. intros H1 Hr He. apply (BRED.ret_to fx R M 0x229e0 W_229e0 r F_229e0 eq_refl D_229e0 H1 Hr He). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition U (R : bvmap 5 word) (j : nat) : Z := bv_unsigned (getr R (reg j)).
Definition VAL (R0 R : bvmap 5 word) (sp o k n fb d i w c m : Z) (j : nat) : word :=
  match j with
  | 2%nat => Z_to_bv 64 sp
  | 33%nat => Z_to_bv 64 o | 34%nat => Z_to_bv 64 k | 35%nat => Z_to_bv 64 n | 36%nat => Z_to_bv 64 fb | 37%nat => Z_to_bv 64 d
  | 39%nat => Z_to_bv 64 i | 40%nat => Z_to_bv 64 w | 41%nat => Z_to_bv 64 c | 42%nat => getr R (reg 1)
  | 43%nat => getr R0 (reg 1) | 44%nat => getr R0 (reg 8) | 47%nat => getr R0 (reg 9) | 38%nat => getr R0 (reg 18) | 32%nat => getr R0 (reg 19)
  | 45%nat => Z_to_bv 64 (64 - k) | 46%nat => Z_to_bv 64 m
  | _ => getr R (reg j)
  end.
Definition VZ (R0 R : bvmap 5 word) (sp o k n fb d i w c m : Z) (j : nat) : Z :=
  match j with
  | 2%nat => sp
  | 33%nat => o | 34%nat => k | 35%nat => n | 36%nat => fb | 37%nat => d | 39%nat => i | 40%nat => w | 41%nat => c | 42%nat => U R 1
  | 43%nat => U R0 1 | 44%nat => U R0 8 | 47%nat => U R0 9 | 38%nat => U R0 18 | 32%nat => U R0 19
  | 45%nat => 64 - k | 46%nat => m
  | _ => U R j
  end.
Lemma VAL_VZ R0 R sp o k n fb d i w c m :
  0 <= sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= k <= 63 -> 0 <= n < 2 ^ 62 -> 0 <= fb < 256 -> 0 <= d < 2 ^ 64 -> 0 <= i < 2 ^ 62 ->
  0 <= w < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  forall j, bv_unsigned (ev (Env (VAL R0 R sp o k n fb d i w c m) (fun _ => [])) j) = VZ R0 R sp o k n fb d i w c m j.
Proof.
  intros until j. cbn [ev]. unfold VAL, VZ, U.
  repeat (lazymatch goal with
          | |- bv_unsigned (match j with _ => _ end) = _ => destruct j as [|j]
          | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.

(* [comment removed for export] *)
Definition saved (M : word -> option byte) (sp : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (U R0 1) /\ L5.u64_at RSEGS M (sp - 16) (U R0 8) /\ L5.u64_at RSEGS M (sp - 24) (U R0 9) /\
  L5.u64_at RSEGS M (sp - 32) (U R0 18) /\ L5.u64_at RSEGS M (sp - 40) (U R0 19).
Definition spok (sp : Z) : Prop := sp mod 16 = 0 /\ 1048624 <= sp <= 140737488355328.
Definition at_ret (R0 R' : bvmap 5 word) (sp o : Z) : Prop :=
  getr R' (reg 1) = getr R0 (reg 1) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = getr R0 (reg 8) /\ getr R' (reg 9) = getr R0 (reg 9) /\
  getr R' (reg 18) = getr R0 (reg 18) /\ getr R' (reg 19) = getr R0 (reg 19) /\ getr R' (reg 10) = Z_to_bv 64 o.
(* [comment removed for export] *)
Definition sh_pass : list nat := [3; 4; 5; 6; 7; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

Lemma rdn_exteq (M M' : word -> option byte) : (forall x : word, M' x = M x) -> forall n a, rdn RSEGS M' a n = rdn RSEGS M a n.
Proof. intros MM. induction n as [|n IH]; intros a. reflexivity. cbn [rdn]. rewrite MM, IH. reflexivity. Qed.
Lemma u64_keep M M' a v : (forall x : word, M' x = M x) -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v.
Proof. intros MM Hu. unfold L5.u64_at in *. rewrite <- Hu. apply rdn_exteq. exact MM. Qed.
Lemma saved_keep M M' sp R0 : (forall x : word, M' x = M x) -> saved M sp R0 -> saved M' sp R0.
Proof. intros MM (S1 & S2 & S3 & S4 & S5). repeat split; eapply u64_keep; eauto. Qed.
Lemma saved_keep_out M M' sp R0 lo hi : (forall x : word, ~ (lo <= bv_unsigned x < hi) -> M' x = M x) ->
  (sp <= lo \/ hi <= sp - 48 \/ hi <= lo) -> 48 <= sp -> sp <= 2 ^ 64 -> saved M sp R0 -> saved M' sp R0.
Proof.
  intros HF Hap H1 H2 (S1 & S2 & S3 & S4 & S5).
  repeat split; (eapply (L5K.u64_at_keep RSEGS M M'); [exact HF | lia | lia | lia | eassumption]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KSA : list nat := Eval vm_compute in (BG.kept_list 48 PA.regs0 PA.regs_out0).
Lemma KSA_ok : BG.kept_ok 48 PA.regs0 PA.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.
Definition KSA0 : list nat := Eval vm_compute in (BG.kept_list 48 PA0.regs0 PA0.regs_out0).
Lemma KSA0_ok : BG.kept_ok 48 PA0.regs0 PA0.regs_out0 KSA0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KSBd : list nat := Eval vm_compute in (BG.kept_list 48 PBd.regs0 PBd.regs_out0).
Lemma KSBd_ok : BG.kept_ok 48 PBd.regs0 PBd.regs_out0 KSBd = true. Proof. vm_compute. reflexivity. Qed.
Definition KSBi : list nat := Eval vm_compute in (BG.kept_list 48 PBi.regs0 PBi.regs_out0).
Lemma KSBi_ok : BG.kept_ok 48 PBi.regs0 PBi.regs_out0 KSBi = true. Proof. vm_compute. reflexivity. Qed.
Definition KSI : list nat := Eval vm_compute in (BG.kept_list 48 PI.regs0 PI.regs_out0).
Lemma KSI_ok0 : BG.kept_ok 48 PI.regs0 PI.regs_out0 KSI = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSI_ok1 : BG.kept_ok 48 PI.regs0 PI.regs_out1 KSI = true. Proof. vm_compute. reflexivity. Qed.
Definition KSR : list nat := Eval vm_compute in (BG.kept_list 48 PR.regs0 PR.regs_out0).
Lemma KSR_ok : BG.kept_ok 48 PR.regs0 PR.regs_out0 KSR = true. Proof. vm_compute. reflexivity. Qed.
Definition KSE : list nat := Eval vm_compute in (BG.kept_list 48 PE.regs0 PE.regs_out0).
Lemma KSE_ok : BG.kept_ok 48 PE.regs0 PE.regs_out0 KSE = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_resize (R : bvmap 5 word) (sp o k n : Z) : Prop :=
  getr R (reg 1) = Z_to_bv 64 AFTER_RESIZE /\ getr R (reg 2) = Z_to_bv 64 (sp - 48) /\ getr R (reg 8) = Z_to_bv 64 o /\
  getr R (reg 9) = Z_to_bv 64 k /\ getr R (reg 10) = Z_to_bv 64 o /\ getr R (reg 11) = Z_to_bv 64 (n + 1) /\
  getr R (reg 18) = Z_to_bv 64 (o + 16) /\ getr R (reg 19) = Z_to_bv 64 0.

Lemma shA_conc fx R M (sp o k n : Z) :
  spok sp -> L5.writable RSEGS M (sp - 48) 48 -> apart (sp - 48) 48 o 32 ->
  1048576 <= o -> o + 32 <= 2 ^ 47 -> o mod 8 = 0 -> L5.u64_at RSEGS M (o + 8) n -> 1 <= n <= 300 -> 1 <= k <= 63 ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 k ->
  exists fx' R' M', msteps RSEGS (st fx R SHL M) (st fx' R' RESIZE M')
    /\ (forall x, In x KSA -> getr R' (reg x) = getr R (reg x)) /\ at_resize R' sp o k n /\ saved M' sp R
    /\ (forall a : word, ~ (sp - 48 <= bv_unsigned a < sp) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW Sap Olo Ohi O8 On Hn Hk H2 H10 H11. unfold apart in *.
  set (Vf := VAL R R sp o k n 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R R sp o k n 0 0 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PA.kn0). { unfold know_ok, PA.kn0. L5K.kn_all ZA. }
  destruct (PA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PA.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA.regs0 PA.regs_out0 48 KSA KSA_ok HR Hag Hregs j Hj). }
  split. { unfold at_resize, AFTER_RESIZE. repeat split; rewrite (BG.out_reg PA.regs_out0 E' R' _ Hregs) by lia; cbn [nth PA.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  change (SR.ps_cells PA.ps0) with PA.cells0 in Hcells. unfold PA.cells0 in Hcells.
  split. { unfold saved, U. repeat split.
    all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PA.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Definition at_reduce (R : bvmap 5 word) (sp o : Z) : Prop :=
  getr R (reg 1) = Z_to_bv 64 AFTER_REDUCE /\ getr R (reg 2) = Z_to_bv 64 (sp - 48) /\ getr R (reg 8) = Z_to_bv 64 o /\ getr R (reg 10) = Z_to_bv 64 o.

Lemma shA0_conc fx R M (sp o n : Z) :
  spok sp -> L5.writable RSEGS M (sp - 48) 48 -> apart (sp - 48) 48 o 32 ->
  1048576 <= o -> o + 32 <= 2 ^ 47 -> o mod 8 = 0 -> L5.u64_at RSEGS M (o + 8) n -> 0 <= n <= 134217728 ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 0 ->
  exists fx' R' M', msteps RSEGS (st fx R SHL M) (st fx' R' L5RED.REDUCE M')
    /\ (forall x, In x KSA0 -> getr R' (reg x) = getr R (reg x)) /\ at_reduce R' sp o /\ saved M' sp R
    /\ (forall a : word, ~ (sp - 48 <= bv_unsigned a < sp) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW Sap Olo Ohi O8 On Hn H2 H10 H11. unfold apart in *.
  set (Vf := VAL R R sp o 0 n 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R R sp o 0 n 0 0 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PA0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA0.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PA0.kn0). { unfold know_ok, PA0.kn0. L5K.kn_all ZA. }
  destruct (PA0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PA0.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA0.regs0 PA0.regs_out0 48 KSA0 KSA0_ok HR Hag Hregs j Hj). }
  split. { unfold at_reduce, AFTER_REDUCE. repeat split; rewrite (BG.out_reg PA0.regs_out0 E' R' _ Hregs) by lia; cbn [nth PA0.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  change (SR.ps_cells PA0.ps0) with PA0.cells0 in Hcells. unfold PA0.cells0 in Hcells.
  split. { unfold saved, U. repeat split.
    all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PA0.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_head (R : bvmap 5 word) (sp o k d : Z) (i : nat) (c : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 48) /\ getr R (reg 8) = Z_to_bv 64 o /\ getr R (reg 9) = Z_to_bv 64 k /\
  getr R (reg 10) = Z_to_bv 64 (Z.of_nat i) /\ getr R (reg 11) = Z_to_bv 64 c /\ getr R (reg 12) = Z_to_bv 64 (64 - k) /\
  getr R (reg 13) = Z_to_bv 64 (2 ^ k - 1) /\ getr R (reg 14) = Z_to_bv 64 (d + 8 * Z.of_nat i - 8) /\ getr R (reg 18) = Z_to_bv 64 d.

(* [comment removed for export] *)
Lemma mulM1 x : 0 <= x < 2 ^ 64 -> (MAXW * x) mod 2 ^ 64 = (2 ^ 64 - x) mod 2 ^ 64.
Proof. intros Hx. unfold MAXW. replace (18446744073709551615 * x) with ((2 ^ 64 - x) + (x - 1) * 2 ^ 64) by lia. apply Z_mod_plus_full. Qed.
Lemma k1_ident k : 1 <= k <= 63 -> ((MAXW * k) mod 2 ^ 64 + 64) mod 2 ^ 64 = 64 - k.
Proof.
  intros Hk. rewrite mulM1 by lia. rewrite (Z.mod_small (2 ^ 64 - k)) by lia.
  replace (2 ^ 64 - k + 64) with ((64 - k) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma mask_ident k : 1 <= k <= 63 -> ((MAXW * ((MAXW * 2 ^ (k mod 64)) mod 2 ^ 64)) mod 2 ^ 64 + MAXW) mod 2 ^ 64 = 2 ^ k - 1.
Proof.
  intros Hk. rewrite (Z.mod_small k 64) by lia.
  pose proof (pow_k_pos k ltac:(lia)) as P. pose proof (Z.pow_le_mono_r 2 k 63 ltac:(lia) ltac:(lia)) as P63.
  rewrite (mulM1 (2 ^ k)) by lia. rewrite (Z.mod_small (2 ^ 64 - 2 ^ k)) by lia.
  rewrite mulM1 by lia. replace (2 ^ 64 - (2 ^ 64 - 2 ^ k)) with (2 ^ k) by lia. rewrite (Z.mod_small (2 ^ k)) by lia.
  unfold MAXW. replace (2 ^ k + 18446744073709551615) with ((2 ^ k - 1) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma shBd_conc fx (R0 R : bvmap 5 word) M (sp o k fb d : Z) (n : nat) :
  spok sp -> L5.writable RSEGS M (sp - 48) 48 -> apart (sp - 48) 48 o 32 ->
  1048576 <= o -> o + 32 <= 2 ^ 47 -> o mod 8 = 0 ->
  L5.u8_at RSEGS M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = true -> L5.u64_at RSEGS M (o + 8) (Z.of_nat n + 1) -> L5.u64_at RSEGS M (o + 24) d ->
  (1 <= n <= 300)%nat -> 1 <= k <= 63 ->
  4096 <= d -> d + 8 * Z.of_nat n + 8 <= 2 ^ 47 -> d mod 8 = 0 -> L5.writable RSEGS M d (8 * Z.of_nat n + 8) -> L5.defined M d (8 * Z.of_nat n) ->
  L5.u64_at RSEGS M (d + 8 * Z.of_nat n) 0 -> apart (sp - 48) 48 d (8 * Z.of_nat n + 8) -> apart o 32 d (8 * Z.of_nat n + 8) ->
  getr R (reg 2) = Z_to_bv 64 (sp - 48) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 k ->
  getr R (reg 18) = Z_to_bv 64 (o + 16) -> getr R (reg 19) = Z_to_bv 64 0 ->
  exists fx' R' M', msteps RSEGS (st fx R AFTER_RESIZE M) (st fx' R' LHEAD M')
    /\ (forall x, In x KSBd -> getr R' (reg x) = getr R (reg x)) /\ at_head R' sp o k d n 0
    /\ L5.u64_at RSEGS M' (d + 8 * Z.of_nat n) 0
    /\ (forall a : word, ~ (d + 8 * Z.of_nat n <= bv_unsigned a < d + 8 * Z.of_nat n + 8) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW Sap Olo Ohi O8 O0 Hfb Hb0 On O24 Hn Hk Dlo Dhi D8 DW DD Xn Dap1 Dap2 H2 H8 H9 H18 H19. unfold apart in *.
  pose proof (mask_range k ltac:(lia)) as MR.
  set (Vf := VAL R0 R sp o k (Z.of_nat n) fb d 0 0 0 (2 ^ k - 1)). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp o k (Z.of_nat n) fb d 0 0 0 (2 ^ k - 1) j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PBd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PBd.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PBd.kn0). { unfold know_ok, PBd.kn0. L5K.kn_all ZA. }
  destruct (PBd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PBd.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PBd.regs0 PBd.regs_out0 48 KSBd KSBd_ok HR Hag Hregs j Hj). }
  split. { unfold at_head. repeat split; rewrite (BG.out_reg PBd.regs_out0 E' R' _ Hregs) by lia; cbn [nth PBd.regs_out0]; try reflexivity.
           all: try L5K.wordE' ZA Hag.
           all: apply BG.word_of_unsigned; L5K.evalB' ZA Hag; first [apply k1_ident; lia | apply mask_ident; lia]. }
  change (SR.ps_cells PBd.ps0) with PBd.cells0 in Hcells. unfold PBd.cells0 in Hcells.
  split. { rewrite <- (Z.add_0_r (d + 8 * Z.of_nat n)). eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PBd.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

Lemma shBi_conc fx (R0 R : bvmap 5 word) M (sp o k fb : Z) :
  spok sp -> L5.writable RSEGS M (sp - 48) 48 -> apart (sp - 48) 48 o 32 ->
  1048576 <= o -> o + 32 <= 2 ^ 47 -> o mod 8 = 0 ->
  L5.u8_at RSEGS M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = false -> L5.u64_at RSEGS M (o + 8) 2 ->
  1 <= k <= 63 -> L5.writable RSEGS M (o + 16) 16 -> L5.defined M (o + 16) 8 -> L5.u64_at RSEGS M (o + 24) 0 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 48) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 k ->
  getr R (reg 18) = Z_to_bv 64 (o + 16) -> getr R (reg 19) = Z_to_bv 64 0 ->
  exists fx' R' M', msteps RSEGS (st fx R AFTER_RESIZE M) (st fx' R' LHEAD M')
    /\ (forall x, In x KSBi -> getr R' (reg x) = getr R (reg x)) /\ at_head R' sp o k (o + 16) 1 0
    /\ L5.u64_at RSEGS M' (o + 24) 0
    /\ (forall a : word, ~ (o + 24 <= bv_unsigned a < o + 32) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW Sap Olo Ohi O8 O0 Hfb Hb0 On Hk DW DD X1 H2 H8 H9 H18 H19. unfold apart in *.
  pose proof (mask_range k ltac:(lia)) as MR.
  set (Vf := VAL R0 R sp o k 1 fb (o + 16) 0 0 0 (2 ^ k - 1)). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp o k 1 fb (o + 16) 0 0 0 (2 ^ k - 1) j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PBi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PBi.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PBi.kn0). { unfold know_ok, PBi.kn0. L5K.kn_all ZA. }
  destruct (PBi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PBi.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PBi.regs0 PBi.regs_out0 48 KSBi KSBi_ok HR Hag Hregs j Hj). }
  split. { unfold at_head. repeat split; rewrite (BG.out_reg PBi.regs_out0 E' R' _ Hregs) by lia; cbn [nth PBi.regs_out0]; try reflexivity.
           all: try L5K.wordE' ZA Hag.
           all: try (apply BG.word_of_unsigned; L5K.evalB' ZA Hag; first [apply k1_ident; lia | apply mask_ident; lia]).
           all: f_equal; lia. }
  change (SR.ps_cells PBi.ps0) with PBi.cells0 in Hcells. unfold PBi.cells0 in Hcells.
  split. { eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PBi.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lo (k w : Z) : Z := BigModel.W.shl w k.
Definition hi (k w c : Z) : Z := Z.lor (Z.land (w / 2 ^ (64 - k)) (2 ^ k - 1)) c.
Lemma lo_ident k w : 1 <= k <= 63 -> (w * 2 ^ (k mod 64)) mod 2 ^ 64 = lo k w.
Proof. intros Hk. rewrite (Z.mod_small k 64) by lia. unfold lo, BigModel.W.shl, BigModel.W.wrap. rewrite BigFactsBase.M_val. reflexivity. Qed.
Lemma hi_ident k w c : 1 <= k <= 63 -> Z.lor (Z.land (w / 2 ^ ((64 - k) mod 64)) (2 ^ k - 1)) c = hi k w c.
Proof. intros Hk. rewrite (Z.mod_small (64 - k) 64) by lia. reflexivity. Qed.
Lemma lo_range k w : 0 <= lo k w < 2 ^ 64.
Proof. unfold lo, BigModel.W.shl, BigModel.W.wrap. rewrite BigFactsBase.M_val. apply Z.mod_pos_bound. lia. Qed.
Lemma hi_range k w c : 0 <= k <= 63 -> 0 <= w -> 0 <= c < 2 ^ 64 -> 0 <= hi k w c < 2 ^ 64.
Proof.
  intros Hk Hw Hc. unfold hi. pose proof (mask_range k Hk) as MR.
  pose proof (L5K.land_le_r (w / 2 ^ (64 - k)) (2 ^ k - 1) ltac:(apply Z.div_pos; [lia | apply pow_k_pos; lia]) ltac:(lia)) as A.
  pose proof (BigFactsBase.lor_range (Z.land (w / 2 ^ (64 - k)) (2 ^ k - 1)) c ltac:(unfold BigFactsBase.wordZ; rewrite BigFactsBase.M_val; lia) ltac:(unfold BigFactsBase.wordZ; rewrite BigFactsBase.M_val; lia)) as B.
  unfold BigFactsBase.wordZ, BigModel.W.lor in B. rewrite BigFactsBase.M_val in B. exact B.
Qed.

Lemma PSS_I : PI.PSS = [PI.ps0; PI.ps1]. Proof. vm_compute. reflexivity. Qed.
Lemma pc_I0 : SR.ps_pc PI.ps0 = LHEAD. Proof. reflexivity. Qed.
Lemma pc_I1 : SR.ps_pc PI.ps1 = LDONE. Proof. reflexivity. Qed.
Definition XI : expr := EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 39)) (EVar 37).
Definition eHI : expr := EAlu ALU_OR (EAlu ALU_AND (EAlu ALU_SRL (EVar 40) (EVar 45)) (EVar 46)) (EVar 41).
Definition eLO : expr := EAlu ALU_SLL (EVar 40) (EVar 34).
Lemma cells_I0 : SR.ps_cells PI.ps0 = [KRange (EVar 39) 2 300; KWord (SA XI 0) 8 eHI; KWord (SA XI (-8)) 8 eLO]. Proof. vm_compute. reflexivity. Qed.
Lemma cells_I1 : SR.ps_cells PI.ps1 = [KRange (EVar 39) 1 1; KWord (SA XI 0) 8 eHI; KWord (SA XI (-8)) 8 eLO]. Proof. vm_compute. reflexivity. Qed.

Lemma shI_conc fx (R0 R : bvmap 5 word) M (sp o k d : Z) (n i : nat) (w c : Z) :
  at_head R sp o k d i c -> (1 <= i <= n)%nat -> (n <= 300)%nat -> 1 <= k <= 63 -> 0 <= sp - 48 -> sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  4096 <= d -> d + 8 * Z.of_nat n + 8 <= 2 ^ 47 -> d mod 8 = 0 ->
  L5.writable RSEGS M (d + 8 * Z.of_nat i - 8) 16 -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i - 8) w -> 0 <= w < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  exists fx' R' M' (pc' : Z), msteps RSEGS (st fx R LHEAD M) (st fx' R' pc' M')
    /\ (forall x, In x KSI -> getr R' (reg x) = getr R (reg x))
    /\ ((pc' = LHEAD /\ (2 <= i)%nat) \/ (pc' = LDONE /\ i = 1%nat))
    /\ at_head R' sp o k d (i - 1) (lo k w)
    /\ L5.u64_at RSEGS M' (d + 8 * Z.of_nat i - 8) (lo k w) /\ L5.u64_at RSEGS M' (d + 8 * Z.of_nat i) (hi k w c)
    /\ (forall a : word, ~ (d + 8 * Z.of_nat i - 8 <= bv_unsigned a < d + 8 * Z.of_nat i + 8) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros (A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A18) Hi Hn Hk Hs1 Hs2 Ho Dlo Dhi D8 DW Xw Hw Hc.
  pose proof (mask_range k ltac:(lia)) as MR.
  set (Vf := VAL R0 R sp o k (Z.of_nat n) 0 d (Z.of_nat i) w c (2 ^ k - 1)). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp o k (Z.of_nat n) 0 d (Z.of_nat i) w c (2 ^ k - 1) j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PI.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PI.kn0). { unfold know_ok, PI.kn0. L5K.kn_all ZA. }
  destruct (PI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  rewrite PSS_I in Hnth. change PI.NX0 with 48%nat in Hag.
  assert (FR: forall a : word, ~ (d + 8 * Z.of_nat i - 8 <= bv_unsigned a < d + 8 * Z.of_nat i + 8) -> M' a = M a).
  { intros x Hx. apply Hfr. unfold PI.F0. L5K.outsideF ZA Hag. }
  (* [comment removed for export] *)
  assert (RB: forall (rs : list expr) (cs : list kentry) (lo' hi' : Z),
    SR.ps_regs ps = map (fun i => (i, nth i rs (ELit 0))) (seq 1 31) ->
    nth 10 rs (ELit 0) = EAlu ALU_ADD (EVar 39) (ELit (-1)) -> nth 11 rs (ELit 0) = eLO -> nth 12 rs (ELit 0) = EVar 45 -> nth 13 rs (ELit 0) = EVar 46 ->
    nth 14 rs (ELit 0) = EAlu ALU_ADD (EAlu ALU_ADD (EVar 37) (EMd M_MUL (ELit 8) (EVar 39))) (ELit (-16)) -> nth 18 rs (ELit 0) = EVar 37 ->
    nth 2 rs (ELit 0) = EAlu ALU_ADD (EVar 2) (ELit (-48)) -> nth 8 rs (ELit 0) = EVar 33 -> nth 9 rs (ELit 0) = EVar 34 ->
    SR.ps_cells ps = [KRange (EVar 39) lo' hi'; KWord (SA XI 0) 8 eHI; KWord (SA XI (-8)) 8 eLO] ->
    at_head R' sp o k d (i - 1) (lo k w)
    /\ L5.u64_at RSEGS M' (d + 8 * Z.of_nat i - 8) (lo k w) /\ L5.u64_at RSEGS M' (d + 8 * Z.of_nat i) (hi k w c)
    /\ lo' <= Z.of_nat i <= hi').
  { intros rs cs lo' hi' HPR N10 N11 N12 N13 N14 N18 N2 N8 N9 HC.
    assert (OUT: forall x, (0 < x < 32)%nat -> getr R' (reg x) = edenot E' (nth x rs (ELit 0))).
    { intros x Hx. apply (proj2 (Hregs x (nth x rs (ELit 0)) ltac:(rewrite HPR; apply in_map_iff; exists x; split; [reflexivity | apply in_seq; lia]))). }
    split. { unfold at_head. repeat split; rewrite OUT by lia.
      - rewrite N2. L5K.wordE' ZA Hag. - rewrite N8. L5K.wordE' ZA Hag. - rewrite N9. L5K.wordE' ZA Hag.
      - rewrite N10. apply BG.word_of_unsigned. L5K.evalE' ZA Hag.
      - rewrite N11. apply BG.word_of_unsigned. L5K.evalB' ZA Hag. apply lo_ident. lia.
      - rewrite N12. L5K.wordE' ZA Hag. - rewrite N13. L5K.wordE' ZA Hag.
      - rewrite N14. apply BG.word_of_unsigned. L5K.evalE' ZA Hag.
      - rewrite N18. L5K.wordE' ZA Hag. }
    rewrite HC in Hcells.
    split. { replace (d + 8 * Z.of_nat i - 8) with ((d + 8 * Z.of_nat i) + (-8)) by lia.
             eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalB' ZA Hag; apply lo_ident; lia]. }
    split. { rewrite <- (Z.add_0_r (d + 8 * Z.of_nat i)).
             eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalB' ZA Hag; apply hi_ident; lia]. }
    eapply (L5K.range_of_KRange RSEGS E' M'). apply Hcells. left; reflexivity. L5K.evalE' ZA Hag. }
  destruct (L5K.nth_error_pair _ _ _ _ Hnth) as [[-> ->] | [-> ->]].
  - destruct (RB PI.regs_out0 PI.cells0 2 300 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl cells_I0) as (AT & X1 & X2 & RG).
    exists fx', R', M', LHEAD. rewrite pc_I0 in Hms. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PI.regs0 PI.regs_out0 48 KSI KSI_ok0 HR Hag Hregs j Hj). }
    split. { left. split. reflexivity. lia. } split. exact AT. split. exact X1. split. exact X2. split. exact FR. exact Hgr.
  - destruct (RB PI.regs_out1 PI.cells1 1 1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl cells_I1) as (AT & X1 & X2 & RG).
    exists fx', R', M', LDONE. rewrite pc_I1 in Hms. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PI.regs0 PI.regs_out1 48 KSI KSI_ok1 HR Hag Hregs j Hj). }
    split. { right. split. reflexivity. lia. } split. exact AT. split. exact X1. split. exact X2. split. exact FR. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shR_conc fx (R0 R : bvmap 5 word) M (sp o : Z) :
  0 <= sp - 48 -> sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 48) -> getr R (reg 8) = Z_to_bv 64 o ->
  exists fx' R' M', msteps RSEGS (st fx R LDONE M) (st fx' R' L5RED.REDUCE M')
    /\ (forall x, In x KSR -> getr R' (reg x) = getr R (reg x)) /\ at_reduce R' sp o /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros Hs1 Hs2 Ho H2 H8.
  set (Vf := VAL R0 R sp o 0 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp o 0 0 0 0 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PR.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PR.kn0). { unfold know_ok, PR.kn0. apply Forall_nil. }
  destruct (PR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PR.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PR.regs0 PR.regs_out0 48 KSR KSR_ok HR Hag Hregs j Hj). }
  split. { unfold at_reduce, AFTER_REDUCE. repeat split; rewrite (BG.out_reg PR.regs_out0 E' R' _ Hregs) by lia; cbn [nth PR.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma shE_conc fx (R0 R : bvmap 5 word) M (sp o : Z) :
  spok sp -> L5.writable RSEGS M (sp - 48) 48 -> saved M sp R0 -> 0 <= o < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 48) -> getr R (reg 8) = Z_to_bv 64 o ->
  exists fx' R' M', msteps RSEGS (st fx R AFTER_REDUCE M) (st fx' R' RET M')
    /\ (forall x, In x KSE -> getr R' (reg x) = getr R (reg x)) /\ at_ret R0 R' sp o /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW SV Ho H2 H8. pose proof SV as (V1 & V2 & V3 & V4 & V5). unfold U in *.
  set (Vf := VAL R0 R sp o 0 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp o 0 0 0 0 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
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
Definition cells_at (M : word -> option byte) (d k : Z) (orig : list Z) (i n : nat) : Prop :=
  (forall j, (j < i)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat j) (nth_w orig j)) /\
  L5.u64_at RSEGS M (d + 8 * Z.of_nat i) (lo k (nth_w orig i)) /\
  (forall j, (i < j <= n)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat j) (BigFactsOps.shlG k orig j)).

Lemma shlG_0 k orig : BigFactsOps.shlG k orig 0 = lo k (nth_w orig 0).
Proof. reflexivity. Qed.
Lemma shlG_S k orig j : (1 <= j)%nat -> 1 <= k <= 63 -> 0 <= nth_w orig (j - 1)%nat ->
  BigFactsOps.shlG k orig j = hi k (nth_w orig (j - 1)%nat) (lo k (nth_w orig j)).
Proof.
  intros Hj Hk Hw. unfold BigFactsOps.shlG, hi, lo. destruct (Nat.ltb_spec 0 j). 2: lia.
  unfold BigModel.W.lor, BigModel.W.land, BigModel.W.shr. rewrite Z.lor_comm. f_equal. f_equal.
  unfold BigModel.W.sub, BigModel.W.shl, BigModel.W.wrap. rewrite BigFactsBase.M_val.
  pose proof (pow_k_pos k ltac:(lia)). pose proof (Z.pow_le_mono_r 2 k 63 ltac:(lia) ltac:(lia)).
  rewrite (Z.mod_small (1 * 2 ^ k)) by lia. rewrite Z.mod_small by lia. lia.
Qed.


Lemma sloop (i : nat) : forall fx (R0 R : bvmap 5 word) M (sp o k d : Z) (n : nat) (orig : list Z),
  at_head R sp o k d i (lo k (nth_w orig i)) -> (1 <= i <= n)%nat -> (n <= 300)%nat -> 1 <= k <= 63 ->
  0 <= sp - 48 -> sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 4096 <= d -> d + 8 * Z.of_nat n + 8 <= 2 ^ 47 -> d mod 8 = 0 ->
  L5.writable RSEGS M d (8 * Z.of_nat n + 8) -> words_ok orig ->
  cells_at M d k orig i n ->
  exists fx' R' M', msteps RSEGS (st fx R LHEAD M) (st fx' R' LDONE M')
    /\ (forall x, In x KSI -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 48) /\ getr R' (reg 8) = Z_to_bv 64 o
    /\ (forall j, (j <= n)%nat -> L5.u64_at RSEGS M' (d + 8 * Z.of_nat j) (BigFactsOps.shlG k orig j))
    /\ (forall a : word, ~ (d <= bv_unsigned a < d + 8 * Z.of_nat n + 8) -> M' a = M a) /\ mem_grows M M'.
Proof.
  induction i as [|i IH]; intros fx R0 R M sp o k d n orig AT Hi Hn Hk Hs1 Hs2 Ho Dlo Dhi D8 DW WO (C1 & C2 & C3). lia.
  pose proof (words_ok_nth orig i WO) as Wi. pose proof (words_ok_nth orig (S i) WO) as WSi.
  assert (WR16: L5.writable RSEGS M (d + 8 * Z.of_nat (S i) - 8) 16). { eapply L5.writable_sub. exact DW. lia. lia. }
  assert (Ci: L5.u64_at RSEGS M (d + 8 * Z.of_nat (S i) - 8) (nth_w orig i)). { replace (d + 8 * Z.of_nat (S i) - 8) with (d + 8 * Z.of_nat i) by lia. apply C1. lia. }
  destruct (shI_conc fx R0 R M sp o k d n (S i) (nth_w orig i) (lo k (nth_w orig (S i))) AT Hi Hn Hk Hs1 Hs2 Ho Dlo Dhi D8 WR16 Ci Wi (lo_range _ _))
    as (fx1 & R1 & M1 & pc1 & MS1 & K1 & EX & AT1 & X1 & X2 & FR1 & G1).
  replace (S i - 1)%nat with i in AT1 by lia.
  assert (DW1: L5.writable RSEGS M1 d (8 * Z.of_nat n + 8)) by (eapply L5.writable_grows; eauto).
  (* [comment removed for export] *)
  assert (CA1: cells_at M1 d k orig i n).
  { split. { intros j Hj. eapply (L5K.u64_at_keep RSEGS M M1). exact FR1. lia. lia. lia. apply C1. lia. }
    split. { replace (d + 8 * Z.of_nat i) with (d + 8 * Z.of_nat (S i) - 8) by lia. exact X1. }
    intros j Hj. destruct (Nat.eq_dec j (S i)) as [->|NE].
    - rewrite (shlG_S k orig (S i) ltac:(lia) Hk ltac:(replace (S i - 1)%nat with i by lia; lia)). replace (S i - 1)%nat with i by lia. exact X2.
    - eapply (L5K.u64_at_keep RSEGS M M1). exact FR1. lia. lia. lia. apply C3. lia. }
  destruct EX as [[-> Hge] | [-> Hone]].
  - (* [comment removed for export] *)
    destruct (IH fx1 R0 R1 M1 sp o k d n orig AT1 ltac:(lia) Hn Hk Hs1 Hs2 Ho Dlo Dhi D8 DW1 WO CA1) as (fx' & R' & M' & MS & K & B2 & B8 & CX & FR & G).
    exists fx', R', M'. split. eapply msteps_trans; eauto.
    split. { intros x Hx. rewrite (K x Hx). apply K1. exact Hx. }
    split. exact B2. split. exact B8. split. exact CX.
    split. { intros a Ha. rewrite (FR a Ha). apply FR1. lia. } eapply mem_grows_trans; eauto.
  - (* [comment removed for export] *)
    assert (I0 : i = 0%nat) by lia. subst i. exists fx1, R1, M1. split. exact MS1. split. exact K1.
    destruct AT1 as (B2 & B8 & _). split. exact B2. split. exact B8.
    split. { intros j Hj. destruct (Nat.eq_dec j 0) as [->|NE]. rewrite shlG_0. exact (proj1 (proj2 CA1)). apply (proj2 (proj2 CA1)). lia. }
    split. { intros a Ha. apply FR1. lia. } exact G1.
Qed.
End SCFG_2.


End L5SHL.
