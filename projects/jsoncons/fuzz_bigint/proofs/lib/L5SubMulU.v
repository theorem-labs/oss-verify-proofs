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
     Ub0_code_221b0_23098 Ub0_code_23138_2379c BigBranchUb0 BigLinkBase BigLinkGlue BigLinkGlueUb0 BigLinkInlBaseU BigLinkDqU BigLinkDivBaseU L5Defs L5Kn.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5SubMulU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5SMU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Module PA := LibSegZ_smuA.
Module PI := LibSegZ_smuI.
Module PK := LibSegZ_smuK.
Module PB := LibSegZ_smuB.
Module PJ := LibSegZ_smuJ.
Module PT := LibSegZ_smuT.
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition SUBMUL : Z := 0x22f68.
Definition L1HEAD : Z := 0x22fd0.
Definition SM_BR : Z := 0x23094.
Definition SM_BOR : Z := 0x23098.
Definition L2HEAD : Z := 0x230b8.
Definition L2DONE : Z := 0x230fc.
Definition SM_EPI : Z := 0x23114.
Definition SM_RET : Z := 0x23138.
Definition SM_SCRATCH : Z := 64.
End SCFG_1.


Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Section SCFG_2.
Context {SCFG_P : ScfgP}.

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition apart (x lx y ly : Z) : Prop := x + lx <= y \/ y + ly <= x.

(* [comment removed for export] *)
Record smctx (M : word -> option byte) (sp a b qa : Z) (n : nat) : Prop := SMC {
  c_sp : sp mod 16 = 0 /\ 1048640 <= sp <= 140737488355328;
  c_spw : L5.writable RSEGS M (sp - 64) 64;
  c_a : a mod 8 = 0 /\ 4096 <= a /\ a + 8 * Z.of_nat n + 8 <= 2 ^ 47;
  c_aw : L5.writable RSEGS M a (8 * Z.of_nat n + 8);
  c_ad : L5.defined M a (8 * Z.of_nat n + 8);
  c_b : b mod 8 = 0 /\ 4096 <= b /\ b + 8 * Z.of_nat n <= 2 ^ 47;
  c_bd : L5.defined M b (8 * Z.of_nat n);
  c_q : qa mod 8 = 0 /\ 4096 <= qa <= 140737488355320;
  c_qw : L5.writable RSEGS M qa 8;
  c_qd : L5.defined M qa 8;
  c_n : (1 <= n <= 300)%nat;
  c_ap1 : apart (sp - 64) 64 a (8 * Z.of_nat n + 8);
  c_ap2 : apart (sp - 64) 64 b (8 * Z.of_nat n);
  c_ap3 : apart (sp - 64) 64 qa 8;
  c_ap4 : apart a (8 * Z.of_nat n + 8) b (8 * Z.of_nat n);
  c_ap5 : apart a (8 * Z.of_nat n + 8) qa 8;
  c_ap6 : apart b (8 * Z.of_nat n) qa 8 }.

Lemma smctx_grows M M' sp a b qa n : smctx M sp a b qa n -> mem_grows M M' -> smctx M' sp a b qa n.
Proof.
  intros C G. destruct C. constructor; auto.
  - eapply L5.writable_grows; eauto. - eapply L5.writable_grows; eauto. - eapply L5.defined_grows; eauto.
  - eapply L5.defined_grows; eauto. - eapply L5.writable_grows; eauto. - eapply L5.defined_grows; eauto.
Qed.

(* [comment removed for export] *)
Definition sm_kept : list nat := [1; 3; 4; 24; 25; 26; 27]%nat.

(* [comment removed for export] *)
Definition sm_rest : list nat := [2; 8; 9; 18; 19; 20; 21; 22; 23]%nat.
Definition submul_post (M M' : word -> option byte) (sp a b qa : Z) (n : nat) (R R' : bvmap 5 word) : Prop :=
  (forall i, In i sm_kept -> getr R' (reg i) = getr R (reg i))
  /\ (forall i, In i sm_rest -> getr R' (reg i) = getr R (reg i))
  /\ regs_preserved R R'
  /\ smctx M' sp a b qa n
  /\ L5.frame_but [(sp - 64, 64); (a, 8 * Z.of_nat n + 8); (qa, 8)] M M' /\ mem_grows M M'.

Definition submul_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (sp a b qa r : Z) (n : nat),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 11%bv = Z_to_bv 64 a -> getr R 12%bv = Z_to_bv 64 b ->
    getr R 13%bv = Z_to_bv 64 (Z.of_nat n) -> getr R 14%bv = Z_to_bv 64 qa ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    smctx M sp a b qa n ->
    (forall (fx' : FPState) R' M', submul_post M M' sp a b qa n R R' -> srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model) K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx) R SUBMUL M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition VAL (R : bvmap 5 word) (sp a b qa : Z) (n i : nat) (x38 x39 x40 x41 : word) (k : nat) : word :=
  match k with
  | 2%nat => Z_to_bv 64 sp
  | 33%nat => Z_to_bv 64 a | 34%nat => Z_to_bv 64 b | 35%nat => Z_to_bv 64 (Z.of_nat n) | 36%nat => Z_to_bv 64 qa
  | 37%nat => Z_to_bv 64 (Z.of_nat i) | 38%nat => x38 | 39%nat => x39 | 40%nat => x40 | 41%nat => x41
  | _ => getr R (reg k)
  end.
Definition VZ (R : bvmap 5 word) (sp a b qa : Z) (n i : nat) (x38 x39 x40 x41 : word) (k : nat) : Z :=
  match k with
  | 2%nat => sp
  | 33%nat => a | 34%nat => b | 35%nat => Z.of_nat n | 36%nat => qa
  | 37%nat => Z.of_nat i | 38%nat => bv_unsigned x38 | 39%nat => bv_unsigned x39 | 40%nat => bv_unsigned x40 | 41%nat => bv_unsigned x41
  | _ => bv_unsigned (getr R (reg k))
  end.
Lemma VAL_VZ R sp a b qa n i x38 x39 x40 x41 :
  0 <= sp < 2 ^ 64 -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= qa < 2 ^ 64 -> (n <= 300)%nat -> (i <= 300)%nat ->
  forall k, bv_unsigned (ev (Env (VAL R sp a b qa n i x38 x39 x40 x41) (fun _ => [])) k) = VZ R sp a b qa n i x38 x39 x40 x41 k.
Proof.
  intros Hs Ha Hb Hq Hn Hi k. cbn [ev].
  unfold VAL, VZ.
  repeat (lazymatch goal with
          | |- bv_unsigned (match k with _ => _ end) = _ => destruct k as [|k]
          | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rl18 : (18%bv : bv 5) = reg 18. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl8 : (8%bv : bv 5) = reg 8. Proof. apply bv_eq. reflexivity. Qed.
Lemma br_22f5c fx R M :
  msteps RSEGS (st fx R 0x23094 M) (st fx R (if branch_taken BC_GEU (getr R (reg 18)) (getr R (reg 8)) then 0x23114 else 0x23098) M).
Proof.
  rewrite <- rl18, <- rl8.
  apply (@BDQU.br_site fx M R 0x23094 0x23114 (0x23094%bv : word) _ BC_GEU 18 8 _ eq_refl F_23094 eq_refl D_23094). reflexivity.
Qed.
Lemma ret_23000 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->
  msteps RSEGS (st fx R 0x23138 M) (st fx R r M).
Proof. intros H1 Hr He. apply (BDU.ret_to fx R M 0x23138 W_23138 r F_23138 eq_refl D_23138 H1 Hr He). Qed.

(* [comment removed for export] *)
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Definition saved (M : word -> option byte) (sp : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (U R0 8) /\ L5.u64_at RSEGS M (sp - 16) (U R0 9) /\ L5.u64_at RSEGS M (sp - 24) (U R0 18) /\
  L5.u64_at RSEGS M (sp - 32) (U R0 19) /\ L5.u64_at RSEGS M (sp - 40) (U R0 20) /\ L5.u64_at RSEGS M (sp - 48) (U R0 21) /\
  L5.u64_at RSEGS M (sp - 56) (U R0 22) /\ L5.u64_at RSEGS M (sp - 64) (U R0 23).
Lemma saved_keep M M' sp R0 lo hi :
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> M' x = M x) -> (sp <= lo \/ hi <= sp - 64 \/ hi <= lo) -> 64 <= sp -> sp <= 2 ^ 64 ->
  saved M sp R0 -> saved M' sp R0.
Proof.
  intros HF Hap H1 H2 (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  repeat split; (eapply (L5K.u64_at_keep RSEGS M M'); [exact HF | lia | lia | lia | eassumption]).
Qed.

Local Ltac intro_ctx C := destruct C as [Csp Cspw Ca Caw Cad Cb Cbd Cq Cqw Cqd Cn Cap1 Cap2 Cap3 Cap4 Cap5 Cap6]; unfold apart in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_A : list nat := Eval vm_compute in (BG.kept_list 48 PA.regs0 PA.regs_out).
Lemma KS_A_ok : BG.kept_ok 48 PA.regs0 PA.regs_out KS_A = true. Proof. vm_compute. reflexivity. Qed.
Lemma cells_A : SR.ps_cells PA.ps0 = [KWord (SA (EVar 2) (-64)) 8 (EVar 23); KWord (SA (EVar 2) (-56)) 8 (EVar 22); KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20); KWord (SA (EVar 2) (-32)) 8 (EVar 19); KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9); KWord (SA (EVar 2) (-8)) 8 (EVar 8)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition at_l1 (R : bvmap 5 word) (sp a b qa : Z) (n i : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R (reg 5) = Z_to_bv 64 1 /\ getr R (reg 7) = Z_to_bv 64 4294967295 /\
  getr R (reg 10) = Z_to_bv 64 (18446744073709551615 - a) /\ getr R (reg 11) = Z_to_bv 64 a /\ getr R (reg 12) = Z_to_bv 64 b /\
  getr R (reg 13) = Z_to_bv 64 (Z.of_nat n) /\ getr R (reg 14) = Z_to_bv 64 qa /\
  getr R (reg 15) = Z_to_bv 64 (8 * Z.of_nat i) /\ getr R (reg 16) = Z_to_bv 64 (Z.of_nat i) /\ getr R (reg 17) = Z_to_bv 64 1 /\
  getr R (reg 28) = Z_to_bv 64 1 /\ getr R (reg 29) = Z_to_bv 64 1 /\ getr R (reg 30) = Z_to_bv 64 1152921504606846974.

Lemma smA_conc fx R M (sp a b qa : Z) (n : nat) :
  smctx M sp a b qa n ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 11) = Z_to_bv 64 a -> getr R (reg 12) = Z_to_bv 64 b ->
  getr R (reg 13) = Z_to_bv 64 (Z.of_nat n) -> getr R (reg 14) = Z_to_bv 64 qa ->
  exists fx' R' M', msteps RSEGS (st fx R SUBMUL M) (st fx' R' L1HEAD M')
    /\ (forall x, In x KS_A -> getr R' (reg x) = getr R (reg x))
    /\ at_l1 R' sp a b qa n 0
    /\ saved M' sp R
    /\ (forall x : word, ~ (sp - 64 <= bv_unsigned x < sp) -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros C H2 H11 H12 H13 H14. intro_ctx C.
  set (Vf := VAL R sp a b qa n 0 (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9))).
  set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ R sp a b qa n 0 (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9)) k)
    by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PA.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PA.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PA.kn0). { unfold know_ok, PA.kn0. L5K.kn_all ZA. }
  destruct (PA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps0. change PA.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA.regs0 PA.regs_out 48 KS_A KS_A_ok HR Hag Hregs j Hj). }
  split. { unfold at_l1. repeat split.
    all: rewrite (BG.out_reg PA.regs_out E' R' _ Hregs) by lia; cbn [nth PA.regs_out PA.regs_out0]; L5K.wordE' ZA Hag. }
  rewrite cells_A in Hcells.
  split. { unfold saved, U. repeat split.
    all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PA.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_I : list nat := Eval vm_compute in (BG.kept_list 48 PI.regs0 PI.regs_out0).
Lemma KS_I_ok0 : BG.kept_ok 48 PI.regs0 PI.regs_out0 KS_I = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS_I_ok1 : BG.kept_ok 48 PI.regs0 PI.regs_out1 KS_I = true. Proof. vm_compute. reflexivity. Qed.
Lemma PSS_I : PI.PSS = [PI.ps0; PI.ps1]. Proof. vm_compute. reflexivity. Qed.
Lemma cells_I0 : exists cs, SR.ps_cells PI.ps0 = KRange (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit (-1)) (EVar 37))) 2 300 :: cs.
Proof. eexists. vm_compute. reflexivity. Qed.
Lemma cells_I1 : exists cs, SR.ps_cells PI.ps1 = KRange (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit (-1)) (EVar 37))) 1 1 :: cs.
Proof. eexists. vm_compute. reflexivity. Qed.
Lemma pc_I0 : SR.ps_pc PI.ps0 = 0x22fd0. Proof. reflexivity. Qed.
Lemma pc_I1 : SR.ps_pc PI.ps1 = 0x23094. Proof. reflexivity. Qed.

Lemma smI_conc fx R M (sp a b qa : Z) (n i : nat) :
  smctx M sp a b qa n -> at_l1 R sp a b qa n i -> (i < n)%nat ->
  exists fx' R' M' (pc' : Z), msteps RSEGS (st fx R L1HEAD M) (st fx' R' pc' M')
    /\ (forall x, In x KS_I -> getr R' (reg x) = getr R (reg x))
    /\ ((pc' = L1HEAD /\ (i + 1 < n)%nat /\ at_l1 R' sp a b qa n (S i)) \/ (pc' = SM_BR /\ (i + 1 = n)%nat))
    /\ (forall x : word, ~ (a + 8 * Z.of_nat i <= bv_unsigned x < a + 8 * Z.of_nat i + 16) -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros C AT Hi. intro_ctx C. destruct AT as (A2 & A5 & A7 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A28 & A29 & A30).
  set (Vf := VAL R sp a b qa n i (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9))).
  set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ R sp a b qa n i (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9)) k)
    by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PI.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PI.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PI.kn0). { unfold know_ok, PI.kn0. L5K.kn_all ZA. }
  destruct (PI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  rewrite PSS_I in Hnth. change PI.NX0 with 48%nat in Hag.
  assert (FR: forall x : word, ~ (a + 8 * Z.of_nat i <= bv_unsigned x < a + 8 * Z.of_nat i + 16) -> M' x = M x).
  { intros x Hx. apply Hfr. unfold PI.F0. L5K.outsideF ZA Hag. }
  destruct (L5K.nth_error_pair _ _ _ _ Hnth) as [[-> ->] | [-> ->]].
  - exists fx', R', M', L1HEAD. rewrite pc_I0 in Hms. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PI.regs0 PI.regs_out0 48 KS_I KS_I_ok0 HR Hag Hregs j Hj). }
    split.
    { left. split. reflexivity.
      destruct cells_I0 as [c Hc]. rewrite Hc in Hcells.
      assert (RG: 2 <= Z.of_nat n - Z.of_nat i <= 300).
      { eapply (L5K.range_of_KRange RSEGS E' M'). apply Hcells. left; reflexivity. L5K.evalE' ZA Hag. }
      split. lia.
      unfold at_l1. repeat split.
      all: rewrite (BG.out_reg PI.regs_out0 E' R' _ Hregs) by lia; cbn [nth PI.regs_out0]; L5K.wordE' ZA Hag. }
    split. exact FR. exact Hgr.
  - exists fx', R', M', SM_BR. rewrite pc_I1 in Hms. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PI.regs0 PI.regs_out1 48 KS_I KS_I_ok1 HR Hag Hregs j Hj). }
    split.
    { right. split. reflexivity.
      destruct cells_I1 as [c Hc]. rewrite Hc in Hcells.
      assert (RG: 1 <= Z.of_nat n - Z.of_nat i <= 1).
      { eapply (L5K.range_of_KRange RSEGS E' M'). apply Hcells. left; reflexivity. L5K.evalE' ZA Hag. }
      lia. }
    split. exact FR. exact Hgr.
Qed.

Definition KS_L : list nat := [1; 2; 3; 4; 5; 7; 10; 11; 12; 13; 14; 17; 24; 25; 26; 27; 28; 29; 30]%nat.

Lemma loop1 (m : nat) : forall fx R M (sp a b qa : Z) (n i : nat),
  (m = n - i)%nat -> smctx M sp a b qa n -> at_l1 R sp a b qa n i -> (i < n)%nat ->
  exists fx' R' M', msteps RSEGS (st fx R L1HEAD M) (st fx' R' SM_BR M')
    /\ (forall x, In x KS_L -> getr R' (reg x) = getr R (reg x))
    /\ (forall x : word, ~ (a <= bv_unsigned x < a + 8 * Z.of_nat n + 8) -> M' x = M x) /\ mem_grows M M'.
Proof.
  induction m as [|m IH]; intros fx R M sp a b qa n i Hm C AT Hi. lia.
  destruct (smI_conc fx R M sp a b qa n i C AT Hi) as (fx1 & R1 & M1 & pc1 & MS1 & K1 & EX & FR1 & G1).
  assert (KL: forall x, In x KS_L -> In x KS_I) by (apply L5K.incl_b; vm_compute; reflexivity).
  destruct EX as [(-> & Hlt & AT1) | (-> & Heq)].
  - destruct (IH fx1 R1 M1 sp a b qa n (S i) ltac:(lia) (smctx_grows _ _ _ _ _ _ _ C G1) AT1 ltac:(lia))
      as (fx' & R' & M' & MS & K & FR & G).
    exists fx', R', M'. split. eapply msteps_trans; eauto.
    split. { intros x Hx. rewrite (K x Hx). apply K1. apply KL. exact Hx. }
    split. { intros x Hx. rewrite (FR x Hx). apply FR1. lia. }
    eapply mem_grows_trans; eauto.
  - exists fx1, R1, M1. split. exact MS1.
    split. { intros x Hx. apply K1. apply KL. exact Hx. }
    split. { intros x Hx. apply FR1. lia. } exact G1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition VALK (R0 R : bvmap 5 word) (sp a b qa : Z) (n : nat) (k : nat) : word :=
  match k with
  | 2%nat => Z_to_bv 64 sp | 33%nat => Z_to_bv 64 a | 34%nat => Z_to_bv 64 b | 35%nat => Z_to_bv 64 (Z.of_nat n) | 36%nat => Z_to_bv 64 qa
  | 8%nat => getr R0 (reg 8) | 9%nat => getr R0 (reg 9) | 18%nat => getr R0 (reg 18) | 19%nat => getr R0 (reg 19)
  | 20%nat => getr R0 (reg 20) | 21%nat => getr R0 (reg 21) | 22%nat => getr R0 (reg 22) | 23%nat => getr R0 (reg 23)
  | 40%nat => getr R (reg 8) | 41%nat => getr R (reg 9) | 42%nat => getr R (reg 18) | 43%nat => getr R (reg 19)
  | 44%nat => getr R (reg 20) | 45%nat => getr R (reg 21) | 46%nat => getr R (reg 22) | 47%nat => getr R (reg 23)
  | _ => getr R (reg k)
  end.
Definition VZK (R0 R : bvmap 5 word) (sp a b qa : Z) (n : nat) (k : nat) : Z :=
  match k with
  | 2%nat => sp | 33%nat => a | 34%nat => b | 35%nat => Z.of_nat n | 36%nat => qa
  | 8%nat => U R0 8 | 9%nat => U R0 9 | 18%nat => U R0 18 | 19%nat => U R0 19 | 20%nat => U R0 20 | 21%nat => U R0 21 | 22%nat => U R0 22 | 23%nat => U R0 23
  | 40%nat => U R 8 | 41%nat => U R 9 | 42%nat => U R 18 | 43%nat => U R 19 | 44%nat => U R 20 | 45%nat => U R 21 | 46%nat => U R 22 | 47%nat => U R 23
  | _ => U R k
  end.
Lemma VALK_VZK R0 R sp a b qa n : 0 <= sp < 2 ^ 64 -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= qa < 2 ^ 64 -> (n <= 300)%nat ->
  forall k, bv_unsigned (ev (Env (VALK R0 R sp a b qa n) (fun _ => [])) k) = VZK R0 R sp a b qa n k.
Proof.
  intros Hs Ha Hb Hq Hn k. cbn [ev]. unfold VALK, VZK, U.
  repeat (lazymatch goal with
          | |- bv_unsigned (match k with _ => _ end) = _ => destruct k as [|k]
          | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.

Definition KS_K : list nat := Eval vm_compute in (BG.kept_list 48 PK.regs0 PK.regs_out0).
Lemma KS_K_ok : BG.kept_ok 48 PK.regs0 PK.regs_out0 KS_K = true. Proof. vm_compute. reflexivity. Qed.

Lemma smK_conc fx R0 R M (sp a b qa : Z) (n : nat) :
  smctx M sp a b qa n -> getr R (reg 2) = Z_to_bv 64 (sp - 64) -> saved M sp R0 ->
  exists fx' R' M', msteps RSEGS (st fx R SM_EPI M) (st fx' R' SM_RET M')
    /\ (forall x, In x KS_K -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 2) = Z_to_bv 64 sp
    /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23]%nat -> getr R' (reg x) = getr R0 (reg x))
    /\ (forall x : word, M' x = M x) /\ mem_grows M M'.
Proof.
  intros C H2 SV. intro_ctx C. pose proof SV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  set (Vf := VALK R0 R sp a b qa n). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZK R0 R sp a b qa n k) by (apply VALK_VZK; lia). unfold VZK, U in ZA.
  assert (HR: regs_ok E PK.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PK.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PK.kn0).
  { unfold know_ok, PK.kn0. unfold U in *. L5K.kn_all ZA.
    all: try (rewrite Z.add_opp_r; assumption). }
  destruct (PK.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PK.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PK.regs0 PK.regs_out0 48 KS_K KS_K_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PK.regs_out0 E' R' 2 Hregs) by lia. cbn [nth PK.regs_out0]. L5K.wordE' ZA Hag. }
  split. { intros x Hx. cbn in Hx.
    repeat (destruct Hx as [<-|Hx]; [rewrite (BG.out_reg PK.regs_out0 E' R' _ Hregs) by lia; cbn [nth PK.regs_out0 edenot];
                                      rewrite <- (proj1 Hag) by lia; reflexivity |]). destruct Hx. }
  split. { intros x. apply Hfr. unfold PK.F0. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_B : list nat := Eval vm_compute in (BG.kept_list 48 PB.regs0 PB.regs_out0).
Lemma KS_B_ok : BG.kept_ok 48 PB.regs0 PB.regs_out0 KS_B = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition at_l2 (R : bvmap 5 word) (sp a b qa : Z) (n j : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R (reg 5) = Z_to_bv 64 (a + 8 * Z.of_nat j) /\
  getr R (reg 10) = Z_to_bv 64 (18446744073709551615 - a) /\ getr R (reg 11) = Z_to_bv 64 a /\
  getr R (reg 12) = Z_to_bv 64 (b + 8 * Z.of_nat j) /\ getr R (reg 13) = Z_to_bv 64 (Z.of_nat n) /\
  getr R (reg 14) = Z_to_bv 64 (18446744073709551615 - b) /\ getr R (reg 15) = Z_to_bv 64 (8 * Z.of_nat j) /\
  getr R (reg 16) = Z_to_bv 64 (Z.of_nat j).

Lemma smB_conc fx R M (sp a b qa : Z) (n : nat) :
  smctx M sp a b qa n ->
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 10) = Z_to_bv 64 (18446744073709551615 - a) -> getr R (reg 11) = Z_to_bv 64 a ->
  getr R (reg 12) = Z_to_bv 64 b -> getr R (reg 13) = Z_to_bv 64 (Z.of_nat n) -> getr R (reg 14) = Z_to_bv 64 qa ->
  exists fx' R' M', msteps RSEGS (st fx R SM_BOR M) (st fx' R' L2HEAD M')
    /\ (forall x, In x KS_B -> getr R' (reg x) = getr R (reg x))
    /\ at_l2 R' sp a b qa n 0
    /\ (forall x : word, ~ (qa <= bv_unsigned x < qa + 8) -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros C H2 H10 H11 H12 H13 H14. intro_ctx C.
  set (Vf := VAL R sp a b qa n 0 (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9))).
  set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ R sp a b qa n 0 (getr R (reg 6)) (getr R (reg 17)) (getr R (reg 8)) (getr R (reg 9)) k)
    by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PB.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PB.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PB.kn0). { unfold know_ok, PB.kn0. L5K.kn_all ZA. }
  destruct (PB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PB.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PB.regs0 PB.regs_out0 48 KS_B KS_B_ok HR Hag Hregs j Hj). }
  split. { unfold at_l2. repeat split.
    all: rewrite (BG.out_reg PB.regs_out0 E' R' _ Hregs) by lia; cbn [nth PB.regs_out PB.regs_out0]; L5K.wordE' ZA Hag. }
  split. { intros x Hx. apply Hfr. unfold PB.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_J : list nat := Eval vm_compute in (BG.kept_list 48 PJ.regs0 PJ.regs_out0).
Lemma KS_J_ok0 : BG.kept_ok 48 PJ.regs0 PJ.regs_out0 KS_J = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS_J_ok1 : BG.kept_ok 48 PJ.regs0 PJ.regs_out1 KS_J = true. Proof. vm_compute. reflexivity. Qed.
Lemma PSS_J : PJ.PSS = [PJ.ps0; PJ.ps1]. Proof. vm_compute. reflexivity. Qed.
Lemma cells_J0 : exists cs, SR.ps_cells PJ.ps0 = KRange (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit (-1)) (EVar 37))) 2 300 :: cs.
Proof. eexists. vm_compute. reflexivity. Qed.
Lemma cells_J1 : exists cs, SR.ps_cells PJ.ps1 = KRange (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit (-1)) (EVar 37))) 1 1 :: cs.
Proof. eexists. vm_compute. reflexivity. Qed.
Lemma pc_J0 : SR.ps_pc PJ.ps0 = 0x230b8. Proof. reflexivity. Qed.
Lemma pc_J1 : SR.ps_pc PJ.ps1 = 0x230fc. Proof. reflexivity. Qed.

Lemma smJ_conc fx R M (sp a b qa : Z) (n j : nat) :
  smctx M sp a b qa n -> at_l2 R sp a b qa n j -> (j < n)%nat ->
  exists fx' R' M' (pc' : Z), msteps RSEGS (st fx R L2HEAD M) (st fx' R' pc' M')
    /\ (forall x, In x KS_J -> getr R' (reg x) = getr R (reg x))
    /\ ((pc' = L2HEAD /\ (j + 1 < n)%nat /\ at_l2 R' sp a b qa n (S j)) \/ (pc' = L2DONE /\ (j + 1 = n)%nat))
    /\ (forall x : word, ~ (a + 8 * Z.of_nat j <= bv_unsigned x < a + 8 * Z.of_nat j + 8) -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros C AT Hj. intro_ctx C. destruct AT as (A2 & A5 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  set (Vf := VAL R sp a b qa n j (getr R (reg 17)) (getr R (reg 6)) (getr R (reg 8)) (getr R (reg 9))).
  set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZ R sp a b qa n j (getr R (reg 17)) (getr R (reg 6)) (getr R (reg 8)) (getr R (reg 9)) k)
    by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PJ.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PJ.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PJ.kn0). { unfold know_ok, PJ.kn0. L5K.kn_all ZA. }
  destruct (PJ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  rewrite PSS_J in Hnth. change PJ.NX0 with 48%nat in Hag.
  assert (FR: forall x : word, ~ (a + 8 * Z.of_nat j <= bv_unsigned x < a + 8 * Z.of_nat j + 8) -> M' x = M x).
  { intros x Hx. apply Hfr. unfold PJ.F0. L5K.outsideF ZA Hag. }
  destruct (L5K.nth_error_pair _ _ _ _ Hnth) as [[-> ->] | [-> ->]].
  - exists fx', R', M', L2HEAD. rewrite pc_J0 in Hms. split. exact Hms.
    split. { intros i Hi. apply (BG.kept_regs E E' R R' PJ.regs0 PJ.regs_out0 48 KS_J KS_J_ok0 HR Hag Hregs i Hi). }
    split.
    { left. split. reflexivity.
      destruct cells_J0 as [c Hc]. rewrite Hc in Hcells.
      assert (RG: 2 <= Z.of_nat n - Z.of_nat j <= 300).
      { eapply (L5K.range_of_KRange RSEGS E' M'). apply Hcells. left; reflexivity. L5K.evalE' ZA Hag. }
      split. lia.
      unfold at_l2. repeat split.
      all: rewrite (BG.out_reg PJ.regs_out0 E' R' _ Hregs) by lia; cbn [nth PJ.regs_out0]; L5K.wordE' ZA Hag. }
    split. exact FR. exact Hgr.
  - exists fx', R', M', L2DONE. rewrite pc_J1 in Hms. split. exact Hms.
    split. { intros i Hi. apply (BG.kept_regs E E' R R' PJ.regs0 PJ.regs_out1 48 KS_J KS_J_ok1 HR Hag Hregs i Hi). }
    split.
    { right. split. reflexivity.
      destruct cells_J1 as [c Hc]. rewrite Hc in Hcells.
      assert (RG: 1 <= Z.of_nat n - Z.of_nat j <= 1).
      { eapply (L5K.range_of_KRange RSEGS E' M'). apply Hcells. left; reflexivity. L5K.evalE' ZA Hag. }
      lia. }
    split. exact FR. exact Hgr.
Qed.

Definition KS_L2 : list nat := [1; 2; 3; 4; 8; 9; 10; 11; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

Lemma loop2 (m : nat) : forall fx R M (sp a b qa : Z) (n j : nat),
  (m = n - j)%nat -> smctx M sp a b qa n -> at_l2 R sp a b qa n j -> (j < n)%nat ->
  exists fx' R' M', msteps RSEGS (st fx R L2HEAD M) (st fx' R' L2DONE M')
    /\ (forall x, In x KS_L2 -> getr R' (reg x) = getr R (reg x))
    /\ (forall x : word, ~ (a <= bv_unsigned x < a + 8 * Z.of_nat n) -> M' x = M x) /\ mem_grows M M'.
Proof.
  induction m as [|m IH]; intros fx R M sp a b qa n j Hm C AT Hj. lia.
  destruct (smJ_conc fx R M sp a b qa n j C AT Hj) as (fx1 & R1 & M1 & pc1 & MS1 & K1 & EX & FR1 & G1).
  assert (KL: forall x, In x KS_L2 -> In x KS_J) by (apply L5K.incl_b; vm_compute; reflexivity).
  destruct EX as [(-> & Hlt & AT1) | (-> & Heq)].
  - destruct (IH fx1 R1 M1 sp a b qa n (S j) ltac:(lia) (smctx_grows _ _ _ _ _ _ _ C G1) AT1 ltac:(lia))
      as (fx' & R' & M' & MS & K & FR & G).
    exists fx', R', M'. split. eapply msteps_trans; eauto.
    split. { intros x Hx. rewrite (K x Hx). apply K1. apply KL. exact Hx. }
    split. { intros x Hx. rewrite (FR x Hx). apply FR1. lia. }
    eapply mem_grows_trans; eauto.
  - exists fx1, R1, M1. split. exact MS1.
    split. { intros x Hx. apply K1. apply KL. exact Hx. }
    split. { intros x Hx. apply FR1. lia. } exact G1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_T : list nat := Eval vm_compute in (BG.kept_list 48 PT.regs0 PT.regs_out0).
Lemma KS_T_ok : BG.kept_ok 48 PT.regs0 PT.regs_out0 KS_T = true. Proof. vm_compute. reflexivity. Qed.

Lemma smT_conc fx R0 R M (sp a b qa : Z) (n : nat) :
  smctx M sp a b qa n ->
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 10) = Z_to_bv 64 (18446744073709551615 - a) ->
  getr R (reg 11) = Z_to_bv 64 a -> getr R (reg 13) = Z_to_bv 64 (Z.of_nat n) -> saved M sp R0 ->
  exists fx' R' M', msteps RSEGS (st fx R L2DONE M) (st fx' R' SM_RET M')
    /\ (forall x, In x KS_T -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 2) = Z_to_bv 64 sp
    /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23]%nat -> getr R' (reg x) = getr R0 (reg x))
    /\ (forall x : word, ~ (a + 8 * Z.of_nat n <= bv_unsigned x < a + 8 * Z.of_nat n + 8) -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros C H2 H10 H11 H13 SV. intro_ctx C. pose proof SV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  set (Vf := VALK R0 R sp a b qa n). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall k, bv_unsigned (ev E k) = VZK R0 R sp a b qa n k) by (apply VALK_VZK; lia). unfold VZK, U in ZA.
  assert (HR: regs_ok E PT.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PT.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PT.kn0).
  { unfold know_ok, PT.kn0. unfold U in *. L5K.kn_all ZA.
    all: try (rewrite Z.add_opp_r; assumption). }
  destruct (PT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PT.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PT.regs0 PT.regs_out0 48 KS_T KS_T_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PT.regs_out0 E' R' 2 Hregs) by lia. cbn [nth PT.regs_out0]. L5K.wordE' ZA Hag. }
  split. { intros x Hx. cbn in Hx.
    repeat (destruct Hx as [<-|Hx]; [rewrite (BG.out_reg PT.regs_out0 E' R' _ Hregs) by lia; cbn [nth PT.regs_out0 edenot];
                                      rewrite <- (proj1 Hag) by lia; reflexivity |]). destruct Hx. }
  split. { intros x Hx. apply Hfr. unfold PT.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kept_regs_preserved R R' :
  (forall i, In i sm_kept -> getr R' (reg i) = getr R (reg i)) ->
  (forall i, In i sm_rest -> getr R' (reg i) = getr R (reg i)) ->
  regs_preserved R R'.
Proof.
  intros K K2 x Hx. rewrite <- (AX2S.ridx_roundtrip x).
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; first [apply K; cbn; tauto | apply K2; cbn; tauto] |]). destruct Hx.
Qed.

Theorem submul_run (fx : FPState) R M (sp a b qa r : Z) (n : nat) :
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 11) = Z_to_bv 64 a -> getr R (reg 12) = Z_to_bv 64 b ->
  getr R (reg 13) = Z_to_bv 64 (Z.of_nat n) -> getr R (reg 14) = Z_to_bv 64 qa ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  smctx M sp a b qa n ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R SUBMUL M) (st fx' R' r M') /\ submul_post M M' sp a b qa n R R'.
Proof.
  intros H2 H11 H12 H13 H14 H1 [Hr He] C. pose proof C as C0. intro_ctx C.
  destruct (smA_conc fx R M sp a b qa n C0 H2 H11 H12 H13 H14) as (fx1 & R1 & M1 & MS1 & K1 & AT1 & SV1 & FR1 & G1).
  pose proof (smctx_grows _ _ _ _ _ _ _ C0 G1) as C1.
  destruct (loop1 (n - 0) fx1 R1 M1 sp a b qa n 0 eq_refl C1 AT1 ltac:(lia)) as (fx2 & R2 & M2 & MS2 & K2 & FR2 & G2).
  pose proof (smctx_grows _ _ _ _ _ _ _ C1 G2) as C2.
  assert (SV2: saved M2 sp R). { eapply (saved_keep M1 M2). exact FR2. lia. lia. lia. exact SV1. }
  destruct AT1 as (A2 & _ & _ & A10 & A11 & A12 & A13 & A14 & _).
  assert (B2: getr R2 (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite (K2 2%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact A2).
  assert (B10: getr R2 (reg 10) = Z_to_bv 64 (18446744073709551615 - a)) by (rewrite (K2 10%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact A10).
  assert (B11: getr R2 (reg 11) = Z_to_bv 64 a) by (rewrite (K2 11%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact A11).
  assert (B12: getr R2 (reg 12) = Z_to_bv 64 b) by (rewrite (K2 12%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact A12).
  assert (B13: getr R2 (reg 13) = Z_to_bv 64 (Z.of_nat n)) by (rewrite (K2 13%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact A13).
  assert (B14: getr R2 (reg 14) = Z_to_bv 64 qa) by (rewrite (K2 14%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact A14).
  assert (B1: getr R2 (reg 1) = Z_to_bv 64 r).
  { rewrite (K2 1%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (K1 1%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H1. }
  assert (PACK: forall (fx' : FPState) R' M',
    (forall i, In i sm_kept -> getr R' (reg i) = getr R2 (reg i)) ->
    getr R' (reg 2) = Z_to_bv 64 sp -> (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23]%nat -> getr R' (reg x) = getr R (reg x)) ->
    smctx M' sp a b qa n ->
    (forall x : word, ~ (a <= bv_unsigned x < a + 8 * Z.of_nat n + 8) -> ~ (qa <= bv_unsigned x < qa + 8) -> M' x = M2 x) -> mem_grows M2 M' ->
    submul_post M M' sp a b qa n R R').
  { intros fx' R' M' K E2 E8 C' FR G.
    assert (KK: forall i, In i sm_kept -> getr R' (reg i) = getr R (reg i)).
    { intros i Hi. rewrite (K i Hi). rewrite (K2 i). apply K1. apply (L5K.incl_b sm_kept KS_A ltac:(vm_compute; reflexivity)); exact Hi.
      apply (L5K.incl_b sm_kept KS_L ltac:(vm_compute; reflexivity)); exact Hi. }
    assert (KR: forall i, In i sm_rest -> getr R' (reg i) = getr R (reg i)).
    { intros i Hi. destruct Hi as [<-|Hi]. rewrite E2, H2; reflexivity. apply E8. exact Hi. }
    split. exact KK. split. exact KR.
    split. { apply kept_regs_preserved. exact KK. exact KR. }
    split. exact C'.
    split. { intros x Hx. rewrite FR. rewrite FR2. apply FR1.
             all: intros Hin.
             apply (Hx (sp - 64, 64)); [left; reflexivity | unfold L5.in_rng; cbn; lia].
             apply (Hx (a, 8 * Z.of_nat n + 8)); [right; left; reflexivity | unfold L5.in_rng; cbn; lia].
             apply (Hx (a, 8 * Z.of_nat n + 8)); [right; left; reflexivity | unfold L5.in_rng; cbn; lia].
             apply (Hx (qa, 8)); [right; right; left; reflexivity | unfold L5.in_rng; cbn; lia]. }
    eapply mem_grows_trans. exact G1. eapply mem_grows_trans. exact G2. exact G. }
  pose proof (br_22f5c fx2 R2 M2) as MB.
  destruct (branch_taken BC_GEU (getr R2 (reg 18)) (getr R2 (reg 8))).
  - (* [comment removed for export] *)
    destruct (smK_conc fx2 R R2 M2 sp a b qa n C2 B2 SV2) as (fx3 & R3 & M3 & MS3 & K3 & E2 & E8 & MM3 & G3).
    pose proof (ret_23000 fx3 R3 M3 r ltac:(rewrite (K3 1%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact B1) Hr He) as MS4.
    exists fx3, R3, M3. split.
    { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact MB. eapply msteps_trans. exact MS3. exact MS4. }
    apply (PACK fx3 R3 M3). { intros i Hi. apply K3. apply (L5K.incl_b sm_kept KS_K ltac:(vm_compute; reflexivity)); exact Hi. } exact E2. exact E8.
    { eapply smctx_grows. exact C2. exact G3. } { intros x _ _. apply MM3. } exact G3.
  - (* [comment removed for export] *)
    destruct (smB_conc fx2 R2 M2 sp a b qa n C2 B2 B10 B11 B12 B13 B14) as (fx3 & R3 & M3 & MS3 & K3 & AT3 & FR3 & G3).
    pose proof (smctx_grows _ _ _ _ _ _ _ C2 G3) as C3.
    destruct (loop2 (n - 0) fx3 R3 M3 sp a b qa n 0 eq_refl C3 AT3 ltac:(lia)) as (fx4 & R4 & M4 & MS4 & K4 & FR4 & G4).
    pose proof (smctx_grows _ _ _ _ _ _ _ C3 G4) as C4.
    destruct AT3 as (D2 & _ & D10 & D11 & _ & D13 & _).
    assert (SV4: saved M4 sp R).
    { eapply (saved_keep M3 M4). exact FR4. lia. lia. lia. eapply (saved_keep M2 M3). exact FR3. lia. lia. lia. exact SV2. }
    destruct (smT_conc fx4 R R4 M4 sp a b qa n C4
                ltac:(rewrite (K4 2%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact D2)
                ltac:(rewrite (K4 10%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact D10)
                ltac:(rewrite (K4 11%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact D11)
                ltac:(rewrite (K4 13%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact D13) SV4)
      as (fx5 & R5 & M5 & MS5 & K5 & E2 & E8 & FR5 & G5).
    assert (B1': getr R5 (reg 1) = Z_to_bv 64 r).
    { rewrite (K5 1%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (K4 1%nat) by (apply L5K.in_b; vm_compute; reflexivity).
      rewrite (K3 1%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact B1. }
    pose proof (ret_23000 fx5 R5 M5 r B1' Hr He) as MS6.
    exists fx5, R5, M5. split.
    { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact MB.
      eapply msteps_trans. exact MS3. eapply msteps_trans. exact MS4. eapply msteps_trans. exact MS5. exact MS6. }
    apply (PACK fx5 R5 M5).
    { intros i Hi. rewrite (K5 i), (K4 i). apply K3.
      apply (L5K.incl_b sm_kept KS_B ltac:(vm_compute; reflexivity)); exact Hi.
      apply (L5K.incl_b sm_kept KS_L2 ltac:(vm_compute; reflexivity)); exact Hi.
      apply (L5K.incl_b sm_kept KS_T ltac:(vm_compute; reflexivity)); exact Hi. }
    exact E2. exact E8. { eapply smctx_grows. exact C4. exact G5. }
    { intros x Ha Hq. rewrite FR5 by lia. rewrite FR4 by lia. apply FR3. exact Hq. }
    eapply mem_grows_trans. exact G3. eapply mem_grows_trans. exact G4. exact G5.
Qed.

(* [comment removed for export] *)
Lemma r2 : (2%bv : bv 5) = reg 2. Proof. apply bv_eq; reflexivity. Qed.
Lemma r1 : (1%bv : bv 5) = reg 1. Proof. apply bv_eq; reflexivity. Qed.
Lemma r11 : (11%bv : bv 5) = reg 11. Proof. apply bv_eq; reflexivity. Qed.
Lemma r12 : (12%bv : bv 5) = reg 12. Proof. apply bv_eq; reflexivity. Qed.
Lemma r13 : (13%bv : bv 5) = reg 13. Proof. apply bv_eq; reflexivity. Qed.
Lemma r14 : (14%bv : bv 5) = reg 14. Proof. apply bv_eq; reflexivity. Qed.

Theorem submul_ok : submul_spec.
Proof.
  intros fx R M model K sp a b qa r n Hh Hl H2 H11 H12 H13 H14 H1 Hra C HK. unfold cfg.
  rewrite r2 in H2. rewrite r1 in H1. rewrite r11 in H11. rewrite r12 in H12. rewrite r13 in H13. rewrite r14 in H14.
  eapply (L5.run_cps RSEGS (fun _ R' M' => submul_post M M' sp a b qa n R R')). exact Hh. exact Hl.
  - exact (submul_run fx R M sp a b qa r n H2 H11 H12 H13 H14 H1 Hra C).
  - intros fx' R' M' HP. apply HK. exact HP.
Qed.
End SCFG_2.


End L5SMU.
