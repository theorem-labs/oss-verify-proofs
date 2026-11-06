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
     Ub0_code_23138_2379c BigBranchUb0 BigLinkBase BigLinkGlue BigLinkInlBaseU BigLinkDqU BigLinkDivBaseU L5Defs L5Kn
     L5Core L5CoreSpecsU L5Words L5ReduceU L5ReduceGU L5DDmul.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5MulMU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5MULMU.
Import L5CSU. Import L5W.
Module PAi := LibSegZ_mmuAi. Module PAd := LibSegZ_mmuAd. Module PBd := LibSegZ_mmuBd. Module PBi := LibSegZ_mmuBi.
Module PI := LibSegZ_mmuI. Module PR := LibSegZ_mmuR. Module PE := LibSegZ_mmuE.
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition MULM : Z := 0x233d0.
Definition AFTER_RESIZE : Z := 0x23448. Definition LHEAD : Z := 0x23494. Definition LDONE : Z := 0x23534.
Definition AFTER_REDUCE : Z := 0x23550. Definition RET : Z := 0x2358c.
Definition FRAME : Z := 144.
Definition MULM_SCR : Z := 144 + RESIZE_SCR.
Definition MASK32 : Z := 4294967295.
End SCFG_1.


Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Section SCFG_2.
Context {SCFG_P : ScfgP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition apart (x lx y ly : Z) : Prop := x + lx <= y \/ y + ly <= x.

Definition mulm_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o sp y : Z) (b : L5.bigobj) (ws : list Z) (g : growth) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 o /\
  let m := S (L5.bo_len b) in
  let rw := mulw_words ws y in
  let n' := rlen rw in
  let fbg := match g with Same => L5.bo_fb b | Grown _ _ => Z.lor (L5.bo_fb b) 1 end in
  let fb' := if Nat.eqb n' 0 then Z.land fbg 253 else fbg in
  length rw = m /\ words_ok rw /\
  exists st',
    L5.big_at RSEGS M' o (L5.BO fb' n' st') /\ L5C.obj_limbs RSEGS M' (L5.BO fb' m st') rw /\ (n' <= m)%nat /\
    match g with
    | Same => (L5.bo_dyn b = true \/ (m <= 2)%nat) /\ LB' = LB /\ cr' = cr
              /\ match L5.bo_st b, st' with
                 | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
                 | L5.BInl _ _, L5.BInl _ _ => True
                 | _, _ => False end
              /\ L5C.hpres L LB sp MULM_SCR [(o, 32); (L5.bo_data o b, 8 * Z.of_nat m)] M M'
    | Grown A cap => L5.bo_dyn b = false /\ (3 <= m)%nat /\ cap = round_up (Z.of_nat m) /\ LB' = (A, 8 * cap) :: LB /\ cr' = debit L cr (8 * cap)
              /\ L5C.fresh_block L LB M' A (8 * cap) /\ st' = L5.BDyn cap A
              /\ L5C.hpres L LB sp MULM_SCR [(o, 32)] M M'
    end.

Definition mulm_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o sp r y : Z) (b : L5.bigobj) (ws : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 y -> 0 <= y < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp MULM_SCR ->
    L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> (1 <= L5.bo_len b <= 300)%nat ->
    o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.defined M o 32 ->
    (L5.bo_dyn b = true -> Z.of_nat (L5.bo_len b) + 1 <= L5.bo_cap b) ->
    (L5.bo_len b = 2%nat -> L5.bo_dyn b = false -> credit_ok L cr (8 * round_up 3)) ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        mulm_post L LB cr M M' R R' o sp y b ws g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R MULM M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_23488 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R 0x2358c M) (st fx R r M).
Proof. intros H1 Hr He. apply (BDU.ret_to fx R M 0x2358c W_2358c r F_2358c eq_refl D_2358c H1 Hr He). Qed.
Lemma word_self (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. apply BG.word_of_unsigned. reflexivity. Qed.
Lemma word_range (w : word) : 0 <= bv_unsigned w < 2 ^ 64. Proof. apply (BL.bvu_range w). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition U (R : bvmap 5 word) (j : nat) : Z := bv_unsigned (getr R (reg j)).
Definition VAL (R0 R : bvmap 5 word) (sp o y n fb d i dg c hv lv nx : Z) (j : nat) : word :=
  match j with
  | 2%nat => Z_to_bv 64 sp
  | 33%nat => Z_to_bv 64 o | 34%nat => Z_to_bv 64 y | 35%nat => Z_to_bv 64 n | 36%nat => Z_to_bv 64 fb | 37%nat => Z_to_bv 64 d
  | 39%nat => Z_to_bv 64 i | 40%nat => Z_to_bv 64 dg | 41%nat => Z_to_bv 64 c | 42%nat => getr R (reg 1)
  | 45%nat => Z_to_bv 64 hv | 46%nat => Z_to_bv 64 lv | 47%nat => Z_to_bv 64 nx
  | 48%nat => getr R0 (reg 1) | 49%nat => getr R0 (reg 8) | 50%nat => getr R0 (reg 9) | 51%nat => getr R0 (reg 18) | 52%nat => getr R0 (reg 19) | 53%nat => getr R0 (reg 20)
  | 54%nat => getr R0 (reg 21) | 55%nat => getr R0 (reg 22) | 56%nat => getr R0 (reg 23) | 57%nat => getr R0 (reg 24) | 58%nat => getr R0 (reg 25) | 59%nat => getr R0 (reg 26)
  | 60%nat => getr R0 (reg 27)
  | _ => getr R (reg j)
  end.
Definition VZ (R0 R : bvmap 5 word) (sp o y n fb d i dg c hv lv nx : Z) (j : nat) : Z :=
  match j with
  | 2%nat => sp
  | 33%nat => o | 34%nat => y | 35%nat => n | 36%nat => fb | 37%nat => d | 39%nat => i | 40%nat => dg | 41%nat => c | 42%nat => U R 1
  | 45%nat => hv | 46%nat => lv | 47%nat => nx
  | 48%nat => U R0 1 | 49%nat => U R0 8 | 50%nat => U R0 9 | 51%nat => U R0 18 | 52%nat => U R0 19 | 53%nat => U R0 20
  | 54%nat => U R0 21 | 55%nat => U R0 22 | 56%nat => U R0 23 | 57%nat => U R0 24 | 58%nat => U R0 25 | 59%nat => U R0 26 | 60%nat => U R0 27
  | _ => U R j
  end.
Lemma VAL_VZ R0 R sp o y n fb d i dg c hv lv nx :
  0 <= sp < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= n < 2 ^ 62 -> 0 <= fb < 256 -> 0 <= d < 2 ^ 64 -> 0 <= i < 2 ^ 62 ->
  0 <= dg < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= hv < 2 ^ 64 -> 0 <= lv < 2 ^ 64 -> 0 <= nx < 2 ^ 64 ->
  forall j, bv_unsigned (ev (Env (VAL R0 R sp o y n fb d i dg c hv lv nx) (fun _ => [])) j) = VZ R0 R sp o y n fb d i dg c hv lv nx j.
Proof.
  intros until j. cbn [ev]. unfold VAL, VZ, U.
  repeat (lazymatch goal with
          | |- bv_unsigned (match j with _ => _ end) = _ => destruct j as [|j]
          | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.

Definition saved (M : word -> option byte) (sp : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (U R0 1) /\ L5.u64_at RSEGS M (sp - 16) (U R0 8) /\ L5.u64_at RSEGS M (sp - 24) (U R0 9) /\
  L5.u64_at RSEGS M (sp - 32) (U R0 18) /\ L5.u64_at RSEGS M (sp - 40) (U R0 19) /\ L5.u64_at RSEGS M (sp - 48) (U R0 20) /\
  L5.u64_at RSEGS M (sp - 56) (U R0 21) /\ L5.u64_at RSEGS M (sp - 64) (U R0 22) /\ L5.u64_at RSEGS M (sp - 72) (U R0 23) /\
  L5.u64_at RSEGS M (sp - 80) (U R0 24) /\ L5.u64_at RSEGS M (sp - 88) (U R0 25) /\ L5.u64_at RSEGS M (sp - 96) (U R0 26) /\
  L5.u64_at RSEGS M (sp - 104) (U R0 27).
(* [comment removed for export] *)
Definition view (M : word -> option byte) (sp o d n : Z) : Prop :=
  L5.u64_at RSEGS M (sp - 136) o /\ L5.u64_at RSEGS M (sp - 128) MASK32 /\ L5.u64_at RSEGS M (sp - 120) d /\ L5.u64_at RSEGS M (sp - 112) (n + 1).
Definition spok (sp : Z) : Prop := sp mod 16 = 0 /\ 1048720 <= sp <= 140737488355328.
Definition at_ret (R0 R' : bvmap 5 word) (sp o : Z) : Prop :=
  getr R' (reg 1) = getr R0 (reg 1) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = getr R0 (reg 8) /\ getr R' (reg 9) = getr R0 (reg 9) /\
  getr R' (reg 18) = getr R0 (reg 18) /\ getr R' (reg 19) = getr R0 (reg 19) /\ getr R' (reg 20) = getr R0 (reg 20) /\
  getr R' (reg 21) = getr R0 (reg 21) /\ getr R' (reg 22) = getr R0 (reg 22) /\ getr R' (reg 23) = getr R0 (reg 23) /\
  getr R' (reg 24) = getr R0 (reg 24) /\ getr R' (reg 25) = getr R0 (reg 25) /\ getr R' (reg 26) = getr R0 (reg 26) /\
  getr R' (reg 27) = getr R0 (reg 27) /\ getr R' (reg 10) = Z_to_bv 64 o.
Lemma saved_keep_out M M' sp R0 lo hi : (forall x : word, ~ (lo <= bv_unsigned x < hi) -> M' x = M x) ->
  (sp <= lo \/ hi <= sp - 104 \/ hi <= lo) -> 144 <= sp -> sp <= 2 ^ 64 -> saved M sp R0 -> saved M' sp R0.
Proof.
  intros HF Hap H1 H2 (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
  repeat split; (eapply (L5K.u64_at_keep RSEGS M M'); [exact HF | lia | lia | lia | eassumption]).
Qed.
Lemma view_keep_out M M' sp o d n lo hi : (forall x : word, ~ (lo <= bv_unsigned x < hi) -> M' x = M x) ->
  (sp - 104 <= lo \/ hi <= sp - 144 \/ hi <= lo) -> 144 <= sp -> sp <= 2 ^ 64 -> view M sp o d n -> view M' sp o d n.
Proof.
  intros HF Hap H1 H2 (S1 & S2 & S3 & S4).
  repeat split; (eapply (L5K.u64_at_keep RSEGS M M'); [exact HF | lia | lia | lia | eassumption]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KSA : list nat := Eval vm_compute in (BG.kept_list 64 PAi.regs0 PAi.regs_out0).
Lemma KSAi_ok : BG.kept_ok 64 PAi.regs0 PAi.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSAd_ok : BG.kept_ok 64 PAd.regs0 PAd.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.
Definition KSBd : list nat := Eval vm_compute in (BG.kept_list 64 PBd.regs0 PBd.regs_out0).
Lemma KSBd_ok : BG.kept_ok 64 PBd.regs0 PBd.regs_out0 KSBd = true. Proof. vm_compute. reflexivity. Qed.
Definition KSBi : list nat := Eval vm_compute in (BG.kept_list 64 PBi.regs0 PBi.regs_out0).
Lemma KSBi_ok : BG.kept_ok 64 PBi.regs0 PBi.regs_out0 KSBi = true. Proof. vm_compute. reflexivity. Qed.
Definition KSI : list nat := Eval vm_compute in (BG.kept_list 64 PI.regs0 PI.regs_out0).
Lemma KSI_ok0 : BG.kept_ok 64 PI.regs0 PI.regs_out0 KSI = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSI_ok1 : BG.kept_ok 64 PI.regs0 PI.regs_out1 KSI = true. Proof. vm_compute. reflexivity. Qed.
Definition KSR : list nat := Eval vm_compute in (BG.kept_list 64 PR.regs0 PR.regs_out0).
Lemma KSR_ok : BG.kept_ok 64 PR.regs0 PR.regs_out0 KSR = true. Proof. vm_compute. reflexivity. Qed.
Definition KSE : list nat := Eval vm_compute in (BG.kept_list 64 PE.regs0 PE.regs_out0).
Lemma KSE_ok : BG.kept_ok 64 PE.regs0 PE.regs_out0 KSE = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_resize (R : bvmap 5 word) (sp o y n dg : Z) : Prop :=
  getr R (reg 1) = Z_to_bv 64 AFTER_RESIZE /\ getr R (reg 2) = Z_to_bv 64 (sp - 144) /\ getr R (reg 8) = Z_to_bv 64 o /\
  getr R (reg 19) = Z_to_bv 64 y /\ getr R (reg 10) = Z_to_bv 64 o /\ getr R (reg 11) = Z_to_bv 64 (n + 1) /\
  getr R (reg 21) = Z_to_bv 64 n /\ getr R (reg 23) = Z_to_bv 64 dg.

Lemma mmAi_conc fx R M (sp o y n fb dg : Z) :
  spok sp -> L5.writable RSEGS M (sp - 144) 144 -> apart (sp - 144) 144 o 32 ->
  1048576 <= o -> o + 32 <= 2 ^ 47 -> o mod 8 = 0 -> L5.u8_at RSEGS M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = false ->
  L5.u64_at RSEGS M (o + 16) dg -> 0 <= dg < 2 ^ 64 ->
  L5.u64_at RSEGS M (o + 8) n -> 1 <= n <= 300 -> 0 <= y < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 y ->
  exists fx' R' M', msteps RSEGS (st fx R MULM M) (st fx' R' RESIZE M')
    /\ (forall x, In x KSA -> getr R' (reg x) = getr R (reg x)) /\ at_resize R' sp o y n dg /\ saved M' sp R
    /\ (forall a : word, ~ (sp - 144 <= bv_unsigned a < sp) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW Sap Olo Ohi O8 O0 Hfb Hb0 D16 Hdg On Hn Hy H2 H10 H11. unfold apart in *.
  set (Vf := VAL R R sp o y n fb 0 0 dg 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R R sp o y n fb 0 0 dg 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PAi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAi.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PAi.kn0). { unfold know_ok, PAi.kn0. L5K.kn_all ZA. }
  destruct (PAi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PAi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PAi.regs0 PAi.regs_out0 64 KSA KSAi_ok HR Hag Hregs j Hj). }
  split. { unfold at_resize, AFTER_RESIZE. repeat split; rewrite (BG.out_reg PAi.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAi.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  change (SR.ps_cells PAi.ps0) with PAi.cells0 in Hcells. unfold PAi.cells0 in Hcells.
  split. { unfold saved, U. repeat split.
    all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PAi.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

Lemma mmAd_conc fx R M (sp o y n fb d dg : Z) :
  spok sp -> L5.writable RSEGS M (sp - 144) 144 -> apart (sp - 144) 144 o 32 ->
  1048576 <= o -> o + 32 <= 2 ^ 47 -> o mod 8 = 0 -> L5.u8_at RSEGS M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = true ->
  L5.u64_at RSEGS M (o + 24) d -> 4096 <= d -> d + 8 <= 2 ^ 47 -> d mod 8 = 0 -> L5.u64_at RSEGS M d dg -> 0 <= dg < 2 ^ 64 -> apart (sp - 144) 144 d 8 ->
  L5.u64_at RSEGS M (o + 8) n -> 1 <= n <= 300 -> 0 <= y < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 y ->
  exists fx' R' M', msteps RSEGS (st fx R MULM M) (st fx' R' RESIZE M')
    /\ (forall x, In x KSA -> getr R' (reg x) = getr R (reg x)) /\ at_resize R' sp o y n dg /\ saved M' sp R
    /\ (forall a : word, ~ (sp - 144 <= bv_unsigned a < sp) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW Sap Olo Ohi O8 O0 Hfb Hb0 O24 Dlo Dhi D8 DD Hdg Dap On Hn Hy H2 H10 H11. unfold apart in *.
  set (Vf := VAL R R sp o y n fb d 0 dg 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R R sp o y n fb d 0 dg 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PAd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAd.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PAd.kn0). { unfold know_ok, PAd.kn0. L5K.kn_all ZA. }
  destruct (PAd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PAd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PAd.regs0 PAd.regs_out0 64 KSA KSAd_ok HR Hag Hregs j Hj). }
  split. { unfold at_resize, AFTER_RESIZE. repeat split; rewrite (BG.out_reg PAd.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAd.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  change (SR.ps_cells PAd.ps0) with PAd.cells0 in Hcells. unfold PAd.cells0 in Hcells.
  split. { unfold saved, U. repeat split.
    all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PAd.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HV (y : Z) : Z := y / L5DDM.K.
Definition LV (y : Z) : Z := y mod L5DDM.K.
Lemma HV_rng y : 0 <= y < 2 ^ 64 -> 0 <= HV y < L5DDM.K. Proof. apply L5DDM.hv_rng. Qed.
Lemma LV_rng y : 0 <= LV y < L5DDM.K. Proof. apply L5DDM.lv_rng. Qed.
Lemma K_val : L5DDM.K = 4294967296. Proof. reflexivity. Qed.
Definition at_head (R : bvmap 5 word) (sp o y d : Z) (n i : nat) (dg c hv lv : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 144) /\ getr R (reg 18) = Z_to_bv 64 (Z.of_nat i) /\ getr R (reg 20) = Z_to_bv 64 hv /\
  getr R (reg 21) = Z_to_bv 64 (Z.of_nat n) /\ getr R (reg 22) = Z_to_bv 64 lv /\ getr R (reg 23) = Z_to_bv 64 dg /\ getr R (reg 24) = Z_to_bv 64 c.

(* [comment removed for export] *)
Lemma mmBd_conc fx (R0 R : bvmap 5 word) M (sp o y fb d dg : Z) (n : nat) :
  spok sp -> L5.writable RSEGS M (sp - 144) 144 -> apart (sp - 144) 144 o 32 ->
  1048576 <= o -> o + 32 <= 2 ^ 47 -> o mod 8 = 0 ->
  L5.u8_at RSEGS M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = true -> L5.u64_at RSEGS M (o + 8) (Z.of_nat n + 1) -> L5.u64_at RSEGS M (o + 24) d ->
  (1 <= n <= 300)%nat -> 0 <= y < 2 ^ 64 -> 0 <= dg < 2 ^ 64 -> 4096 <= d -> d + 8 * Z.of_nat n + 8 <= 2 ^ 47 -> d mod 8 = 0 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 144) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 19) = Z_to_bv 64 y ->
  getr R (reg 21) = Z_to_bv 64 (Z.of_nat n) -> getr R (reg 23) = Z_to_bv 64 dg ->
  exists fx' R' M', msteps RSEGS (st fx R AFTER_RESIZE M) (st fx' R' LHEAD M')
    /\ (forall x, In x KSBd -> getr R' (reg x) = getr R (reg x))
    /\ at_head R' sp o y d n 0 dg 0 (HV y) (LV y) /\ view M' sp o d (Z.of_nat n)
    /\ (forall a : word, ~ (sp - 136 <= bv_unsigned a < sp - 104) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW Sap Olo Ohi O8 O0 Hfb Hb0 On O24 Hn Hy Hdg Dlo Dhi D8 H2 H8 H19 H21 H23. unfold apart in *.
  set (Vf := VAL R0 R sp o y (Z.of_nat n) fb d 0 dg 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp o y (Z.of_nat n) fb d 0 dg 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PBd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PBd.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PBd.kn0). { unfold know_ok, PBd.kn0. L5K.kn_all ZA. }
  destruct (PBd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PBd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PBd.regs0 PBd.regs_out0 64 KSBd KSBd_ok HR Hag Hregs j Hj). }
  split. { unfold at_head, HV, LV. repeat split; rewrite (BG.out_reg PBd.regs_out0 E' R' _ Hregs) by lia; cbn [nth PBd.regs_out0];
           first [reflexivity | L5K.wordE' ZA Hag
                 | apply BG.word_of_unsigned; L5K.evalB' ZA Hag; first [reflexivity | apply L5DDM.lv_eq; lia] ]. }
  change (SR.ps_cells PBd.ps0) with PBd.cells0 in Hcells. unfold PBd.cells0 in Hcells.
  split. { unfold view, MASK32. repeat split.
    all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PBd.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma mmBi_conc fx (R0 R : bvmap 5 word) M (sp o y fb dg : Z) :
  spok sp -> L5.writable RSEGS M (sp - 144) 144 -> apart (sp - 144) 144 o 32 ->
  1048576 <= o -> o + 32 <= 2 ^ 47 -> o mod 8 = 0 ->
  L5.u8_at RSEGS M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = false -> L5.u64_at RSEGS M (o + 8) 2 -> 0 <= y < 2 ^ 64 -> 0 <= dg < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 144) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 19) = Z_to_bv 64 y ->
  getr R (reg 21) = Z_to_bv 64 1 -> getr R (reg 23) = Z_to_bv 64 dg ->
  exists fx' R' M', msteps RSEGS (st fx R AFTER_RESIZE M) (st fx' R' LHEAD M')
    /\ (forall x, In x KSBi -> getr R' (reg x) = getr R (reg x))
    /\ at_head R' sp o y (o + 16) 1 0 dg 0 (HV y) (LV y) /\ view M' sp o (o + 16) 1
    /\ (forall a : word, ~ (sp - 136 <= bv_unsigned a < sp - 104) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW Sap Olo Ohi O8 O0 Hfb Hb0 On Hy Hdg H2 H8 H19 H21 H23. unfold apart in *.
  set (Vf := VAL R0 R sp o y 1 fb (o + 16) 0 dg 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp o y 1 fb (o + 16) 0 dg 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PBi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PBi.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PBi.kn0). { unfold know_ok, PBi.kn0. L5K.kn_all ZA. }
  destruct (PBi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PBi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PBi.regs0 PBi.regs_out0 64 KSBi KSBi_ok HR Hag Hregs j Hj). }
  split. { unfold at_head, HV, LV. repeat split; rewrite (BG.out_reg PBi.regs_out0 E' R' _ Hregs) by lia; cbn [nth PBi.regs_out0];
           first [reflexivity | L5K.wordE' ZA Hag | apply BG.word_of_unsigned; L5K.evalE' ZA Hag | cbn; f_equal; lia
                 | apply BG.word_of_unsigned; L5K.evalB' ZA Hag; first [reflexivity | apply L5DDM.lv_eq; lia] ]. }
  change (SR.ps_cells PBi.ps0) with PBi.cells0 in Hcells. unfold PBi.cells0 in Hcells.
  split. { unfold view, MASK32. repeat split.
    all: first [ rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag] ]. }
  split. { intros x Hx. apply Hfr. unfold PBi.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma PSS_I : PI.PSS = [PI.ps0; PI.ps1]. Proof. vm_compute. reflexivity. Qed.
Lemma pc_I0 : SR.ps_pc PI.ps0 = LHEAD. Proof. reflexivity. Qed.
Lemma pc_I1 : SR.ps_pc PI.ps1 = LDONE. Proof. reflexivity. Qed.
Definition XI : expr := EAlu ALU_ADD (EVar 37) (EMd M_MUL (ELit 8) (EVar 39)).
(* [comment removed for export] *)
Definition EXLO : expr := Eval vm_compute in (match SR.ps_cells PI.ps0 with [_; KWord _ _ e] => e | _ => ELit 0 end).
Lemma cells_I0 : SR.ps_cells PI.ps0 = [KRange (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit (-1)) (EVar 39))) 2 300; KWord (SA XI 0) 8 EXLO].
Proof. vm_compute. reflexivity. Qed.
Lemma cells_I1 : SR.ps_cells PI.ps1 = [KRange (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit (-1)) (EVar 39))) 1 1; KWord (SA XI 0) 8 EXLO].
Proof. vm_compute. reflexivity. Qed.
Lemma r18_I0 : nth 18 PI.regs_out0 (ELit 0) = EAlu ALU_ADD (EVar 39) (ELit 1). Proof. vm_compute. reflexivity. Qed.
Lemma r18_I1 : nth 18 PI.regs_out1 (ELit 0) = EAlu ALU_ADD (EVar 39) (ELit 1). Proof. vm_compute. reflexivity. Qed.
Lemma r24_I : nth 24 PI.regs_out1 (ELit 0) = nth 24 PI.regs_out0 (ELit 0). Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition mstep (dg hv lv c : Z) : Z := dg * (hv * L5DDM.K + lv) + c.

Lemma mmI_conc fx (R0 R : bvmap 5 word) M (sp o y d : Z) (n i : nat) (dg c hv lv nx : Z) :
  at_head R sp o y d n i dg c hv lv -> view M sp o d (Z.of_nat n) -> spok sp -> apart (sp - 144) 144 d (8 * Z.of_nat n + 8) ->
  (i < n)%nat -> (n <= 300)%nat -> 1048576 <= o -> o + 32 <= 2 ^ 47 -> 0 <= y < 2 ^ 64 ->
  0 <= dg < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= hv < L5DDM.K -> 0 <= lv < L5DDM.K -> 0 <= nx < 2 ^ 64 ->
  4096 <= d -> d + 8 * Z.of_nat n + 8 <= 2 ^ 47 -> d mod 8 = 0 ->
  L5.writable RSEGS M (d + 8 * Z.of_nat i) 8 -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i + 8) nx ->
  exists fx' R' M' (pc' : Z), msteps RSEGS (st fx R LHEAD M) (st fx' R' pc' M')
    /\ (forall x, In x KSI -> getr R' (reg x) = getr R (reg x))
    /\ ((pc' = LHEAD /\ (i + 1 < n)%nat) \/ (pc' = LDONE /\ (i + 1 = n)%nat))
    /\ at_head R' sp o y d n (S i) nx (mstep dg hv lv c / 2 ^ 64) hv lv
    /\ L5.u64_at RSEGS M' (d + 8 * Z.of_nat i) (mstep dg hv lv c mod 2 ^ 64)
    /\ (forall a : word, ~ (d + 8 * Z.of_nat i <= bv_unsigned a < d + 8 * Z.of_nat i + 8) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros (A2 & A18 & A20 & A21 & A22 & A23 & A24) (V1 & V2 & V3 & V4) [S16 Ssp] Dap Hi Hn Olo Ohi Hy Hdg Hc Hhv Hlv Hnx Dlo Dhi D8 DW DX.
  unfold apart in Dap. pose proof K_val as KV. unfold MASK32 in V2.
  set (Vf := VAL R0 R sp o y (Z.of_nat n) 0 d (Z.of_nat i) dg c hv lv nx). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp o y (Z.of_nat n) 0 d (Z.of_nat i) dg c hv lv nx j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PI.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PI.kn0). { unfold know_ok, PI.kn0. L5K.kn_all ZA. }
  destruct (PI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  rewrite PSS_I in Hnth. change PI.NX0 with 64%nat in Hag.
  assert (FR: forall a : word, ~ (d + 8 * Z.of_nat i <= bv_unsigned a < d + 8 * Z.of_nat i + 8) -> M' a = M a).
  { intros x Hx. apply Hfr. unfold PI.F0. L5K.outsideF ZA Hag. }
  (* [comment removed for export] *)
  assert (CAR: bv_unsigned (edenot E' (nth 24 PI.regs_out0 (ELit 0))) = mstep dg hv lv c / 2 ^ 64).
  { unfold mstep. L5K.evalB' ZA Hag. etransitivity. 2: apply (L5DDM.hi_eq dg hv lv c); lia. cbv zeta. reflexivity. }
  assert (LOW: bv_unsigned (edenot E' EXLO) = mstep dg hv lv c mod 2 ^ 64).
  { unfold mstep, EXLO. L5K.evalB' ZA Hag. apply (L5DDM.lo_eq dg hv lv c); lia. }
  assert (RB: forall (rs : list expr) (lo' hi' : Z),
    SR.ps_regs ps = map (fun i => (i, nth i rs (ELit 0))) (seq 1 31) ->
    nth 2 rs (ELit 0) = EAlu ALU_ADD (EVar 2) (ELit (-144)) ->
    nth 18 rs (ELit 0) = EAlu ALU_ADD (EVar 39) (ELit 1) -> nth 20 rs (ELit 0) = EVar 45 -> nth 21 rs (ELit 0) = EVar 35 -> nth 22 rs (ELit 0) = EVar 46 ->
    nth 23 rs (ELit 0) = EVar 47 -> nth 24 rs (ELit 0) = nth 24 PI.regs_out0 (ELit 0) ->
    SR.ps_cells ps = [KRange (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit (-1)) (EVar 39))) lo' hi'; KWord (SA XI 0) 8 EXLO] ->
    at_head R' sp o y d n (S i) nx (mstep dg hv lv c / 2 ^ 64) hv lv
    /\ L5.u64_at RSEGS M' (d + 8 * Z.of_nat i) (mstep dg hv lv c mod 2 ^ 64)
    /\ lo' <= Z.of_nat n - Z.of_nat i <= hi').
  { intros rs lo' hi' HPR N2 N18 N20 N21 N22 N23 N24 HC.
    assert (OUT: forall x, (0 < x < 32)%nat -> getr R' (reg x) = edenot E' (nth x rs (ELit 0))).
    { intros x Hx. apply (proj2 (Hregs x (nth x rs (ELit 0)) ltac:(rewrite HPR; apply in_map_iff; exists x; split; [reflexivity | apply in_seq; lia]))). }
    split. { unfold at_head. repeat split; rewrite OUT by lia.
             - rewrite N2. L5K.wordE' ZA Hag.
             - rewrite N18. apply BG.word_of_unsigned. L5K.evalE' ZA Hag.
             - rewrite N20. L5K.wordE' ZA Hag. - rewrite N21. L5K.wordE' ZA Hag. - rewrite N22. L5K.wordE' ZA Hag.
             - rewrite N23. L5K.wordE' ZA Hag.
             - rewrite N24. apply BG.word_of_unsigned. exact CAR. }
    rewrite HC in Hcells.
    split. { rewrite <- (Z.add_0_r (d + 8 * Z.of_nat i)). eapply (L5K.u64_of_KWord8 RSEGS E' M'). apply Hcells. right; left; reflexivity. L5K.evalE' ZA Hag. exact LOW. }
    eapply (L5K.range_of_KRange RSEGS E' M'). apply Hcells. left; reflexivity. L5K.evalE' ZA Hag. }
  destruct (L5K.nth_error_pair _ _ _ _ Hnth) as [[-> ->] | [-> ->]].
  - destruct (RB PI.regs_out0 2 300 eq_refl eq_refl r18_I0 eq_refl eq_refl eq_refl eq_refl eq_refl cells_I0) as (AT & XV & RG).
    exists fx', R', M', LHEAD. rewrite pc_I0 in Hms. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PI.regs0 PI.regs_out0 64 KSI KSI_ok0 HR Hag Hregs j Hj). }
    split. { left. split. reflexivity. lia. } split. exact AT. split. exact XV. split. exact FR. exact Hgr.
  - destruct (RB PI.regs_out1 1 1 eq_refl eq_refl r18_I1 eq_refl eq_refl eq_refl eq_refl r24_I cells_I1) as (AT & XV & RG).
    exists fx', R', M', LDONE. rewrite pc_I1 in Hms. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PI.regs0 PI.regs_out1 64 KSI KSI_ok1 HR Hag Hregs j Hj). }
    split. { right. split. reflexivity. lia. } split. exact AT. split. exact XV. split. exact FR. exact Hgr.
Qed.

(* [comment removed for export] *)
Definition at_reduce (R : bvmap 5 word) (sp o : Z) : Prop :=
  getr R (reg 1) = Z_to_bv 64 AFTER_REDUCE /\ getr R (reg 2) = Z_to_bv 64 (sp - 144) /\ getr R (reg 8) = Z_to_bv 64 o /\ getr R (reg 10) = Z_to_bv 64 o.
Lemma mmR_conc fx (R0 R : bvmap 5 word) M (sp o d c : Z) (n : nat) :
  spok sp -> view M sp o d (Z.of_nat n) -> apart (sp - 144) 144 d (8 * Z.of_nat n + 8) -> 1048576 <= o -> o + 32 <= 2 ^ 47 ->
  0 <= c < 2 ^ 64 -> (1 <= n <= 300)%nat ->
  4096 <= d -> d + 8 * Z.of_nat n + 8 <= 2 ^ 47 -> d mod 8 = 0 -> L5.writable RSEGS M (d + 8 * Z.of_nat n) 8 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 144) -> getr R (reg 21) = Z_to_bv 64 (Z.of_nat n) -> getr R (reg 24) = Z_to_bv 64 c ->
  exists fx' R' M', msteps RSEGS (st fx R LDONE M) (st fx' R' L5REDU.REDUCE M')
    /\ (forall x, In x KSR -> getr R' (reg x) = getr R (reg x)) /\ at_reduce R' sp o
    /\ L5.u64_at RSEGS M' (d + 8 * Z.of_nat n) c
    /\ (forall a : word, ~ (d + 8 * Z.of_nat n <= bv_unsigned a < d + 8 * Z.of_nat n + 8) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] (V1 & V2 & V3 & V4) Dap Olo Ohi Hc Hn Dlo Dhi D8 DW H2 H21 H24. unfold apart in Dap. unfold MASK32 in V2.
  set (Vf := VAL R0 R sp o 0 (Z.of_nat n) 0 d 0 0 c 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp o 0 (Z.of_nat n) 0 d 0 0 c 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PR.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PR.kn0). { unfold know_ok, PR.kn0. L5K.kn_all ZA. }
  destruct (PR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PR.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PR.regs0 PR.regs_out0 64 KSR KSR_ok HR Hag Hregs j Hj). }
  split. { unfold at_reduce, AFTER_REDUCE. repeat split; rewrite (BG.out_reg PR.regs_out0 E' R' _ Hregs) by lia; cbn [nth PR.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  change (SR.ps_cells PR.ps0) with PR.cells0 in Hcells. unfold PR.cells0 in Hcells.
  split. { rewrite <- (Z.add_0_r (d + 8 * Z.of_nat n)). eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PR.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma mmE_conc fx (R0 R : bvmap 5 word) M (sp o : Z) :
  spok sp -> L5.writable RSEGS M (sp - 144) 144 -> saved M sp R0 -> 0 <= o < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 144) -> getr R (reg 8) = Z_to_bv 64 o ->
  exists fx' R' M', msteps RSEGS (st fx R AFTER_REDUCE M) (st fx' R' RET M')
    /\ (forall x, In x KSE -> getr R' (reg x) = getr R (reg x)) /\ at_ret R0 R' sp o /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW SV Ho H2 H8. pose proof SV as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13). unfold U in *.
  set (Vf := VAL R0 R sp o 0 0 0 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp o 0 0 0 0 0 0 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PE.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PE.kn0). { unfold know_ok, PE.kn0. L5K.kn_all ZA. }
  destruct (PE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PE.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PE.regs0 PE.regs_out0 64 KSE KSE_ok HR Hag Hregs j Hj). }
  split. { unfold at_ret. repeat split; rewrite (BG.out_reg PE.regs_out0 E' R' _ Hregs) by lia; cbn [nth PE.regs_out0 edenot];
           first [reflexivity | rewrite <- (proj1 Hag) by lia; reflexivity | L5K.wordE' ZA Hag]. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Definition KSL : list nat := [2; 3; 4; 5; 6; 7; 17; 20; 21; 22; 28; 29; 30; 31]%nat.

Lemma y_halves y : 0 <= y -> HV y * L5DDM.K + LV y = y.
Proof. intros. unfold HV, LV. symmetry. apply L5DDM.y_split. lia. Qed.
Lemma mstep_eq ws y i : 0 <= y -> mstep (nth_w ws i) (HV y) (LV y) (mulw_c ws y 0 i) = nth_w ws i * y + mulw_c ws y 0 i.
Proof. intros. unfold mstep. rewrite y_halves by lia. reflexivity. Qed.

Lemma mloop (m : nat) : forall fx (R0 R : bvmap 5 word) M (sp o y d : Z) (n i : nat) (ws : list Z),
  (m = n - i)%nat -> at_head R sp o y d n i (nth_w ws i) (mulw_c ws y 0 i) (HV y) (LV y) -> (i < n)%nat -> (1 <= n <= 300)%nat ->
  length ws = n -> words_ok ws -> 0 <= y < 2 ^ 64 ->
  view M sp o d (Z.of_nat n) -> spok sp -> apart (sp - 144) 144 d (8 * Z.of_nat n + 8) ->
  1048576 <= o -> o + 32 <= 2 ^ 47 -> 4096 <= d -> d + 8 * Z.of_nat n + 8 <= 2 ^ 47 -> d mod 8 = 0 ->
  L5.writable RSEGS M d (8 * Z.of_nat n + 8) ->
  (forall j, (j < i)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat j) (nth_w (mulw_words ws y) j)) ->
  (forall j, (i < j <= n)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat j) (nth_w (ws ++ [0]) j)) ->
  exists fx' R' M', msteps RSEGS (st fx R LHEAD M) (st fx' R' L5REDU.REDUCE M')
    /\ (forall x, In x KSL -> getr R' (reg x) = getr R (reg x))
    /\ at_reduce R' sp o
    /\ L5.limbs_at RSEGS M' d (mulw_words ws y)
    /\ (forall a : word, ~ (d <= bv_unsigned a < d + 8 * Z.of_nat n + 8) -> M' a = M a) /\ mem_grows M M'.
Proof.
  induction m as [|m IH]; intros fx R0 R M sp o y d n i ws Hm AT Hi Hn WL WO Hy VW SP Dap Olo Ohi Dlo Dhi D8 DW DONE TODO. lia.
  pose proof SP as [S16 Ssp]. pose proof Dap as Dap'. unfold apart in Dap'.
  pose proof (words_ok_nth ws i WO) as Hdg. pose proof (mulw_c_bound ws y 0 i WO Hy ltac:(lia)) as Hc.
  pose proof (HV_rng y Hy) as Hhv. pose proof (LV_rng y) as Hlv.
  assert (WO0: words_ok (ws ++ [0])). { apply words_ok_app. exact WO. constructor. lia. constructor. }
  pose proof (words_ok_nth (ws ++ [0]) (S i) WO0) as Hnx.
  destruct (mmI_conc fx R0 R M sp o y d n i (nth_w ws i) (mulw_c ws y 0 i) (HV y) (LV y) (nth_w (ws ++ [0]) (S i)) AT VW SP Dap Hi ltac:(lia) Olo Ohi Hy Hdg Hc Hhv Hlv Hnx Dlo Dhi D8
              ltac:(eapply L5.writable_sub; [exact DW|lia|lia])
              ltac:(replace (d + 8 * Z.of_nat i + 8) with (d + 8 * Z.of_nat (S i)) by lia; apply TODO; lia))
    as (fx1 & R1 & M1 & pc1 & MS1 & K1 & EX & AT1 & Xv & FR1 & G1).
  rewrite mstep_eq in AT1, Xv by lia.
  rewrite <- (mulw_c_S ws y 0 i) in AT1 by lia.
  assert (Xv': L5.u64_at RSEGS M1 (d + 8 * Z.of_nat i) (nth_w (mulw_words ws y) i)).
  { unfold mulw_words. rewrite mulw_loop_nth by lia. exact Xv. }
  assert (DONE1: forall j, (j < S i)%nat -> L5.u64_at RSEGS M1 (d + 8 * Z.of_nat j) (nth_w (mulw_words ws y) j)).
  { intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]. exact Xv'.
    eapply (L5K.u64_at_keep RSEGS M M1). exact FR1. lia. lia. lia. apply DONE. lia. }
  assert (TODO1: forall j, (S i < j <= n)%nat -> L5.u64_at RSEGS M1 (d + 8 * Z.of_nat j) (nth_w (ws ++ [0]) j)).
  { intros j Hj. eapply (L5K.u64_at_keep RSEGS M M1). exact FR1. lia. lia. lia. apply TODO. lia. }
  assert (DW1: L5.writable RSEGS M1 d (8 * Z.of_nat n + 8)) by (eapply L5.writable_grows; eauto).
  assert (VW1: view M1 sp o d (Z.of_nat n)). { eapply view_keep_out. exact FR1. lia. lia. lia. exact VW. }
  destruct EX as [[-> Hlt] | [-> Heq]].
  - assert (NX: nth_w (ws ++ [0]) (S i) = nth_w ws (S i)). { unfold nth_w. rewrite app_nth1 by lia. reflexivity. }
    rewrite NX in AT1.
    destruct (IH fx1 R0 R1 M1 sp o y d n (S i) ws ltac:(lia) AT1 ltac:(lia) Hn WL WO Hy VW1 SP Dap Olo Ohi Dlo Dhi D8 DW1 DONE1 TODO1)
      as (fx' & R' & M' & MS & K & AT' & RS & FR & G).
    exists fx', R', M'. split. eapply msteps_trans; eauto.
    split. { intros x Hx. rewrite (K x Hx). apply K1. apply (L5K.incl_b KSL KSI ltac:(vm_compute; reflexivity)). exact Hx. }
    split. exact AT'. split. exact RS.
    split. { intros a Ha. rewrite (FR a Ha). apply FR1. lia. } eapply mem_grows_trans; eauto.
  - destruct AT1 as (B2 & B18 & B20 & B21 & B22 & B23 & B24).
    pose proof (mulw_c_bound ws y 0 (S i) WO Hy ltac:(lia)) as Hc'.
    destruct (mmR_conc fx1 R0 R1 M1 sp o d (mulw_c ws y 0 (S i)) n SP VW1 Dap Olo Ohi Hc' Hn Dlo Dhi D8 ltac:(eapply L5.writable_sub; [exact DW1|lia|lia]) B2 B21 B24)
      as (fx2 & R2 & M2 & MS2 & K2 & AT2 & X2 & FR2 & G2).
    exists fx2, R2, M2. split. eapply msteps_trans; eauto.
    split. { intros x Hx. rewrite (K2 x) by (apply (L5K.incl_b KSL KSR ltac:(vm_compute; reflexivity)); exact Hx). apply K1. apply (L5K.incl_b KSL KSI ltac:(vm_compute; reflexivity)). exact Hx. }
    split. exact AT2.
    split. { intros j Hj. rewrite mulw_words_length, WL in Hj. fold (nth_w (mulw_words ws y) j). destruct (Nat.eq_dec j n) as [->|NE].
             - unfold mulw_words. rewrite <- WL at 2. rewrite mulw_loop_last. rewrite WL. replace n with (S i) at 2 by lia. exact X2.
             - eapply (L5K.u64_at_keep RSEGS M1 M2). exact FR2. lia. lia. lia. apply DONE1. lia. }
    split. { intros a Ha. rewrite (FR2 a) by lia. apply FR1. lia. } eapply mem_grows_trans; eauto.
Qed.
End SCFG_2.


End L5MULMU.
