(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigLinkZA.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5DivOP.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVOP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5K.zpoly_sound E Vz e z A Pz)).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, BL.MM. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u64_of_KWord8; eauto. Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u32_of_KWord4; eauto. Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof. intros K Ha Hv Hr ->. eapply L5K.u8_of_KWord1; eauto. Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof. intros Ha Hm. pose proof (L5K.land_le_r a m Ha ltac:(lia)). lia. Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
  intros Ha Hb. split. apply Z.lor_nonneg; lia.
  destruct (Z.eq_dec a 0) as [->|Na]. rewrite Z.lor_0_l. lia. destruct (Z.eq_dec b 0) as [->|Nb]. rewrite Z.lor_0_r. lia.
  apply (Z.log2_lt_cancel). rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; try lia; change (2 ^ Z.log2 256) with 256; lia.
Qed.
(* [comment removed for export] *)
Local Ltac byte_tac0 k :=
  lazymatch goal with
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; k
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_tac0 k
  | |- 0 <= (_ mod 2 ^ 64) < 256 => rewrite Z.mod_small by k; k
  | _ => k
  end.
Tactic Notation "byte_tac" tactic(k) := byte_tac0 k.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac solve_modk k :=
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5K.zpoly_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5K.zpoly]; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5K.zpoly_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5K.zpoly]; reflexivity | solve_modk k ].
(* [comment removed for export] *)
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
(* [comment removed for export] *)
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
(* [comment removed for export] *)
Local Ltac den_tac := first [reflexivity | lia | idtac].
(* [comment removed for export] *)
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5K.zpoly]; f_equal; clear; lia]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5K.zpoly]; f_equal; clear; lia ].
(* [comment removed for export] *)
Module Pd6e2 := LibSegZ_d6e2.
Definition KS_d6e2 : list nat := Eval vm_compute in (BG.kept_list 80 Pd6e2.regs0 Pd6e2.regs_out0).
Lemma KS_d6e2_ok : BG.kept_ok 80 Pd6e2.regs0 Pd6e2.regs_out0 KS_d6e2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6e2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 (V 36%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 42%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false -> 1 <= (V 42%nat) <= 300 ->
  1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 33%nat) (V 38%nat) ->
  0 <= (V 38%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21dd4 M) (st fx' R' 0x22848 M')
        /\ (forall x, In x KS_d6e2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 138760
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 168)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 200)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 38%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV41l HV41r] [HV42l HV42r] G2 G9 G18 G23 G27 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6 [K7l K7r] [K8l K8r] K9 K10 K11 [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E Pd6e2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6e2.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6e2.kn0).
  { unfold know_ok, Pd6e2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV41l HV41r K5l K5r K6) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | byte_tac ltac:(clear - HV41l HV41r K5l K5r K6; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV42l HV42r K7l K7r) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K5l K5r K6) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K5l K5r K6) | clear; lia | rewrite (L5K.land1_bit0_false (V 41%nat) ltac:(clear - HV41l HV41r K5l K5r K6; lia) K6); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10) | evalEk ZA ltac:(clear - HV38l HV38r K12l K12r) | clear - HV33l HV33r K8l K8r K10; lia | clear - HV33l HV33r K8l K8r K10; lia | byte_tac ltac:(clear - HV38l HV38r K12l K12r; lia) | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  destruct (Pd6e2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6e2.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd6e2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6e2.ps0) with 0x22848 in Hms. change (SR.ps_regs Pd6e2.ps0) with (map (fun i => (i, nth i Pd6e2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6e2.ps0) with Pd6e2.cells0 in Hcells. unfold Pd6e2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6e2.regs0 Pd6e2.regs_out0 80 KS_d6e2 KS_d6e2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6e2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd6e2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd6e2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6e2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd6e2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd6e2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd6e2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pd6e2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd6e2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd6e2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd6e2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6e2d := LibSegZ_d6e2d.
Definition KS_d6e2d : list nat := Eval vm_compute in (BG.kept_list 80 Pd6e2d.regs0 Pd6e2d.regs_out0).
Lemma KS_d6e2d_ok : BG.kept_ok 80 Pd6e2d.regs0 Pd6e2d.regs_out0 KS_d6e2d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6e2d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 (V 36%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 43%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = true ->
  1 <= (V 42%nat) <= 300 -> 0 <= (V 43%nat) <= 18446744073709551615 -> 1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (((V 2%nat) - 304) + 304 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 33%nat) (V 38%nat) -> 0 <= (V 38%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21dd4 M) (st fx' R' 0x22848 M')
        /\ (forall x, In x KS_d6e2d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 138760
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 168)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 200)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 38%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] G2 G9 G18 G23 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] [K9l K9r] [K10l K10r] K11 K12 K13 [K14l K14r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E Pd6e2d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6e2d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6e2d.kn0).
  { unfold know_ok, Pd6e2d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12; lia | clear - HV2l HV2r K0l K0r K12; lia | clear - HV2l HV2r K0l K0r K12; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12) | evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | clear - HV2l HV2r K0l K0r K12; lia | clear - HV2l HV2r K0l K0r K12; lia | byte_tac ltac:(clear - HV41l HV41r K6l K6r K7; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12) | evalEk ZA ltac:(clear - HV42l HV42r K8l K8r) | clear - HV2l HV2r K0l K0r K12; lia | clear - HV2l HV2r K0l K0r K12; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12) | evalEk ZA ltac:(clear - HV43l HV43r K9l K9r) | clear - HV2l HV2r K0l K0r K12; lia | clear - HV2l HV2r K0l K0r K12; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | clear; lia | rewrite (L5K.land1_bit0_true (V 41%nat) ltac:(clear - HV41l HV41r K6l K6r K7; lia) K7); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear - HV33l HV33r K10l K10r K12; lia | clear - HV33l HV33r K10l K10r K12; lia | byte_tac ltac:(clear - HV38l HV38r K14l K14r; lia) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_nil. }
  destruct (Pd6e2d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6e2d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd6e2d.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6e2d.ps0) with 0x22848 in Hms. change (SR.ps_regs Pd6e2d.ps0) with (map (fun i => (i, nth i Pd6e2d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6e2d.ps0) with Pd6e2d.cells0 in Hcells. unfold Pd6e2d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6e2d.regs0 Pd6e2d.regs_out0 80 KS_d6e2d KS_d6e2d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6e2d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd6e2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2d.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd6e2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6e2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd6e2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2d.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd6e2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2d.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd6e2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2d.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pd6e2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2d.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd6e2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd6e2d.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd6e2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6e2z := LibSegZ_d6e2z.
Definition KS_d6e2z : list nat := Eval vm_compute in (BG.kept_list 80 Pd6e2z.regs0 Pd6e2z.regs_out0).
Lemma KS_d6e2z_ok : BG.kept_ok 80 Pd6e2z.regs0 Pd6e2z.regs_out0 KS_d6e2z = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6e2z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 (V 36%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) 0 -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21dd4 M) (st fx' R' 0x22350 M')
        /\ (forall x, In x KS_d6e2z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 16
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 120)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV41l HV41r] G2 G9 G18 G23 G27 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 41%nat => (V 41%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E Pd6e2z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6e2z.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6e2z.kn0).
  { unfold know_ok, Pd6e2z.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K5l K5r K6) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K5l K5r K6; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K5l K5r K6) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K5l K5r K6) | clear; lia | rewrite (L5K.land1_bit0_false (V 41%nat) ltac:(clear - HV41l HV41r K5l K5r K6; lia) K6); clear; lia]. }
    apply Forall_nil. }
  destruct (Pd6e2z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6e2z.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd6e2z.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6e2z.ps0) with 0x22350 in Hms. change (SR.ps_regs Pd6e2z.ps0) with (map (fun i => (i, nth i Pd6e2z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6e2z.ps0) with Pd6e2z.cells0 in Hcells. unfold Pd6e2z.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6e2z.regs0 Pd6e2z.regs_out0 80 KS_d6e2z KS_d6e2z_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6e2z.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd6e2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6e2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2z.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd6e2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e2z.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pd6e2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd6e2z.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd6e2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6e4e := LibSegZ_d6e4e.
Definition KS_d6e4e : list nat := Eval vm_compute in (BG.kept_list 80 Pd6e4e.regs0 Pd6e4e.regs_out0).
Lemma KS_d6e4e_ok : BG.kept_ok 80 Pd6e4e.regs0 Pd6e4e.regs_out0 KS_d6e4e = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6e4e_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 10) = Z_to_bv 64 18446744073709551615 ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21e3c M) (st fx' R' 0x21e54 M')
        /\ (forall x, In x KS_d6e4e -> getr R' (reg x) = getr R (reg x))).
Proof.
  intros [HV2l HV2r] G2 G10 [K0l K0r] K1.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pd6e4e.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6e4e.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6e4e.kn0).
  { unfold know_ok, Pd6e4e.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_nil. }
  destruct (Pd6e4e.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6e4e.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd6e4e.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6e4e.ps0) with 0x21e54 in Hms. change (SR.ps_regs Pd6e4e.ps0) with (map (fun i => (i, nth i Pd6e4e.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6e4e.ps0) with Pd6e4e.cells0 in Hcells. unfold Pd6e4e.cells0 in Hcells.
  split. { exact Hms. }
  intros j Hj. apply (BG.kept_regs E E' R R' Pd6e4e.regs0 Pd6e4e.regs_out0 80 KS_d6e4e KS_d6e4e_ok HR Hag Hregs j Hj). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6e4g2 := LibSegZ_d6e4g2.
Definition KS_d6e4g2 : list nat := Eval vm_compute in (BG.kept_list 80 Pd6e4g2.regs0 Pd6e4g2.regs_out0).
Lemma KS_d6e4g2_ok : BG.kept_ok 80 Pd6e4g2.regs0 Pd6e4g2.regs_out0 KS_d6e4g2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6e4g2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 2 -> getr R (reg 21) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 168) (V 44%nat) ->
  0 <= (V 47%nat) <= 1 -> 0 <= (V 44%nat) <= 255 -> Z.testbit (V 44%nat) 0 = false -> 0 <= (V 37%nat) <= 1 ->
  1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 33%nat) (V 38%nat) ->
  0 <= (V 38%nat) <= 255 -> Z.testbit (V 38%nat) 0 = false -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21e3c M) (st fx' R' 0x2209c M')
        /\ (forall x, In x KS_d6e4g2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 35%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 37%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV37l HV37r] [HV38l HV38r] [HV44l HV44r] [HV47l HV47r] G2 G9 G10 G18 G19 G21 G23 [K0l K0r] K1 K2 K3 [K4l K4r] [K5l K5r] K6 [K7l K7r] [K8l K8r] K9 K10 K11 [K12l K12r] K13 [K14l K14r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 44%nat => (V 44%nat) | 47%nat => (V 47%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E Pd6e4g2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6e4g2.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6e4g2.kn0).
  { unfold know_ok, Pd6e4g2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV44l HV44r K5l K5r K6) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | byte_tac ltac:(clear - HV44l HV44r K5l K5r K6; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r K6) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r K6) | clear; lia | rewrite (L5K.land1_bit0_false (V 44%nat) ltac:(clear - HV44l HV44r K5l K5r K6; lia) K6); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10) | evalEk ZA ltac:(clear - HV38l HV38r K12l K12r K13) | clear - HV33l HV33r K8l K8r K10; lia | clear - HV33l HV33r K8l K8r K10; lia | byte_tac ltac:(clear - HV38l HV38r K12l K12r K13; lia) | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K12l K12r K13) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K12l K12r K13) | clear; lia | rewrite (L5K.land1_bit0_false (V 38%nat) ltac:(clear - HV38l HV38r K12l K12r K13; lia) K13); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_nil. }
  destruct (Pd6e4g2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6e4g2.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd6e4g2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6e4g2.ps0) with 0x2209c in Hms. change (SR.ps_regs Pd6e4g2.ps0) with (map (fun i => (i, nth i Pd6e4g2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6e4g2.ps0) with Pd6e4g2.cells0 in Hcells. unfold Pd6e4g2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6e4g2.regs0 Pd6e4g2.regs_out0 80 KS_d6e4g2 KS_d6e4g2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6e4g2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6e4g2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e4g2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd6e4g2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e4g2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd6e4g2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e4g2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd6e4g2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K7l K7r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6e4g1 := LibSegZ_d6e4g1.
Definition KS_d6e4g1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd6e4g1.regs0 Pd6e4g1.regs_out0).
Lemma KS_d6e4g1_ok : BG.kept_ok 80 Pd6e4g1.regs0 Pd6e4g1.regs_out0 KS_d6e4g1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6e4g1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 168) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 160) 2 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 63%nat) -> 0 <= (V 47%nat) <= 1 -> 0 <= (V 44%nat) <= 255 ->
  Z.testbit (V 44%nat) 0 = false -> 4294967296 <= (V 63%nat) <= 18446744073709551615 -> srl_range (V 63%nat) 4294967296 1 4294967295 -> 0 <= (V 37%nat) <= 1 ->
  1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 33%nat) (V 38%nat) ->
  0 <= (V 38%nat) <= 255 -> Z.testbit (V 38%nat) 0 = false -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21e3c M) (st fx' R' 0x2209c M')
        /\ (forall x, In x KS_d6e4g1 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = ((V 63%nat) / 4294967296)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 19) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 35%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 37%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV37l HV37r] [HV38l HV38r] [HV44l HV44r] [HV47l HV47r] [HV63l HV63r] G2 G9 G10 G18 G19 G21 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] [K7l K7r] K8 [K9l K9r] K10 [K11l K11r] [K12l K12r] K13 K14 K15 [K16l K16r] K17 [K18l K18r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 44%nat => (V 44%nat) | 47%nat => (V 47%nat) | 63%nat => (V 63%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 64%nat. }
  assert (HR: regs_ok E Pd6e4g1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6e4g1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6e4g1.kn0).
  { unfold know_ok, Pd6e4g1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV44l HV44r K7l K7r K8) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | byte_tac ltac:(clear - HV44l HV44r K7l K7r K8; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r K9l K9r K10) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV44l HV44r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_false (V 44%nat) ltac:(clear - HV44l HV44r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K9l K9r K10) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K17) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | byte_tac ltac:(clear - HV38l HV38r K16l K16r K17; lia) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K17) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K17) | clear; lia | rewrite (L5K.land1_bit0_false (V 38%nat) ltac:(clear - HV38l HV38r K16l K16r K17; lia) K17); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_nil. }
  destruct (Pd6e4g1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6e4g1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd6e4g1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6e4g1.ps0) with 0x2209c in Hms. change (SR.ps_regs Pd6e4g1.ps0) with (map (fun i => (i, nth i Pd6e4g1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6e4g1.ps0) with Pd6e4g1.cells0 in Hcells. unfold Pd6e4g1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6e4g1.regs0 Pd6e4g1.regs_out0 80 KS_d6e4g1 KS_d6e4g1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6e4g1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6e4g1.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg Pd6e4g1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd6e4g1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e4g1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd6e4g1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e4g1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd6e4g1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e4g1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd6e4g1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e4g1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd6e4g1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K11l K11r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6e4h := LibSegZ_d6e4h.
Definition KS_d6e4h : list nat := Eval vm_compute in (BG.kept_list 80 Pd6e4h.regs0 Pd6e4h.regs_out0).
Lemma KS_d6e4h_ok : BG.kept_ok 80 Pd6e4h.regs0 Pd6e4h.regs_out0 KS_d6e4h = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6e4h_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 168) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 160) 2 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 63%nat) -> 0 <= (V 47%nat) <= 1 -> 0 <= (V 44%nat) <= 255 ->
  Z.testbit (V 44%nat) 0 = false -> 1 <= (V 63%nat) <= 4294967295 -> srl_range (V 63%nat) 4294967296 0 0 -> 0 <= (V 37%nat) <= 1 ->
  1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 33%nat) (V 38%nat) ->
  0 <= (V 38%nat) <= 255 -> Z.testbit (V 38%nat) 0 = false -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21e3c M) (st fx' R' 0x21f9c M')
        /\ (forall x, In x KS_d6e4h -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 19) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 35%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 37%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV37l HV37r] [HV38l HV38r] [HV44l HV44r] [HV47l HV47r] [HV63l HV63r] G2 G9 G10 G18 G19 G21 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] [K7l K7r] K8 [K9l K9r] K10 [K11l K11r] [K12l K12r] K13 K14 K15 [K16l K16r] K17 [K18l K18r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 44%nat => (V 44%nat) | 47%nat => (V 47%nat) | 63%nat => (V 63%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 64%nat. }
  assert (HR: regs_ok E Pd6e4h.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6e4h.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6e4h.kn0).
  { unfold know_ok, Pd6e4h.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV44l HV44r K7l K7r K8) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | byte_tac ltac:(clear - HV44l HV44r K7l K7r K8; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r K9l K9r K10) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV44l HV44r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_false (V 44%nat) ltac:(clear - HV44l HV44r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K9l K9r K10) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K17) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | byte_tac ltac:(clear - HV38l HV38r K16l K16r K17; lia) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K17) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K17) | clear; lia | rewrite (L5K.land1_bit0_false (V 38%nat) ltac:(clear - HV38l HV38r K16l K16r K17; lia) K17); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_nil. }
  destruct (Pd6e4h.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6e4h.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd6e4h.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6e4h.ps0) with 0x21f9c in Hms. change (SR.ps_regs Pd6e4h.ps0) with (map (fun i => (i, nth i Pd6e4h.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6e4h.ps0) with Pd6e4h.cells0 in Hcells. unfold Pd6e4h.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6e4h.regs0 Pd6e4h.regs_out0 80 KS_d6e4h KS_d6e4h_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6e4h.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6e4h.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e4h.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd6e4h.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e4h.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd6e4h.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e4h.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd6e4h.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e4h.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd6e4h.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6e4h.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd6e4h.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K11l K11r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6g4i := LibSegZ_d6g4i.
Definition KS_d6g4i : list nat := Eval vm_compute in (BG.kept_list 80 Pd6g4i.regs0 Pd6g4i.regs_out0).
Lemma KS_d6g4i_ok : BG.kept_ok 80 Pd6g4i.regs0 Pd6g4i.regs_out0 KS_d6g4i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6g4i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 (V 64%nat) -> getr R (reg 24) = Z_to_bv 64 (V 68%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 65%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  1 <= (V 67%nat) <= 3 -> 1 <= (V 65%nat) <= 300 -> 0 <= (V 64%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> ~ (((V 2%nat) - 264) <= bv_unsigned a < ((V 2%nat) - 264) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 296) <= i < ((V 2%nat) - 296) + 8) -> ~ (((V 2%nat) - 264) <= i < ((V 2%nat) - 264) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x220d4 M) (st fx' R' 0x210bc M')
        /\ (forall x, In x KS_d6g4i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139520
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 65%nat) - (V 67%nat))
        /\ getr R' (reg 19) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) (V 68%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 64%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV41l HV41r] [HV64l HV64r] [HV65l HV65r] [HV67l HV67r] [HV68l HV68r] G2 G9 G10 G24 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] [K9l K9r] [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 41%nat => (V 41%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | 67%nat => (V 67%nat) | 68%nat => (V 68%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E Pd6g4i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6g4i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6g4i.kn0).
  { unfold know_ok, Pd6g4i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K6l K6r K7; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV67l HV67r K8l K8r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV65l HV65r K9l K9r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | clear; lia | rewrite (L5K.land1_bit0_false (V 41%nat) ltac:(clear - HV41l HV41r K6l K6r K7; lia) K7); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (Pd6g4i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6g4i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> ~ (((V 2%nat) - 264) <= bv_unsigned a < ((V 2%nat) - 264) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd6g4i.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6g4i.ps0) with 0x210bc in Hms. change (SR.ps_regs Pd6g4i.ps0) with (map (fun i => (i, nth i Pd6g4i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6g4i.ps0) with Pd6g4i.cells0 in Hcells. unfold Pd6g4i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6g4i.regs0 Pd6g4i.regs_out0 80 KS_d6g4i KS_d6g4i_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6g4i.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd6g4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g4i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6g4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g4i.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd6g4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g4i.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd6g4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g4i.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd6g4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV68l HV68r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV64l HV64r K10l K10r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6g4d := LibSegZ_d6g4d.
Definition KS_d6g4d : list nat := Eval vm_compute in (BG.kept_list 80 Pd6g4d.regs0 Pd6g4d.regs_out0).
Lemma KS_d6g4d_ok : BG.kept_ok 80 Pd6g4d.regs0 Pd6g4d.regs_out0 KS_d6g4d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6g4d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 (V 64%nat) -> getr R (reg 24) = Z_to_bv 64 (V 68%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 65%nat) -> 0 <= (V 41%nat) <= 255 ->
  Z.testbit (V 41%nat) 0 = true -> 1 <= (V 67%nat) <= 3 -> 1 <= (V 65%nat) <= 300 -> 0 <= (V 64%nat) <= 1 ->
  0 <= (V 66%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> ~ (((V 2%nat) - 264) <= bv_unsigned a < ((V 2%nat) - 264) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 296) <= i < ((V 2%nat) - 296) + 8) -> ~ (((V 2%nat) - 264) <= i < ((V 2%nat) - 264) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x220d4 M) (st fx' R' 0x210bc M')
        /\ (forall x, In x KS_d6g4d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139520
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 65%nat) - (V 67%nat))
        /\ getr R' (reg 19) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) (V 68%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 64%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV41l HV41r] [HV64l HV64r] [HV65l HV65r] [HV66l HV66r] [HV67l HV67r] [HV68l HV68r] G2 G9 G10 G24 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r] K8 [K9l K9r] [K10l K10r] [K11l K11r] [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 41%nat => (V 41%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 68%nat => (V 68%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E Pd6g4d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6g4d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6g4d.kn0).
  { unfold know_ok, Pd6g4d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K7l K7r K8) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K7l K7r K8; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV67l HV67r K9l K9r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV66l HV66r K12l K12r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV65l HV65r K10l K10r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_true (V 41%nat) ltac:(clear - HV41l HV41r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  destruct (Pd6g4d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6g4d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> ~ (((V 2%nat) - 264) <= bv_unsigned a < ((V 2%nat) - 264) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd6g4d.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6g4d.ps0) with 0x210bc in Hms. change (SR.ps_regs Pd6g4d.ps0) with (map (fun i => (i, nth i Pd6g4d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6g4d.ps0) with Pd6g4d.cells0 in Hcells. unfold Pd6g4d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6g4d.regs0 Pd6g4d.regs_out0 80 KS_d6g4d KS_d6g4d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6g4d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd6g4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g4d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6g4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g4d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd6g4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g4d.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd6g4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g4d.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pd6g4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g4d.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd6g4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV68l HV68r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV64l HV64r K11l K11r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6g5i := LibSegZ_d6g5i.
Definition KS_d6g5i_0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd6g5i.regs0 Pd6g5i.regs_out0).
Lemma KS_d6g5i_0_ok : BG.kept_ok 80 Pd6g5i.regs0 Pd6g5i.regs_out0 KS_d6g5i_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_d6g5i_1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd6g5i.regs0 Pd6g5i.regs_out1).
Lemma KS_d6g5i_1_ok : BG.kept_ok 80 Pd6g5i.regs0 Pd6g5i.regs_out1 KS_d6g5i_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6g5i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 264) (V 68%nat) ->
  1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) ->
  0 <= (V 69%nat) <= 255 -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 70%nat) -> Z.testbit (V 69%nat) 0 = false -> 0 <= (V 70%nat) <= 300 ->
  0 <= (V 68%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x22100 M) (st fx' R' 0x58ea4 M')
        /\ (forall x, In x KS_d6g5i_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139564
        /\ getr R' (reg 10) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (8 * (V 70%nat))
        /\ getr R' (reg 24) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 70%nat)
        /\ 1 <= (V 70%nat) <= 300)
      \/ (msteps RSEGS (st fx R 0x22100 M) (st fx' R' 0x2212c M')
        /\ (forall x, In x KS_d6g5i_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 70%nat)
        /\ 0 <= (V 70%nat) <= 0)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV68l HV68r] [HV69l HV69r] [HV70l HV70r] G2 G9 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 [K8l K8r] K9 K10 [K11l K11r] [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | 70%nat => (V 70%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 71%nat. }
  assert (HR: regs_ok E Pd6g5i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6g5i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6g5i.kn0).
  { unfold know_ok, Pd6g5i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV68l HV68r K12l K12r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K10) | clear - HV35l HV35r K4l K4r K6; lia | clear - HV35l HV35r K4l K4r K6; lia | byte_tac ltac:(clear - HV69l HV69r K8l K8r K10; lia) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K10) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | evalEk ZA ltac:(clear - HV70l HV70r K11l K11r) | clear - HV35l HV35r K4l K4r K6; lia | clear - HV35l HV35r K4l K4r K6; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K10) | clear; lia | rewrite (L5K.land1_bit0_false (V 69%nat) ltac:(clear - HV69l HV69r K8l K8r K10; lia) K10); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  destruct (Pd6g5i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6g5i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd6g5i.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc Pd6g5i.ps0) with 0x58ea4 in Hms. change (SR.ps_regs Pd6g5i.ps0) with (map (fun i => (i, nth i Pd6g5i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pd6g5i.ps0) with Pd6g5i.cells0 in Hcells. unfold Pd6g5i.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6g5i.regs0 Pd6g5i.regs_out0 80 KS_d6g5i_0 KS_d6g5i_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pd6g5i.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd6g5i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd6g5i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6g5i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd6g5i.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd6g5i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd6g5i.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd6g5i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd6g5i.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd6g5i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd6g5i.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pd6g5i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV70l HV70r K11l K11r)]. 
  - right.
    change (SR.ps_pc Pd6g5i.ps1) with 0x2212c in Hms. change (SR.ps_regs Pd6g5i.ps1) with (map (fun i => (i, nth i Pd6g5i.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pd6g5i.ps1) with Pd6g5i.cells1 in Hcells. unfold Pd6g5i.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6g5i.regs0 Pd6g5i.regs_out1 80 KS_d6g5i_1 KS_d6g5i_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pd6g5i.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6g5i.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd6g5i.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd6g5i.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd6g5i.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth Pd6g5i.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV70l HV70r K11l K11r)]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6g7i0 := LibSegZ_d6g7i0.
Definition KS_d6g7i0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd6g7i0.regs0 Pd6g7i0.regs_out0).
Lemma KS_d6g7i0_ok : BG.kept_ok 80 Pd6g7i0.regs0 Pd6g7i0.regs_out0 KS_d6g7i0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6g7i0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 61%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 20) = Z_to_bv 64 (V 66%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 26) = Z_to_bv 64 (V 62%nat) -> getr R (reg 27) = Z_to_bv 64 (V 36%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> 4096 <= (V 66%nat) <= 140737488355328 ->
  aligned (V 66%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 66%nat) \/ (V 66%nat) + 64 <= ((V 2%nat) - 304)) -> 2 <= (V 67%nat) <= 3 -> L5.u64_at RSEGS M (((V 66%nat) + (8 * (V 67%nat))) - 8) (V 74%nat) ->
  (((V 2%nat) - 304) + 304 <= (((V 66%nat) + (8 * (V 67%nat))) - 8) \/ (((V 66%nat) + (8 * (V 67%nat))) - 8) + 8 <= ((V 2%nat) - 304)) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (((V 2%nat) - 304) + 304 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = false ->
  L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 65%nat))) + 8) (V 73%nat) -> (((V 2%nat) - 304) + 304 <= (((V 36%nat) + (8 * (V 65%nat))) + 8) \/ (((V 36%nat) + (8 * (V 65%nat))) + 8) + 8 <= ((V 2%nat) - 304)) -> 0 <= (V 73%nat) <= 18446744073709551615 -> 1 <= (V 65%nat) <= 2 ->
  (V 73%nat) < (V 74%nat) -> 0 <= (V 61%nat) <= 1 -> 0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 288) <= i < ((V 2%nat) - 288) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22138 M) (st fx' R' 0x221d4 M')
        /\ (forall x, In x KS_d6g7i0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 67%nat) - 1)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ getr R' (reg 27) = Z_to_bv 64 (((V 66%nat) + (8 * (V 67%nat))) - 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (V 61%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV66l HV66r] [HV67l HV67r] [HV71l HV71r] [HV73l HV73r] [HV74l HV74r] G2 G8 G19 G20 G21 G26 G27 [K0l K0r] K1 K2 [K3l K3r] K4 K5 [K6l K6r] K7 K8 [K9l K9r] [K10l K10r] K11 K12 K13 [K14l K14r] K15 K16 K17 [K18l K18r] [K19l K19r] K20 [K21l K21r] [K22l K22r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 71%nat => (V 71%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd6g7i0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6g7i0.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6g7i0.kn0).
  { unfold know_ok, Pd6g7i0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K12 K17; lia | clear - HV2l HV2r K0l K0r K5 K8 K12 K17; lia | clear - HV2l HV2r K0l K0r K5 K8 K12 K17; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K6l K6r K8) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r) | evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K20) | clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r; lia | clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K20) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K17) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K17) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K17) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K17) | evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K15) | clear - HV36l HV36r K10l K10r K12 K17; lia | clear - HV36l HV36r K10l K10r K12 K17; lia | byte_tac ltac:(clear - HV71l HV71r K14l K14r K15; lia) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K15) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K15) | clear; lia | rewrite (L5K.land1_bit0_false (V 71%nat) ltac:(clear - HV71l HV71r K14l K14r K15; lia) K15); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K17 HV65l HV65r K19l K19r) | evalEk ZA ltac:(clear - HV73l HV73r K18l K18r K20) | clear - HV36l HV36r K10l K10r K12 K17 HV65l HV65r K19l K19r; lia | clear - HV36l HV36r K10l K10r K12 K17 HV65l HV65r K19l K19r; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K17 HV65l HV65r K19l K19r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K18l K18r K20) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K17 K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K20; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_nil. }
  destruct (Pd6g7i0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6g7i0.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd6g7i0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K12 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6g7i0.ps0) with 0x221d4 in Hms. change (SR.ps_regs Pd6g7i0.ps0) with (map (fun i => (i, nth i Pd6g7i0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6g7i0.ps0) with Pd6g7i0.cells0 in Hcells. unfold Pd6g7i0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6g7i0.regs0 Pd6g7i0.regs_out0 80 KS_d6g7i0 KS_d6g7i0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6g7i0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd6g7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7i0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6g7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7i0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd6g7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7i0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd6g7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7i0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd6g7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7i0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd6g7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7i0.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pd6g7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K10l K10r K12 K17) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K22l K22r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K21l K21r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6g7i1 := LibSegZ_d6g7i1.
Definition KS_d6g7i1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd6g7i1.regs0 Pd6g7i1.regs_out0).
Lemma KS_d6g7i1_ok : BG.kept_ok 80 Pd6g7i1.regs0 Pd6g7i1.regs_out0 KS_d6g7i1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6g7i1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 61%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 20) = Z_to_bv 64 (V 66%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 26) = Z_to_bv 64 (V 62%nat) -> getr R (reg 27) = Z_to_bv 64 (V 36%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> 4096 <= (V 66%nat) <= 140737488355328 ->
  aligned (V 66%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 66%nat) \/ (V 66%nat) + 64 <= ((V 2%nat) - 304)) -> 2 <= (V 67%nat) <= 3 -> L5.u64_at RSEGS M (((V 66%nat) + (8 * (V 67%nat))) - 8) (V 74%nat) ->
  (((V 2%nat) - 304) + 304 <= (((V 66%nat) + (8 * (V 67%nat))) - 8) \/ (((V 66%nat) + (8 * (V 67%nat))) - 8) + 8 <= ((V 2%nat) - 304)) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (((V 2%nat) - 304) + 304 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = false ->
  L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 65%nat))) + 8) (V 73%nat) -> (((V 2%nat) - 304) + 304 <= (((V 36%nat) + (8 * (V 65%nat))) + 8) \/ (((V 36%nat) + (8 * (V 65%nat))) + 8) + 8 <= ((V 2%nat) - 304)) -> 0 <= (V 73%nat) <= 18446744073709551615 -> 1 <= (V 65%nat) <= 2 ->
  (V 74%nat) <= (V 73%nat) -> 0 <= (V 61%nat) <= 1 -> 0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 288) <= i < ((V 2%nat) - 288) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22138 M) (st fx' R' 0x22180 M')
        /\ (forall x, In x KS_d6g7i1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 67%nat) - 1)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ getr R' (reg 27) = Z_to_bv 64 (((V 66%nat) + (8 * (V 67%nat))) - 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (V 61%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV66l HV66r] [HV67l HV67r] [HV71l HV71r] [HV73l HV73r] [HV74l HV74r] G2 G8 G19 G20 G21 G26 G27 [K0l K0r] K1 K2 [K3l K3r] K4 K5 [K6l K6r] K7 K8 [K9l K9r] [K10l K10r] K11 K12 K13 [K14l K14r] K15 K16 K17 [K18l K18r] [K19l K19r] K20 [K21l K21r] [K22l K22r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 71%nat => (V 71%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd6g7i1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6g7i1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6g7i1.kn0).
  { unfold know_ok, Pd6g7i1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K12 K17; lia | clear - HV2l HV2r K0l K0r K5 K8 K12 K17; lia | clear - HV2l HV2r K0l K0r K5 K8 K12 K17; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K6l K6r K8) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r) | evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K20) | clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r; lia | clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K20) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K17) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K17) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K17) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K17) | evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K15) | clear - HV36l HV36r K10l K10r K12 K17; lia | clear - HV36l HV36r K10l K10r K12 K17; lia | byte_tac ltac:(clear - HV71l HV71r K14l K14r K15; lia) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K15) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K15) | clear; lia | rewrite (L5K.land1_bit0_false (V 71%nat) ltac:(clear - HV71l HV71r K14l K14r K15; lia) K15); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K17 HV65l HV65r K19l K19r) | evalEk ZA ltac:(clear - HV73l HV73r K18l K18r K20) | clear - HV36l HV36r K10l K10r K12 K17 HV65l HV65r K19l K19r; lia | clear - HV36l HV36r K10l K10r K12 K17 HV65l HV65r K19l K19r; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K17 HV65l HV65r K19l K19r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K18l K18r K20) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K17 K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K20; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_nil. }
  destruct (Pd6g7i1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6g7i1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd6g7i1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K12 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6g7i1.ps0) with 0x22180 in Hms. change (SR.ps_regs Pd6g7i1.ps0) with (map (fun i => (i, nth i Pd6g7i1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6g7i1.ps0) with Pd6g7i1.cells0 in Hcells. unfold Pd6g7i1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6g7i1.regs0 Pd6g7i1.regs_out0 80 KS_d6g7i1 KS_d6g7i1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6g7i1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd6g7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7i1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6g7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7i1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd6g7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7i1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd6g7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7i1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd6g7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7i1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd6g7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7i1.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pd6g7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K10l K10r K12 K17) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K22l K22r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K17) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K21l K21r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6g7d0 := LibSegZ_d6g7d0.
Definition KS_d6g7d0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd6g7d0.regs0 Pd6g7d0.regs_out0).
Lemma KS_d6g7d0_ok : BG.kept_ok 80 Pd6g7d0.regs0 Pd6g7d0.regs_out0 KS_d6g7d0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6g7d0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 61%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 20) = Z_to_bv 64 (V 66%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 26) = Z_to_bv 64 (V 62%nat) -> getr R (reg 27) = Z_to_bv 64 (V 36%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> 4096 <= (V 66%nat) <= 140737488355328 ->
  aligned (V 66%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 66%nat) \/ (V 66%nat) + 64 <= ((V 2%nat) - 304)) -> 2 <= (V 67%nat) <= 3 -> L5.u64_at RSEGS M (((V 66%nat) + (8 * (V 67%nat))) - 8) (V 74%nat) ->
  (((V 2%nat) - 304) + 304 <= (((V 66%nat) + (8 * (V 67%nat))) - 8) \/ (((V 66%nat) + (8 * (V 67%nat))) - 8) + 8 <= ((V 2%nat) - 304)) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (((V 2%nat) - 304) + 304 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 36%nat) + 24) (V 72%nat) -> 4096 <= (V 72%nat) <= 140737488355328 -> aligned (V 72%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 72%nat) \/ (V 72%nat) + 64 <= ((V 2%nat) - 304)) ->
  L5.u64_at RSEGS M (((8 * (V 65%nat)) + (V 72%nat)) - 8) (V 73%nat) -> (((V 2%nat) - 304) + 304 <= (((8 * (V 65%nat)) + (V 72%nat)) - 8) \/ (((8 * (V 65%nat)) + (V 72%nat)) - 8) + 8 <= ((V 2%nat) - 304)) -> 0 <= (V 73%nat) <= 18446744073709551615 -> 1 <= (V 65%nat) <= 7 ->
  (V 73%nat) < (V 74%nat) -> 0 <= (V 61%nat) <= 1 -> 0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 288) <= i < ((V 2%nat) - 288) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22138 M) (st fx' R' 0x221d4 M')
        /\ (forall x, In x KS_d6g7d0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 67%nat) - 1)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ getr R' (reg 27) = Z_to_bv 64 (((V 66%nat) + (8 * (V 67%nat))) - 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (V 61%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV66l HV66r] [HV67l HV67r] [HV71l HV71r] [HV72l HV72r] [HV73l HV73r] [HV74l HV74r] G2 G8 G19 G20 G21 G26 G27 [K0l K0r] K1 K2 [K3l K3r] K4 K5 [K6l K6r] K7 K8 [K9l K9r] [K10l K10r] K11 K12 K13 [K14l K14r] K15 K16 [K17l K17r] K18 K19 K20 K21 [K22l K22r] [K23l K23r] K24 [K25l K25r] [K26l K26r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd6g7d0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6g7d0.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6g7d0.kn0).
  { unfold know_ok, Pd6g7d0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21; lia | clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21; lia | clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K6l K6r K8) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r) | evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K24) | clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r; lia | clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K24) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K15) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | byte_tac ltac:(clear - HV71l HV71r K14l K14r K15; lia) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K15) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K15) | clear; lia | rewrite (L5K.land1_bit0_true (V 71%nat) ltac:(clear - HV71l HV71r K14l K14r K15; lia) K15); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV72l HV72r K17l K17r K19 K21) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K17l K17r K19 K21) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV72l HV72r K17l K17r K19 K21) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV72l HV72r K17l K17r K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV65l HV65r K21 K23l K23r HV72l HV72r K17l K17r K19) | evalEk ZA ltac:(clear - HV73l HV73r K22l K22r K24) | clear - HV65l HV65r K21 K23l K23r HV72l HV72r K17l K17r K19; lia | clear - HV65l HV65r K21 K23l K23r HV72l HV72r K17l K17r K19; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K21 K23l K23r HV72l HV72r K17l K17r K19) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K22l K22r K24) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K21 K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K24; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  destruct (Pd6g7d0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6g7d0.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd6g7d0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6g7d0.ps0) with 0x221d4 in Hms. change (SR.ps_regs Pd6g7d0.ps0) with (map (fun i => (i, nth i Pd6g7d0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6g7d0.ps0) with Pd6g7d0.cells0 in Hcells. unfold Pd6g7d0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6g7d0.regs0 Pd6g7d0.regs_out0 80 KS_d6g7d0 KS_d6g7d0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6g7d0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd6g7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7d0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6g7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7d0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd6g7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7d0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd6g7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7d0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd6g7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7d0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd6g7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7d0.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pd6g7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K10l K10r K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K26l K26r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K25l K25r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6g7d1 := LibSegZ_d6g7d1.
Definition KS_d6g7d1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd6g7d1.regs0 Pd6g7d1.regs_out0).
Lemma KS_d6g7d1_ok : BG.kept_ok 80 Pd6g7d1.regs0 Pd6g7d1.regs_out0 KS_d6g7d1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6g7d1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 61%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 20) = Z_to_bv 64 (V 66%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 26) = Z_to_bv 64 (V 62%nat) -> getr R (reg 27) = Z_to_bv 64 (V 36%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> 4096 <= (V 66%nat) <= 140737488355328 ->
  aligned (V 66%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 66%nat) \/ (V 66%nat) + 64 <= ((V 2%nat) - 304)) -> 2 <= (V 67%nat) <= 3 -> L5.u64_at RSEGS M (((V 66%nat) + (8 * (V 67%nat))) - 8) (V 74%nat) ->
  (((V 2%nat) - 304) + 304 <= (((V 66%nat) + (8 * (V 67%nat))) - 8) \/ (((V 66%nat) + (8 * (V 67%nat))) - 8) + 8 <= ((V 2%nat) - 304)) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (((V 2%nat) - 304) + 304 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 36%nat) + 24) (V 72%nat) -> 4096 <= (V 72%nat) <= 140737488355328 -> aligned (V 72%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 72%nat) \/ (V 72%nat) + 64 <= ((V 2%nat) - 304)) ->
  L5.u64_at RSEGS M (((8 * (V 65%nat)) + (V 72%nat)) - 8) (V 73%nat) -> (((V 2%nat) - 304) + 304 <= (((8 * (V 65%nat)) + (V 72%nat)) - 8) \/ (((8 * (V 65%nat)) + (V 72%nat)) - 8) + 8 <= ((V 2%nat) - 304)) -> 0 <= (V 73%nat) <= 18446744073709551615 -> 1 <= (V 65%nat) <= 7 ->
  (V 74%nat) <= (V 73%nat) -> 0 <= (V 61%nat) <= 1 -> 0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 288) <= i < ((V 2%nat) - 288) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22138 M) (st fx' R' 0x22180 M')
        /\ (forall x, In x KS_d6g7d1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 67%nat) - 1)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ getr R' (reg 27) = Z_to_bv 64 (((V 66%nat) + (8 * (V 67%nat))) - 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (V 61%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV66l HV66r] [HV67l HV67r] [HV71l HV71r] [HV72l HV72r] [HV73l HV73r] [HV74l HV74r] G2 G8 G19 G20 G21 G26 G27 [K0l K0r] K1 K2 [K3l K3r] K4 K5 [K6l K6r] K7 K8 [K9l K9r] [K10l K10r] K11 K12 K13 [K14l K14r] K15 K16 [K17l K17r] K18 K19 K20 K21 [K22l K22r] [K23l K23r] K24 [K25l K25r] [K26l K26r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd6g7d1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6g7d1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6g7d1.kn0).
  { unfold know_ok, Pd6g7d1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21; lia | clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21; lia | clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K6l K6r K8) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r) | evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K24) | clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r; lia | clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV66l HV66r K3l K3r K5 K8 HV67l HV67r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K24) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K15) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | byte_tac ltac:(clear - HV71l HV71r K14l K14r K15; lia) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K15) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K15) | clear; lia | rewrite (L5K.land1_bit0_true (V 71%nat) ltac:(clear - HV71l HV71r K14l K14r K15; lia) K15); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV72l HV72r K17l K17r K19 K21) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K17l K17r K19 K21) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV72l HV72r K17l K17r K19 K21) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV72l HV72r K17l K17r K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV65l HV65r K21 K23l K23r HV72l HV72r K17l K17r K19) | evalEk ZA ltac:(clear - HV73l HV73r K22l K22r K24) | clear - HV65l HV65r K21 K23l K23r HV72l HV72r K17l K17r K19; lia | clear - HV65l HV65r K21 K23l K23r HV72l HV72r K17l K17r K19; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K21 K23l K23r HV72l HV72r K17l K17r K19) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K22l K22r K24) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K21 K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K24; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  destruct (Pd6g7d1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6g7d1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd6g7d1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6g7d1.ps0) with 0x22180 in Hms. change (SR.ps_regs Pd6g7d1.ps0) with (map (fun i => (i, nth i Pd6g7d1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6g7d1.ps0) with Pd6g7d1.cells0 in Hcells. unfold Pd6g7d1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6g7d1.regs0 Pd6g7d1.regs_out0 80 KS_d6g7d1 KS_d6g7d1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6g7d1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd6g7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7d1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6g7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7d1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd6g7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7d1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd6g7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7d1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd6g7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7d1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd6g7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g7d1.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pd6g7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K10l K10r K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K26l K26r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K12 K19 K21) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K25l K25r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6g10ii := LibSegZ_d6g10ii.
Definition KS_d6g10ii : list nat := Eval vm_compute in (BG.kept_list 80 Pd6g10ii.regs0 Pd6g10ii.regs_out0).
Lemma KS_d6g10ii_ok : BG.kept_ok 80 Pd6g10ii.regs0 Pd6g10ii.regs_out0 KS_d6g10ii = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6g10ii_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 ((V 36%nat) + 16) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 23) = Z_to_bv 64 (V 72%nat) -> getr R (reg 24) = Z_to_bv 64 (V 71%nat) -> getr R (reg 27) = Z_to_bv 64 (V 79%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 264) (V 68%nat) ->
  0 <= (V 68%nat) <= 18446744073709551615 -> 0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = false -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 ->
  Z.testbit (V 69%nat) 0 = false -> 4096 <= (V 79%nat) <= 140737488355328 -> aligned (V 79%nat) 8 -> L5.u64_at RSEGS M (V 79%nat) (V 74%nat) ->
  0 <= (V 74%nat) <= 18446744073709551615 -> 0 <= (V 72%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x221a8 M) (st fx' R' 0x221d4 M')
        /\ (forall x, In x KS_d6g10ii -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 65%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV36l HV36r] [HV65l HV65r] [HV68l HV68r] [HV69l HV69r] [HV71l HV71r] [HV72l HV72r] [HV74l HV74r] [HV79l HV79r] G2 G8 G9 G19 G23 G24 G27 [K0l K0r] K1 K2 K3 [K4l K4r] [K5l K5r] K6 [K7l K7r] K8 K9 K10 [K11l K11r] K12 [K13l K13r] K14 K15 [K16l K16r] [K17l K17r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 65%nat => (V 65%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 74%nat => (V 74%nat) | 79%nat => (V 79%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E Pd6g10ii.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6g10ii.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6g10ii.kn0).
  { unfold know_ok, Pd6g10ii.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV68l HV68r K4l K4r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K5l K5r K6) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K5l K5r K6) | clear; lia | rewrite (L5K.land1_bit0_false (V 71%nat) ltac:(clear - HV71l HV71r K5l K5r K6; lia) K6); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk ZA ltac:(clear - HV69l HV69r K11l K11r K12) | clear - HV35l HV35r K7l K7r K9; lia | clear - HV35l HV35r K7l K7r K9; lia | byte_tac ltac:(clear - HV69l HV69r K11l K11r K12; lia) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K11l K11r K12) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K11l K11r K12) | clear; lia | rewrite (L5K.land1_bit0_false (V 69%nat) ltac:(clear - HV69l HV69r K11l K11r K12; lia) K12); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV79l HV79r K13l K13r) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV79l HV79r K13l K13r) | evalEk ZA ltac:(clear - HV74l HV74r K16l K16r) | clear - HV79l HV79r K13l K13r; lia | clear - HV79l HV79r K13l K13r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  destruct (Pd6g10ii.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6g10ii.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd6g10ii.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6g10ii.ps0) with 0x221d4 in Hms. change (SR.ps_regs Pd6g10ii.ps0) with (map (fun i => (i, nth i Pd6g10ii.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6g10ii.ps0) with Pd6g10ii.cells0 in Hcells. unfold Pd6g10ii.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6g10ii.regs0 Pd6g10ii.regs_out0 80 KS_d6g10ii KS_d6g10ii_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6g10ii.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6g10ii.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g10ii.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd6g10ii.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g10ii.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd6g10ii.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd6g10ii.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd6g10ii.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6g10id := LibSegZ_d6g10id.
Definition KS_d6g10id : list nat := Eval vm_compute in (BG.kept_list 80 Pd6g10id.regs0 Pd6g10id.regs_out0).
Lemma KS_d6g10id_ok : BG.kept_ok 80 Pd6g10id.regs0 Pd6g10id.regs_out0 KS_d6g10id = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6g10id_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 ((V 36%nat) + 16) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 23) = Z_to_bv 64 (V 72%nat) -> getr R (reg 24) = Z_to_bv 64 (V 71%nat) -> getr R (reg 27) = Z_to_bv 64 (V 79%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 264) (V 68%nat) ->
  0 <= (V 68%nat) <= 18446744073709551615 -> 0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = false -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 ->
  Z.testbit (V 69%nat) 0 = true -> L5.u64_at RSEGS M ((V 35%nat) + 24) (V 78%nat) -> 0 <= (V 78%nat) <= 18446744073709551615 -> 4096 <= (V 79%nat) <= 140737488355328 ->
  aligned (V 79%nat) 8 -> L5.u64_at RSEGS M (V 79%nat) (V 74%nat) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 0 <= (V 72%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x221a8 M) (st fx' R' 0x221d4 M')
        /\ (forall x, In x KS_d6g10id -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 78%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 65%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV36l HV36r] [HV65l HV65r] [HV68l HV68r] [HV69l HV69r] [HV71l HV71r] [HV72l HV72r] [HV74l HV74r] [HV78l HV78r] [HV79l HV79r] G2 G8 G9 G19 G23 G24 G27 [K0l K0r] K1 K2 K3 [K4l K4r] [K5l K5r] K6 [K7l K7r] K8 K9 K10 [K11l K11r] K12 K13 [K14l K14r] [K15l K15r] K16 K17 [K18l K18r] [K19l K19r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 65%nat => (V 65%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 74%nat => (V 74%nat) | 78%nat => (V 78%nat) | 79%nat => (V 79%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E Pd6g10id.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6g10id.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6g10id.kn0).
  { unfold know_ok, Pd6g10id.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV68l HV68r K4l K4r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K5l K5r K6) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K5l K5r K6) | clear; lia | rewrite (L5K.land1_bit0_false (V 71%nat) ltac:(clear - HV71l HV71r K5l K5r K6; lia) K6); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk ZA ltac:(clear - HV69l HV69r K11l K11r K12) | clear - HV35l HV35r K7l K7r K9; lia | clear - HV35l HV35r K7l K7r K9; lia | byte_tac ltac:(clear - HV69l HV69r K11l K11r K12; lia) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K11l K11r K12) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K11l K11r K12) | clear; lia | rewrite (L5K.land1_bit0_true (V 69%nat) ltac:(clear - HV69l HV69r K11l K11r K12; lia) K12); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk ZA ltac:(clear - HV78l HV78r K14l K14r) | clear - HV35l HV35r K7l K7r K9; lia | clear - HV35l HV35r K7l K7r K9; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV79l HV79r K15l K15r) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV79l HV79r K15l K15r) | evalEk ZA ltac:(clear - HV74l HV74r K18l K18r) | clear - HV79l HV79r K15l K15r; lia | clear - HV79l HV79r K15l K15r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_nil. }
  destruct (Pd6g10id.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6g10id.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd6g10id.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6g10id.ps0) with 0x221d4 in Hms. change (SR.ps_regs Pd6g10id.ps0) with (map (fun i => (i, nth i Pd6g10id.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6g10id.ps0) with Pd6g10id.cells0 in Hcells. unfold Pd6g10id.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6g10id.regs0 Pd6g10id.regs_out0 80 KS_d6g10id KS_d6g10id_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6g10id.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6g10id.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g10id.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd6g10id.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g10id.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd6g10id.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd6g10id.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd6g10id.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6g10di := LibSegZ_d6g10di.
Definition KS_d6g10di : list nat := Eval vm_compute in (BG.kept_list 80 Pd6g10di.regs0 Pd6g10di.regs_out0).
Lemma KS_d6g10di_ok : BG.kept_ok 80 Pd6g10di.regs0 Pd6g10di.regs_out0 KS_d6g10di = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6g10di_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 23) = Z_to_bv 64 (V 72%nat) -> getr R (reg 24) = Z_to_bv 64 (V 71%nat) -> getr R (reg 27) = Z_to_bv 64 (V 79%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 264) (V 68%nat) ->
  0 <= (V 68%nat) <= 18446744073709551615 -> 0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = true -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 ->
  Z.testbit (V 69%nat) 0 = false -> 4096 <= (V 79%nat) <= 140737488355328 -> aligned (V 79%nat) 8 -> L5.u64_at RSEGS M (V 79%nat) (V 74%nat) ->
  0 <= (V 74%nat) <= 18446744073709551615 -> 0 <= (V 72%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x221a8 M) (st fx' R' 0x221d4 M')
        /\ (forall x, In x KS_d6g10di -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 65%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV65l HV65r] [HV68l HV68r] [HV69l HV69r] [HV71l HV71r] [HV72l HV72r] [HV74l HV74r] [HV79l HV79r] G2 G9 G19 G23 G24 G27 [K0l K0r] K1 K2 K3 [K4l K4r] [K5l K5r] K6 [K7l K7r] K8 K9 K10 [K11l K11r] K12 [K13l K13r] K14 K15 [K16l K16r] [K17l K17r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 65%nat => (V 65%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 74%nat => (V 74%nat) | 79%nat => (V 79%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E Pd6g10di.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6g10di.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6g10di.kn0).
  { unfold know_ok, Pd6g10di.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV68l HV68r K4l K4r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K5l K5r K6) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K5l K5r K6) | clear; lia | rewrite (L5K.land1_bit0_true (V 71%nat) ltac:(clear - HV71l HV71r K5l K5r K6; lia) K6); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk ZA ltac:(clear - HV69l HV69r K11l K11r K12) | clear - HV35l HV35r K7l K7r K9; lia | clear - HV35l HV35r K7l K7r K9; lia | byte_tac ltac:(clear - HV69l HV69r K11l K11r K12; lia) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K11l K11r K12) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K11l K11r K12) | clear; lia | rewrite (L5K.land1_bit0_false (V 69%nat) ltac:(clear - HV69l HV69r K11l K11r K12; lia) K12); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV79l HV79r K13l K13r) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV79l HV79r K13l K13r) | evalEk ZA ltac:(clear - HV74l HV74r K16l K16r) | clear - HV79l HV79r K13l K13r; lia | clear - HV79l HV79r K13l K13r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  destruct (Pd6g10di.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6g10di.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd6g10di.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6g10di.ps0) with 0x221d4 in Hms. change (SR.ps_regs Pd6g10di.ps0) with (map (fun i => (i, nth i Pd6g10di.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6g10di.ps0) with Pd6g10di.cells0 in Hcells. unfold Pd6g10di.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6g10di.regs0 Pd6g10di.regs_out0 80 KS_d6g10di KS_d6g10di_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6g10di.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd6g10di.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g10di.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6g10di.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g10di.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd6g10di.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g10di.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd6g10di.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd6g10di.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd6g10di.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6g10dd := LibSegZ_d6g10dd.
Definition KS_d6g10dd : list nat := Eval vm_compute in (BG.kept_list 80 Pd6g10dd.regs0 Pd6g10dd.regs_out0).
Lemma KS_d6g10dd_ok : BG.kept_ok 80 Pd6g10dd.regs0 Pd6g10dd.regs_out0 KS_d6g10dd = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6g10dd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 23) = Z_to_bv 64 (V 72%nat) -> getr R (reg 24) = Z_to_bv 64 (V 71%nat) -> getr R (reg 27) = Z_to_bv 64 (V 79%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 264) (V 68%nat) ->
  0 <= (V 68%nat) <= 18446744073709551615 -> 0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = true -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 ->
  Z.testbit (V 69%nat) 0 = true -> L5.u64_at RSEGS M ((V 35%nat) + 24) (V 78%nat) -> 0 <= (V 78%nat) <= 18446744073709551615 -> 4096 <= (V 79%nat) <= 140737488355328 ->
  aligned (V 79%nat) 8 -> L5.u64_at RSEGS M (V 79%nat) (V 74%nat) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 0 <= (V 72%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x221a8 M) (st fx' R' 0x221d4 M')
        /\ (forall x, In x KS_d6g10dd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 78%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 65%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV65l HV65r] [HV68l HV68r] [HV69l HV69r] [HV71l HV71r] [HV72l HV72r] [HV74l HV74r] [HV78l HV78r] [HV79l HV79r] G2 G9 G19 G23 G24 G27 [K0l K0r] K1 K2 K3 [K4l K4r] [K5l K5r] K6 [K7l K7r] K8 K9 K10 [K11l K11r] K12 K13 [K14l K14r] [K15l K15r] K16 K17 [K18l K18r] [K19l K19r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 65%nat => (V 65%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 74%nat => (V 74%nat) | 78%nat => (V 78%nat) | 79%nat => (V 79%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E Pd6g10dd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6g10dd.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6g10dd.kn0).
  { unfold know_ok, Pd6g10dd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV68l HV68r K4l K4r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K5l K5r K6) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K5l K5r K6) | clear; lia | rewrite (L5K.land1_bit0_true (V 71%nat) ltac:(clear - HV71l HV71r K5l K5r K6; lia) K6); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk ZA ltac:(clear - HV69l HV69r K11l K11r K12) | clear - HV35l HV35r K7l K7r K9; lia | clear - HV35l HV35r K7l K7r K9; lia | byte_tac ltac:(clear - HV69l HV69r K11l K11r K12; lia) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K11l K11r K12) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K11l K11r K12) | clear; lia | rewrite (L5K.land1_bit0_true (V 69%nat) ltac:(clear - HV69l HV69r K11l K11r K12; lia) K12); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk ZA ltac:(clear - HV78l HV78r K14l K14r) | clear - HV35l HV35r K7l K7r K9; lia | clear - HV35l HV35r K7l K7r K9; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV79l HV79r K15l K15r) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV79l HV79r K15l K15r) | evalEk ZA ltac:(clear - HV74l HV74r K18l K18r) | clear - HV79l HV79r K15l K15r; lia | clear - HV79l HV79r K15l K15r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_nil. }
  destruct (Pd6g10dd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6g10dd.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd6g10dd.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6g10dd.ps0) with 0x221d4 in Hms. change (SR.ps_regs Pd6g10dd.ps0) with (map (fun i => (i, nth i Pd6g10dd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6g10dd.ps0) with Pd6g10dd.cells0 in Hcells. unfold Pd6g10dd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6g10dd.regs0 Pd6g10dd.regs_out0 80 KS_d6g10dd KS_d6g10dd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6g10dd.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd6g10dd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g10dd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6g10dd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g10dd.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd6g10dd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6g10dd.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd6g10dd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd6g10dd.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd6g10dd.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6x2 := LibSegZ_d6x2.
Definition KS_d6x2 : list nat := Eval vm_compute in (BG.kept_list 80 Pd6x2.regs0 Pd6x2.regs_out0).
Lemma KS_d6x2_ok : BG.kept_ok 80 Pd6x2.regs0 Pd6x2.regs_out0 KS_d6x2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6x2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 272) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 280) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 288) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 256) 1 -> L5.u32_at RSEGS M ((V 2%nat) - 236) (V 77%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 296) (V 64%nat) -> 1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 304)) ->
  L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 -> L5.writable RSEGS M (V 35%nat) 32 -> 0 <= (V 61%nat) <= 1 ->
  0 <= (V 62%nat) <= 2 -> 0 <= (V 64%nat) <= 1 -> 0 <= (V 77%nat) <= 63 -> 0 <= (V 36%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 35%nat) + 0) <= i < ((V 35%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22244 M) (st fx' R' 0x22790 M')
        /\ (forall x, In x KS_d6x2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139904
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 77%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 62%nat)
        /\ L5.u8_at RSEGS M' (V 35%nat) (Z.lor (Z.land (V 69%nat) 253) ((2 * (V 61%nat)) mod 2 ^ 64))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV36l HV36r] [HV61l HV61r] [HV62l HV62r] [HV64l HV64r] [HV69l HV69r] [HV77l HV77r] G2 G9 G18 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 [K9l K9r] K10 K11 K12 [K13l K13r] K14 [K15l K15r] [K16l K16r] [K17l K17r] [K18l K18r] [K19l K19r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 64%nat => (V 64%nat) | 69%nat => (V 69%nat) | 77%nat => (V 77%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 78%nat. }
  assert (HR: regs_ok E Pd6x2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6x2.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6x2.kn0).
  { unfold know_ok, Pd6x2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV62l HV62r K16l K16r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV61l HV61r K15l K15r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV77l HV77r K18l K18r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV64l HV64r K17l K17r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K9l K9r K11) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K9l K9r K11) | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K9l K9r K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K9l K9r K11) | evalEk ZA ltac:(clear - HV69l HV69r K13l K13r) | clear - HV35l HV35r K9l K9r K11; lia | clear - HV35l HV35r K9l K9r K11; lia | byte_tac ltac:(clear - HV69l HV69r K13l K13r; lia) | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K9l K9r K11) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K9l K9r K11; lia | clear - HV35l HV35r K9l K9r K11; lia | clear - HV35l HV35r K9l K9r K11; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_nil. }
  destruct (Pd6x2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6x2.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd6x2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K9l K9r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K9l K9r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6x2.ps0) with 0x22790 in Hms. change (SR.ps_regs Pd6x2.ps0) with (map (fun i => (i, nth i Pd6x2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6x2.ps0) with Pd6x2.cells0 in Hcells. unfold Pd6x2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6x2.regs0 Pd6x2.regs_out0 80 KS_d6x2 KS_d6x2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6x2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd6x2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6x2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd6x2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6x2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6x2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6x2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd6x2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6x2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd6x2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6x2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd6x2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd6x2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd6x2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K9l K9r K11) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV61l HV61r K15l K15r HV69l HV69r K13l K13r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd6x3 := LibSegZ_d6x3.
Definition KS_d6x3 : list nat := Eval vm_compute in (BG.kept_list 80 Pd6x3.regs0 Pd6x3.regs_out0).
Lemma KS_d6x3_ok : BG.kept_ok 80 Pd6x3.regs0 Pd6x3.regs_out0 KS_d6x3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d6x3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 (V 62%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (((V 2%nat) - 304) + 304 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> L5.writable RSEGS M (V 36%nat) 32 ->
  0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22280 M) (st fx' R' 0x22290 M')
        /\ (forall x, In x KS_d6x3 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (Z.land (V 71%nat) 253) (V 62%nat))
        /\ L5.u8_at RSEGS M' (V 36%nat) (Z.lor (Z.land (V 71%nat) 253) (V 62%nat))).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV62l HV62r] [HV71l HV71r] G2 G8 G19 [K0l K0r] K1 [K2l K2r] K3 K4 K5 [K6l K6r] K7 [K8l K8r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 62%nat => (V 62%nat) | 71%nat => (V 71%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 72%nat. }
  assert (HR: regs_ok E Pd6x3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd6x3.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd6x3.kn0).
  { unfold know_ok, Pd6x3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r K4) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r K4) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K2l K2r K4) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r K4) | evalEk ZA ltac:(clear - HV71l HV71r K6l K6r) | clear - HV36l HV36r K2l K2r K4; lia | clear - HV36l HV36r K2l K2r K4; lia | byte_tac ltac:(clear - HV71l HV71r K6l K6r; lia) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r K4) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K2l K2r K4; lia | clear - HV36l HV36r K2l K2r K4; lia | clear - HV36l HV36r K2l K2r K4; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  destruct (Pd6x3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd6x3.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd6x3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K2l K2r K4) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K2l K2r K4 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd6x3.ps0) with 0x22290 in Hms. change (SR.ps_regs Pd6x3.ps0) with (map (fun i => (i, nth i Pd6x3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd6x3.ps0) with Pd6x3.cells0 in Hcells. unfold Pd6x3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd6x3.regs0 Pd6x3.regs_out0 80 KS_d6x3 KS_d6x3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd6x3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd6x3.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K2l K2r K4) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV62l HV62r K8l K8r HV71l HV71r K6l K6r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End L5DIVOP.
