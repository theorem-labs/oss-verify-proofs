(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigLinkZA.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5DivO2PU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVO2PU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).

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
Module Pd7ue2 := LibSegZ_d7ue2.
Definition KS_d7ue2 : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ue2.regs0 Pd7ue2.regs_out0).
Lemma KS_d7ue2_ok : BG.kept_ok 80 Pd7ue2.regs0 Pd7ue2.regs_out0 KS_d7ue2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7ue2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 42%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false -> 2 <= (V 42%nat) <= 2 ->
  1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 33%nat) (V 38%nat) ->
  0 <= (V 38%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22548 M) (st fx' R' 0x23208 M')
        /\ (forall x, In x KS_d7ue2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 140676
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 216)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) ((V 2%nat) - 120)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV41l HV41r] [HV42l HV42r] G2 G8 G9 G18 G23 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6 [K7l K7r] [K8l K8r] K9 K10 K11 [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E Pd7ue2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7ue2.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7ue2.kn0).
  { unfold know_ok, Pd7ue2.kn0.
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
  destruct (Pd7ue2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7ue2.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd7ue2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd7ue2.ps0) with 0x23208 in Hms. change (SR.ps_regs Pd7ue2.ps0) with (map (fun i => (i, nth i Pd7ue2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd7ue2.ps0) with Pd7ue2.cells0 in Hcells. unfold Pd7ue2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ue2.regs0 Pd7ue2.regs_out0 80 KS_d7ue2 KS_d7ue2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd7ue2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd7ue2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ue2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd7ue2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd7ue2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd7ue2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pd7ue2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd7ue2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd7ue4i := LibSegZ_d7ue4i.
Definition KS_d7ue4i : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ue4i.regs0 Pd7ue4i.regs_out0).
Lemma KS_d7ue4i_ok : BG.kept_ok 80 Pd7ue4i.regs0 Pd7ue4i.regs_out0 KS_d7ue4i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7ue4i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 184) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2 -> 0 <= (V 47%nat) <= 1 -> 0 <= (V 44%nat) <= 255 ->
  Z.testbit (V 44%nat) 0 = false -> 1 <= (V 45%nat) <= 300 -> 1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 33%nat) (V 38%nat) -> 0 <= (V 38%nat) <= 255 -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 39%nat) ->
  Z.testbit (V 38%nat) 0 = false -> 1 <= (V 39%nat) <= 300 -> 1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 35%nat) 0 -> L5.u64_at RSEGS M ((V 35%nat) + 8) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> ~ (((V 2%nat) - 248) <= bv_unsigned a < ((V 2%nat) - 248) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 16) -> ~ (((V 2%nat) - 248) <= i < ((V 2%nat) - 248) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x225b8 M) (st fx' R' 0x22798 M')
        /\ (forall x, In x KS_d7ue4i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 2
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 168)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 35%nat) + 16)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV38l HV38r] [HV39l HV39r] [HV44l HV44r] [HV45l HV45r] [HV47l HV47r] G2 G9 G10 G18 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] [K7l K7r] K8 [K9l K9r] [K10l K10r] K11 K12 K13 [K14l K14r] K15 K16 [K17l K17r] [K18l K18r] K19 K20 K21 K22.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 47%nat => (V 47%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E Pd7ue4i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7ue4i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7ue4i.kn0).
  { unfold know_ok, Pd7ue4i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K20; lia | clear - HV2l HV2r K0l K0r K12 K20; lia | clear - HV2l HV2r K0l K0r K12 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K20) | evalEk ZA ltac:(clear - HV44l HV44r K7l K7r K8) | clear - HV2l HV2r K0l K0r K12 K20; lia | clear - HV2l HV2r K0l K0r K12 K20; lia | byte_tac ltac:(clear - HV44l HV44r K7l K7r K8; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K20) | evalEk ZA ltac:(clear - HV45l HV45r K9l K9r) | clear - HV2l HV2r K0l K0r K12 K20; lia | clear - HV2l HV2r K0l K0r K12 K20; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K20; lia | clear - HV2l HV2r K0l K0r K12 K20; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV44l HV44r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_false (V 44%nat) ltac:(clear - HV44l HV44r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r K16) | clear - HV33l HV33r K10l K10r K12; lia | clear - HV33l HV33r K10l K10r K12; lia | byte_tac ltac:(clear - HV38l HV38r K14l K14r K16; lia) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r K16) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12) | evalEk ZA ltac:(clear - HV39l HV39r K17l K17r) | clear - HV33l HV33r K10l K10r K12; lia | clear - HV33l HV33r K10l K10r K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r K16) | clear; lia | rewrite (L5K.land1_bit0_false (V 38%nat) ltac:(clear - HV38l HV38r K14l K14r K16; lia) K16); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K18l K18r K20) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K18l K18r K20) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K18l K18r K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K18l K18r K20) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K18l K18r K20; lia | clear - HV35l HV35r K18l K18r K20; lia | byte_tac ltac:(clear; lia) | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K18l K18r K20) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K18l K18r K20; lia | clear - HV35l HV35r K18l K18r K20; lia | exactA K22]. }
    apply Forall_nil. }
  destruct (Pd7ue4i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7ue4i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> ~ (((V 2%nat) - 248) <= bv_unsigned a < ((V 2%nat) - 248) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd7ue4i.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K12 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K20 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K12 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K20 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd7ue4i.ps0) with 0x22798 in Hms. change (SR.ps_regs Pd7ue4i.ps0) with (map (fun i => (i, nth i Pd7ue4i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd7ue4i.ps0) with Pd7ue4i.cells0 in Hcells. unfold Pd7ue4i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ue4i.regs0 Pd7ue4i.regs_out0 80 KS_d7ue4i KS_d7ue4i_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd7ue4i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ue4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue4i.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd7ue4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue4i.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd7ue4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue4i.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd7ue4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue4i.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd7ue4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue4i.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd7ue4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K12 K20) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K12 K20) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K12 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K12 K20) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K18l K18r K20) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd7ue4d := LibSegZ_d7ue4d.
Definition KS_d7ue4d : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ue4d.regs0 Pd7ue4d.regs_out0).
Lemma KS_d7ue4d_ok : BG.kept_ok 80 Pd7ue4d.regs0 Pd7ue4d.regs_out0 KS_d7ue4d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7ue4d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 184) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2 -> 0 <= (V 47%nat) <= 1 ->
  0 <= (V 44%nat) <= 255 -> Z.testbit (V 44%nat) 0 = true -> 1 <= (V 45%nat) <= 300 -> 4096 <= (V 46%nat) <= 140737488355328 ->
  1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 33%nat) (V 38%nat) ->
  0 <= (V 38%nat) <= 255 -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 39%nat) -> Z.testbit (V 38%nat) 0 = true -> 1 <= (V 39%nat) <= 300 ->
  L5.u64_at RSEGS M ((V 33%nat) + 24) (V 40%nat) -> 4096 <= (V 40%nat) <= 140737488355328 -> 1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 35%nat) 0 -> L5.u64_at RSEGS M ((V 35%nat) + 8) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> ~ (((V 2%nat) - 248) <= bv_unsigned a < ((V 2%nat) - 248) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 16) -> ~ (((V 2%nat) - 248) <= i < ((V 2%nat) - 248) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x225b8 M) (st fx' R' 0x22798 M')
        /\ (forall x, In x KS_d7ue4d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 2
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 35%nat) + 16)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] G2 G9 G10 G18 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r] [K8l K8r] K9 [K10l K10r] [K11l K11r] [K12l K12r] K13 K14 K15 [K16l K16r] K17 K18 [K19l K19r] K20 [K21l K21r] [K22l K22r] K23 K24 K25 K26.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E Pd7ue4d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7ue4d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7ue4d.kn0).
  { unfold know_ok, Pd7ue4d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K24) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K24) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K24; lia | clear - HV2l HV2r K0l K0r K14 K24; lia | clear - HV2l HV2r K0l K0r K14 K24; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K24) | evalEk ZA ltac:(clear - HV44l HV44r K8l K8r K9) | clear - HV2l HV2r K0l K0r K14 K24; lia | clear - HV2l HV2r K0l K0r K14 K24; lia | byte_tac ltac:(clear - HV44l HV44r K8l K8r K9; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K24) | evalEk ZA ltac:(clear - HV45l HV45r K10l K10r) | clear - HV2l HV2r K0l K0r K14 K24; lia | clear - HV2l HV2r K0l K0r K14 K24; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K24) | evalEk ZA ltac:(clear - HV46l HV46r K11l K11r) | clear - HV2l HV2r K0l K0r K14 K24; lia | clear - HV2l HV2r K0l K0r K14 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K24; lia | clear - HV2l HV2r K0l K0r K14 K24; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K8l K8r K9) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV44l HV44r K8l K8r K9) | clear; lia | rewrite (L5K.land1_bit0_true (V 44%nat) ltac:(clear - HV44l HV44r K8l K8r K9; lia) K9); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K18) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | byte_tac ltac:(clear - HV38l HV38r K16l K16r K18; lia) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K18) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear - HV39l HV39r K19l K19r) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K18) | clear; lia | rewrite (L5K.land1_bit0_true (V 38%nat) ltac:(clear - HV38l HV38r K16l K16r K18; lia) K18); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear - HV40l HV40r K21l K21r) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K22l K22r K24; lia | clear - HV35l HV35r K22l K22r K24; lia | byte_tac ltac:(clear; lia) | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K22l K22r K24; lia | clear - HV35l HV35r K22l K22r K24; lia | exactA K26]. }
    apply Forall_nil. }
  destruct (Pd7ue4d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7ue4d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> ~ (((V 2%nat) - 248) <= bv_unsigned a < ((V 2%nat) - 248) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd7ue4d.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K24 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K24 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd7ue4d.ps0) with 0x22798 in Hms. change (SR.ps_regs Pd7ue4d.ps0) with (map (fun i => (i, nth i Pd7ue4d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd7ue4d.ps0) with Pd7ue4d.cells0 in Hcells. unfold Pd7ue4d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ue4d.regs0 Pd7ue4d.regs_out0 80 KS_d7ue4d KS_d7ue4d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd7ue4d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ue4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue4d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd7ue4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue4d.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd7ue4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue4d.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd7ue4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue4d.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd7ue4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ue4d.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd7ue4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K24) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K24) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K21l K21r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K24) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K22l K22r K24) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd7ug4d := LibSegZ_d7ug4d.
Definition KS_d7ug4d : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ug4d.regs0 Pd7ug4d.regs_out0).
Lemma KS_d7ug4d_ok : BG.kept_ok 80 Pd7ug4d.regs0 Pd7ug4d.regs_out0 KS_d7ug4d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7ug4d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 (V 64%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 65%nat) -> 0 <= (V 41%nat) <= 255 ->
  Z.testbit (V 41%nat) 0 = true -> 2 <= (V 67%nat) <= 2 -> 2 <= (V 65%nat) <= 300 -> 0 <= (V 64%nat) <= 1 ->
  4096 <= (V 66%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 344) <= bv_unsigned a < ((V 2%nat) - 344) + 8) -> ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 344) <= i < ((V 2%nat) - 344) + 8) -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x227d0 M) (st fx' R' 0x214e4 M')
        /\ (forall x, In x KS_d7ug4d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141312
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 65%nat) - 2)
        /\ getr R' (reg 21) = Z_to_bv 64 2
        /\ getr R' (reg 22) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 66%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 344) (V 64%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV41l HV41r] [HV64l HV64r] [HV65l HV65r] [HV66l HV66r] [HV67l HV67r] G2 G9 G10 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r] K8 [K9l K9r] [K10l K10r] [K11l K11r] [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 41%nat => (V 41%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 68%nat. }
  assert (HR: regs_ok E Pd7ug4d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7ug4d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7ug4d.kn0).
  { unfold know_ok, Pd7ug4d.kn0.
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
  destruct (Pd7ug4d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7ug4d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 344) <= bv_unsigned a < ((V 2%nat) - 344) + 8) -> ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd7ug4d.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd7ug4d.ps0) with 0x214e4 in Hms. change (SR.ps_regs Pd7ug4d.ps0) with (map (fun i => (i, nth i Pd7ug4d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd7ug4d.ps0) with Pd7ug4d.cells0 in Hcells. unfold Pd7ug4d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ug4d.regs0 Pd7ug4d.regs_out0 80 KS_d7ug4d KS_d7ug4d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd7ug4d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd7ug4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug4d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ug4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug4d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd7ug4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug4d.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd7ug4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug4d.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd7ug4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug4d.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd7ug4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV66l HV66r K12l K12r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV64l HV64r K11l K11r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd7ug5i := LibSegZ_d7ug5i.
Definition KS_d7ug5i_0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ug5i.regs0 Pd7ug5i.regs_out0).
Lemma KS_d7ug5i_0_ok : BG.kept_ok 80 Pd7ug5i.regs0 Pd7ug5i.regs_out0 KS_d7ug5i_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_d7ug5i_1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ug5i.regs0 Pd7ug5i.regs_out1).
Lemma KS_d7ug5i_1_ok : BG.kept_ok 80 Pd7ug5i.regs0 Pd7ug5i.regs_out1 KS_d7ug5i_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7ug5i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 ->
  L5.u64_at RSEGS M ((V 35%nat) + 8) (V 70%nat) -> Z.testbit (V 69%nat) 0 = false -> 0 <= (V 70%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x22800 M) (st fx' R' 0x22830 M')
        /\ (forall x, In x KS_d7ug5i_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) + 16)
        /\ getr R' (reg 19) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 70%nat) - 1)
        /\ 1 <= (V 70%nat) <= 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 35%nat) + 16))
      \/ (msteps RSEGS (st fx R 0x22800 M) (st fx' R' 0x22848 M')
        /\ (forall x, In x KS_d7ug5i_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) + 16)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 70%nat)
        /\ 0 <= (V 70%nat) <= 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 35%nat) + 16))).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV69l HV69r] [HV70l HV70r] G2 G9 [K0l K0r] K1 K2 [K3l K3r] K4 K5 K6 [K7l K7r] K8 K9 [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 69%nat => (V 69%nat) | 70%nat => (V 70%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 71%nat. }
  assert (HR: regs_ok E Pd7ug5i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7ug5i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7ug5i.kn0).
  { unfold know_ok, Pd7ug5i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K9) | clear - HV35l HV35r K3l K3r K5; lia | clear - HV35l HV35r K3l K3r K5; lia | byte_tac ltac:(clear - HV69l HV69r K7l K7r K9; lia) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear - HV70l HV70r K10l K10r) | clear - HV35l HV35r K3l K3r K5; lia | clear - HV35l HV35r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K9) | clear; lia | rewrite (L5K.land1_bit0_false (V 69%nat) ltac:(clear - HV69l HV69r K7l K7r K9; lia) K9); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (Pd7ug5i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7ug5i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd7ug5i.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc Pd7ug5i.ps0) with 0x22830 in Hms. change (SR.ps_regs Pd7ug5i.ps0) with (map (fun i => (i, nth i Pd7ug5i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pd7ug5i.ps0) with Pd7ug5i.cells0 in Hcells. unfold Pd7ug5i.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ug5i.regs0 Pd7ug5i.regs_out0 80 KS_d7ug5i_0 KS_d7ug5i_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pd7ug5i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ug5i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7ug5i.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd7ug5i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7ug5i.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd7ug5i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV70l HV70r K10l K10r)]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV70l HV70r K10l K10r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K3l K3r K5) | clear; lia]. 
  - right.
    change (SR.ps_pc Pd7ug5i.ps1) with 0x22848 in Hms. change (SR.ps_regs Pd7ug5i.ps1) with (map (fun i => (i, nth i Pd7ug5i.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pd7ug5i.ps1) with Pd7ug5i.cells1 in Hcells. unfold Pd7ug5i.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ug5i.regs0 Pd7ug5i.regs_out1 80 KS_d7ug5i_1 KS_d7ug5i_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pd7ug5i.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ug5i.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7ug5i.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd7ug5i.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV70l HV70r K10l K10r)]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV70l HV70r K10l K10r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K3l K3r K5) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd7uzl := LibSegZ_d7uzl.
Definition KS_d7uzl_0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd7uzl.regs0 Pd7uzl.regs_out0).
Lemma KS_d7uzl_0_ok : BG.kept_ok 80 Pd7uzl.regs0 Pd7uzl.regs_out0 KS_d7uzl_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_d7uzl_1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd7uzl.regs0 Pd7uzl.regs_out1).
Lemma KS_d7uzl_1_ok : BG.kept_ok 80 Pd7uzl.regs0 Pd7uzl.regs_out1 KS_d7uzl_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7uzl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 19) = Z_to_bv 64 18446744073709551615 -> getr R (reg 22) = Z_to_bv 64 (V 75%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 224) (V 70%nat) -> 4096 <= (V 68%nat) <= 140737488355328 -> aligned (V 68%nat) 8 -> L5.writable RSEGS M ((V 68%nat) + (8 * (V 75%nat))) 8 ->
  (((V 2%nat) - 352) + 352 <= ((V 68%nat) + (8 * (V 75%nat))) \/ ((V 68%nat) + (8 * (V 75%nat))) + 8 <= ((V 2%nat) - 352)) -> 0 <= (V 75%nat) <= 299 -> 0 <= (V 70%nat) <= 300 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 68%nat) + (8 * (V 75%nat))) + 0) <= bv_unsigned a < (((V 68%nat) + (8 * (V 75%nat))) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 68%nat) + (8 * (V 75%nat))) + 0) <= i < (((V 68%nat) + (8 * (V 75%nat))) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x22830 M) (st fx' R' 0x22830 M')
        /\ (forall x, In x KS_d7uzl_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141372
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 68%nat) + (8 * (V 75%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 75%nat) - 1)
        /\ 1 <= (V 75%nat) <= 299
        /\ L5.u64_at RSEGS M' ((V 68%nat) + (8 * (V 75%nat))) 0)
      \/ (msteps RSEGS (st fx R 0x22830 M) (st fx' R' 0x22848 M')
        /\ (forall x, In x KS_d7uzl_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141372
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 68%nat) + (8 * (V 75%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 75%nat) - 1)
        /\ 0 <= (V 75%nat) <= 0
        /\ L5.u64_at RSEGS M' ((V 68%nat) + (8 * (V 75%nat))) 0)).
Proof.
  intros [HV2l HV2r] [HV68l HV68r] [HV70l HV70r] [HV75l HV75r] G2 G19 G22 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6 K7 K8 [K9l K9r] [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 68%nat => (V 68%nat) | 70%nat => (V 70%nat) | 75%nat => (V 75%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E Pd7uzl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7uzl.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7uzl.kn0).
  { unfold know_ok, Pd7uzl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear - HV70l HV70r K10l K10r) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8 HV75l HV75r K9l K9r) | evalEk ZA ltac:(clear) | clear - HV68l HV68r K5l K5r K8 HV75l HV75r K9l K9r; lia | clear - HV68l HV68r K5l K5r K8 HV75l HV75r K9l K9r; lia | clear - HV68l HV68r K5l K5r K8 HV75l HV75r K9l K9r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8 HV75l HV75r K9l K9r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K8 K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (Pd7uzl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7uzl.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 68%nat) + (8 * (V 75%nat))) + 0) <= bv_unsigned a < (((V 68%nat) + (8 * (V 75%nat))) + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd7uzl.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV68l HV68r K5l K5r K8 HV75l HV75r K9l K9r) | evalEk' ZA Hag ltac:(clear) | clear - HV68l HV68r K5l K5r K8 HV75l HV75r K9l K9r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc Pd7uzl.ps0) with 0x22830 in Hms. change (SR.ps_regs Pd7uzl.ps0) with (map (fun i => (i, nth i Pd7uzl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pd7uzl.ps0) with Pd7uzl.cells0 in Hcells. unfold Pd7uzl.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7uzl.regs0 Pd7uzl.regs_out0 80 KS_d7uzl_0 KS_d7uzl_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV75l HV75r K8 K9l K9r)]. }
    eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV68l HV68r K5l K5r K8 HV75l HV75r K9l K9r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  - right.
    change (SR.ps_pc Pd7uzl.ps1) with 0x22848 in Hms. change (SR.ps_regs Pd7uzl.ps1) with (map (fun i => (i, nth i Pd7uzl.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pd7uzl.ps1) with Pd7uzl.cells1 in Hcells. unfold Pd7uzl.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7uzl.regs0 Pd7uzl.regs_out1 80 KS_d7uzl_1 KS_d7uzl_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd7uzl.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd7uzl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV75l HV75r K8 K9l K9r)]. }
    eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV68l HV68r K5l K5r K8 HV75l HV75r K9l K9r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd7ug7i0 := LibSegZ_d7ug7i0.
Definition KS_d7ug7i0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ug7i0.regs0 Pd7ug7i0.regs_out0).
Lemma KS_d7ug7i0_ok : BG.kept_ok 80 Pd7ug7i0.regs0 Pd7ug7i0.regs_out0 KS_d7ug7i0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7ug7i0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) -> getr R (reg 24) = Z_to_bv 64 (V 65%nat) -> getr R (reg 25) = Z_to_bv 64 (V 62%nat) -> getr R (reg 26) = Z_to_bv 64 (V 61%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 67%nat) -> 4096 <= (V 66%nat) <= 140737488355328 -> aligned (V 66%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 66%nat) \/ (V 66%nat) + 64 <= ((V 2%nat) - 352)) ->
  L5.u64_at RSEGS M ((V 66%nat) + 8) (V 74%nat) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> L5.u64_at RSEGS M ((V 36%nat) + 8) (V 65%nat) ->
  Z.testbit (V 71%nat) 0 = false -> L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 65%nat))) + 8) (V 73%nat) -> 1 <= (V 65%nat) <= 2 -> 0 <= (V 73%nat) <= 18446744073709551615 ->
  (V 73%nat) < (V 74%nat) -> 2 <= (V 67%nat) <= 2 -> 0 <= (V 61%nat) <= 1 -> 0 <= (V 62%nat) <= 2 ->
  1 <= (V 37%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= i < ((V 2%nat) - 304) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22854 M) (st fx' R' 0x2291c M')
        /\ (forall x, In x KS_d7ug7i0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141480
        /\ getr R' (reg 10) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 1
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) ((V 36%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 336) (V 37%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV37l HV37r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV66l HV66r] [HV67l HV67r] [HV71l HV71r] [HV73l HV73r] [HV74l HV74r] G2 G8 G21 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6 K7 K8 [K9l K9r] [K10l K10r] K11 K12 K13 [K14l K14r] K15 K16 K17 [K18l K18r] [K19l K19r] K20 [K21l K21r] [K22l K22r] [K23l K23r] [K24l K24r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 71%nat => (V 71%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd7ug7i0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7ug7i0.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7ug7i0.kn0).
  { unfold know_ok, Pd7ug7i0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K12; lia | clear - HV2l HV2r K0l K0r K7 K12; lia | clear - HV2l HV2r K0l K0r K7 K12; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | clear - HV2l HV2r K0l K0r K7 K12; lia | clear - HV2l HV2r K0l K0r K7 K12; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk ZA ltac:(clear - HV67l HV67r K21l K21r) | clear - HV2l HV2r K0l K0r K7 K12; lia | clear - HV2l HV2r K0l K0r K7 K12; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K20) | clear - HV66l HV66r K5l K5r K7; lia | clear - HV66l HV66r K5l K5r K7; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K20) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K16) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | byte_tac ltac:(clear - HV71l HV71r K14l K14r K16; lia) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K16) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV65l HV65r K18l K18r) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K16) | clear; lia | rewrite (L5K.land1_bit0_false (V 71%nat) ltac:(clear - HV71l HV71r K14l K14r K16; lia) K16); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 HV65l HV65r K18l K18r) | evalEk ZA ltac:(clear - HV73l HV73r K19l K19r K20) | clear - HV36l HV36r K10l K10r K12 HV65l HV65r K18l K18r; lia | clear - HV36l HV36r K10l K10r K12 HV65l HV65r K18l K18r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K19l K19r K20) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K20; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  destruct (Pd7ug7i0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7ug7i0.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd7ug7i0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K12 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd7ug7i0.ps0) with 0x2291c in Hms. change (SR.ps_regs Pd7ug7i0.ps0) with (map (fun i => (i, nth i Pd7ug7i0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd7ug7i0.ps0) with Pd7ug7i0.cells0 in Hcells. unfold Pd7ug7i0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ug7i0.regs0 Pd7ug7i0.regs_out0 80 KS_d7ug7i0 KS_d7ug7i0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd7ug7i0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd7ug7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ug7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd7ug7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd7ug7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd7ug7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd7ug7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd7ug7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd7ug7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd7ug7i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear - HV65l HV65r K18l K18r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K10l K10r K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K23l K23r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K22l K22r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K24l K24r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd7ug7i1 := LibSegZ_d7ug7i1.
Definition KS_d7ug7i1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ug7i1.regs0 Pd7ug7i1.regs_out0).
Lemma KS_d7ug7i1_ok : BG.kept_ok 80 Pd7ug7i1.regs0 Pd7ug7i1.regs_out0 KS_d7ug7i1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7ug7i1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) -> getr R (reg 24) = Z_to_bv 64 (V 65%nat) -> getr R (reg 25) = Z_to_bv 64 (V 62%nat) -> getr R (reg 26) = Z_to_bv 64 (V 61%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 67%nat) -> 4096 <= (V 66%nat) <= 140737488355328 -> aligned (V 66%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 66%nat) \/ (V 66%nat) + 64 <= ((V 2%nat) - 352)) ->
  L5.u64_at RSEGS M ((V 66%nat) + 8) (V 74%nat) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> L5.u64_at RSEGS M ((V 36%nat) + 8) (V 65%nat) ->
  Z.testbit (V 71%nat) 0 = false -> L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 65%nat))) + 8) (V 73%nat) -> 1 <= (V 65%nat) <= 2 -> 0 <= (V 73%nat) <= 18446744073709551615 ->
  (V 74%nat) <= (V 73%nat) -> 2 <= (V 67%nat) <= 2 -> 0 <= (V 61%nat) <= 1 -> 0 <= (V 62%nat) <= 2 ->
  1 <= (V 37%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= i < ((V 2%nat) - 304) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22854 M) (st fx' R' 0x228b0 M')
        /\ (forall x, In x KS_d7ug7i1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141480
        /\ getr R' (reg 10) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 1
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) ((V 36%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 336) (V 37%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV37l HV37r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV66l HV66r] [HV67l HV67r] [HV71l HV71r] [HV73l HV73r] [HV74l HV74r] G2 G8 G21 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6 K7 K8 [K9l K9r] [K10l K10r] K11 K12 K13 [K14l K14r] K15 K16 K17 [K18l K18r] [K19l K19r] K20 [K21l K21r] [K22l K22r] [K23l K23r] [K24l K24r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 71%nat => (V 71%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd7ug7i1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7ug7i1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7ug7i1.kn0).
  { unfold know_ok, Pd7ug7i1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K12; lia | clear - HV2l HV2r K0l K0r K7 K12; lia | clear - HV2l HV2r K0l K0r K7 K12; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | clear - HV2l HV2r K0l K0r K7 K12; lia | clear - HV2l HV2r K0l K0r K7 K12; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk ZA ltac:(clear - HV67l HV67r K21l K21r) | clear - HV2l HV2r K0l K0r K7 K12; lia | clear - HV2l HV2r K0l K0r K7 K12; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K20) | clear - HV66l HV66r K5l K5r K7; lia | clear - HV66l HV66r K5l K5r K7; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K20) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K16) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | byte_tac ltac:(clear - HV71l HV71r K14l K14r K16; lia) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K16) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV65l HV65r K18l K18r) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K16) | clear; lia | rewrite (L5K.land1_bit0_false (V 71%nat) ltac:(clear - HV71l HV71r K14l K14r K16; lia) K16); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 HV65l HV65r K18l K18r) | evalEk ZA ltac:(clear - HV73l HV73r K19l K19r K20) | clear - HV36l HV36r K10l K10r K12 HV65l HV65r K18l K18r; lia | clear - HV36l HV36r K10l K10r K12 HV65l HV65r K18l K18r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K19l K19r K20) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K20; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  destruct (Pd7ug7i1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7ug7i1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd7ug7i1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K12 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd7ug7i1.ps0) with 0x228b0 in Hms. change (SR.ps_regs Pd7ug7i1.ps0) with (map (fun i => (i, nth i Pd7ug7i1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd7ug7i1.ps0) with Pd7ug7i1.cells0 in Hcells. unfold Pd7ug7i1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ug7i1.regs0 Pd7ug7i1.regs_out0 80 KS_d7ug7i1 KS_d7ug7i1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd7ug7i1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd7ug7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ug7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd7ug7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd7ug7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd7ug7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd7ug7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd7ug7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd7ug7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7i1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd7ug7i1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear - HV65l HV65r K18l K18r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K10l K10r K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K23l K23r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K22l K22r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K24l K24r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd7ug7d0 := LibSegZ_d7ug7d0.
Definition KS_d7ug7d0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ug7d0.regs0 Pd7ug7d0.regs_out0).
Lemma KS_d7ug7d0_ok : BG.kept_ok 80 Pd7ug7d0.regs0 Pd7ug7d0.regs_out0 KS_d7ug7d0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7ug7d0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) -> getr R (reg 24) = Z_to_bv 64 (V 65%nat) -> getr R (reg 25) = Z_to_bv 64 (V 62%nat) -> getr R (reg 26) = Z_to_bv 64 (V 61%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 67%nat) -> 4096 <= (V 66%nat) <= 140737488355328 -> aligned (V 66%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 66%nat) \/ (V 66%nat) + 64 <= ((V 2%nat) - 352)) ->
  L5.u64_at RSEGS M ((V 66%nat) + 8) (V 74%nat) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> L5.u64_at RSEGS M ((V 36%nat) + 8) (V 65%nat) ->
  Z.testbit (V 71%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 24) (V 72%nat) -> 4096 <= (V 72%nat) <= 140737488355328 -> aligned (V 72%nat) 8 ->
  (((V 2%nat) - 352) + 352 <= (V 72%nat) \/ (V 72%nat) + (8 * (V 65%nat)) <= ((V 2%nat) - 352)) -> L5.u64_at RSEGS M (((8 * (V 65%nat)) + (V 72%nat)) - 8) (V 73%nat) -> 2 <= (V 65%nat) <= 300 -> 0 <= (V 73%nat) <= 18446744073709551615 ->
  (V 73%nat) < (V 74%nat) -> 2 <= (V 67%nat) <= 2 -> 0 <= (V 61%nat) <= 1 -> 0 <= (V 62%nat) <= 2 ->
  1 <= (V 37%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= i < ((V 2%nat) - 304) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22854 M) (st fx' R' 0x2291c M')
        /\ (forall x, In x KS_d7ug7d0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141480
        /\ getr R' (reg 10) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 1
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 336) (V 37%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV37l HV37r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV66l HV66r] [HV67l HV67r] [HV71l HV71r] [HV72l HV72r] [HV73l HV73r] [HV74l HV74r] G2 G8 G21 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6 K7 K8 [K9l K9r] [K10l K10r] K11 K12 K13 [K14l K14r] K15 K16 K17 [K18l K18r] K19 K20 K21 [K22l K22r] [K23l K23r] K24 [K25l K25r] [K26l K26r] [K27l K27r] [K28l K28r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd7ug7d0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7ug7d0.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7ug7d0.kn0).
  { unfold know_ok, Pd7ug7d0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk ZA ltac:(clear - HV67l HV67r K25l K25r) | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K24) | clear - HV66l HV66r K5l K5r K7; lia | clear - HV66l HV66r K5l K5r K7; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K24) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K16) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | byte_tac ltac:(clear - HV71l HV71r K14l K14r K16; lia) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K16) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV65l HV65r K20 K22l K22r) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K16) | clear; lia | rewrite (L5K.land1_bit0_true (V 71%nat) ltac:(clear - HV71l HV71r K14l K14r K16; lia) K16); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV72l HV72r K18l K18r K20) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K18l K18r K20) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV72l HV72r K18l K18r K20) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV72l HV72r K18l K18r K20) | evalEk ZA ltac:(clear - HV65l HV65r K20 K22l K22r) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV65l HV65r K20 K22l K22r HV72l HV72r K18l K18r) | evalEk ZA ltac:(clear - HV73l HV73r K23l K23r K24) | clear - HV65l HV65r K20 K22l K22r HV72l HV72r K18l K18r; lia | clear - HV65l HV65r K20 K22l K22r HV72l HV72r K18l K18r; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K20 K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K23l K23r K24) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K24; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K27l K27r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_nil. }
  destruct (Pd7ug7d0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7ug7d0.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd7ug7d0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K12 K20 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K12 K20 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd7ug7d0.ps0) with 0x2291c in Hms. change (SR.ps_regs Pd7ug7d0.ps0) with (map (fun i => (i, nth i Pd7ug7d0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd7ug7d0.ps0) with Pd7ug7d0.cells0 in Hcells. unfold Pd7ug7d0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ug7d0.regs0 Pd7ug7d0.regs_out0 80 KS_d7ug7d0 KS_d7ug7d0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd7ug7d0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd7ug7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ug7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd7ug7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd7ug7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd7ug7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd7ug7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd7ug7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd7ug7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd7ug7d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear - HV65l HV65r K20 K22l K22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear - HV72l HV72r K18l K18r K20) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K27l K27r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K26l K26r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K28l K28r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd7ug7d1 := LibSegZ_d7ug7d1.
Definition KS_d7ug7d1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ug7d1.regs0 Pd7ug7d1.regs_out0).
Lemma KS_d7ug7d1_ok : BG.kept_ok 80 Pd7ug7d1.regs0 Pd7ug7d1.regs_out0 KS_d7ug7d1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7ug7d1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) -> getr R (reg 24) = Z_to_bv 64 (V 65%nat) -> getr R (reg 25) = Z_to_bv 64 (V 62%nat) -> getr R (reg 26) = Z_to_bv 64 (V 61%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 67%nat) -> 4096 <= (V 66%nat) <= 140737488355328 -> aligned (V 66%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 66%nat) \/ (V 66%nat) + 64 <= ((V 2%nat) - 352)) ->
  L5.u64_at RSEGS M ((V 66%nat) + 8) (V 74%nat) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> L5.u64_at RSEGS M ((V 36%nat) + 8) (V 65%nat) ->
  Z.testbit (V 71%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 24) (V 72%nat) -> 4096 <= (V 72%nat) <= 140737488355328 -> aligned (V 72%nat) 8 ->
  (((V 2%nat) - 352) + 352 <= (V 72%nat) \/ (V 72%nat) + (8 * (V 65%nat)) <= ((V 2%nat) - 352)) -> L5.u64_at RSEGS M (((8 * (V 65%nat)) + (V 72%nat)) - 8) (V 73%nat) -> 2 <= (V 65%nat) <= 300 -> 0 <= (V 73%nat) <= 18446744073709551615 ->
  (V 74%nat) <= (V 73%nat) -> 2 <= (V 67%nat) <= 2 -> 0 <= (V 61%nat) <= 1 -> 0 <= (V 62%nat) <= 2 ->
  1 <= (V 37%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= i < ((V 2%nat) - 304) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22854 M) (st fx' R' 0x228b0 M')
        /\ (forall x, In x KS_d7ug7d1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141480
        /\ getr R' (reg 10) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 1
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 336) (V 37%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV37l HV37r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV66l HV66r] [HV67l HV67r] [HV71l HV71r] [HV72l HV72r] [HV73l HV73r] [HV74l HV74r] G2 G8 G21 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6 K7 K8 [K9l K9r] [K10l K10r] K11 K12 K13 [K14l K14r] K15 K16 K17 [K18l K18r] K19 K20 K21 [K22l K22r] [K23l K23r] K24 [K25l K25r] [K26l K26r] [K27l K27r] [K28l K28r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd7ug7d1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7ug7d1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7ug7d1.kn0).
  { unfold know_ok, Pd7ug7d1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk ZA ltac:(clear - HV67l HV67r K25l K25r) | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | clear - HV2l HV2r K0l K0r K7 K12 K20; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r K7) | evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K24) | clear - HV66l HV66r K5l K5r K7; lia | clear - HV66l HV66r K5l K5r K7; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K9l K9r K24) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K16) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | byte_tac ltac:(clear - HV71l HV71r K14l K14r K16; lia) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K16) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV65l HV65r K20 K22l K22r) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K14l K14r K16) | clear; lia | rewrite (L5K.land1_bit0_true (V 71%nat) ltac:(clear - HV71l HV71r K14l K14r K16; lia) K16); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12) | evalEk ZA ltac:(clear - HV72l HV72r K18l K18r K20) | clear - HV36l HV36r K10l K10r K12; lia | clear - HV36l HV36r K10l K10r K12; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K18l K18r K20) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV72l HV72r K18l K18r K20) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV72l HV72r K18l K18r K20) | evalEk ZA ltac:(clear - HV65l HV65r K20 K22l K22r) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV65l HV65r K20 K22l K22r HV72l HV72r K18l K18r) | evalEk ZA ltac:(clear - HV73l HV73r K23l K23r K24) | clear - HV65l HV65r K20 K22l K22r HV72l HV72r K18l K18r; lia | clear - HV65l HV65r K20 K22l K22r HV72l HV72r K18l K18r; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K20 K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K23l K23r K24) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K24; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K27l K27r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_nil. }
  destruct (Pd7ug7d1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7ug7d1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd7ug7d1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K12 K20 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K12 K20 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd7ug7d1.ps0) with 0x228b0 in Hms. change (SR.ps_regs Pd7ug7d1.ps0) with (map (fun i => (i, nth i Pd7ug7d1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd7ug7d1.ps0) with Pd7ug7d1.cells0 in Hcells. unfold Pd7ug7d1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ug7d1.regs0 Pd7ug7d1.regs_out0 80 KS_d7ug7d1 KS_d7ug7d1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd7ug7d1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd7ug7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ug7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd7ug7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd7ug7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd7ug7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd7ug7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd7ug7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd7ug7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug7d1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd7ug7d1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear - HV65l HV65r K20 K22l K22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear - HV72l HV72r K18l K18r K20) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K27l K27r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K26l K26r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K12 K20) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K28l K28r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd7ug10i := LibSegZ_d7ug10i.
Definition KS_d7ug10i : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ug10i.regs0 Pd7ug10i.regs_out0).
Lemma KS_d7ug10i_ok : BG.kept_ok 80 Pd7ug10i.regs0 Pd7ug10i.regs_out0 KS_d7ug10i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7ug10i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 (V 65%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 ->
  Z.testbit (V 69%nat) 0 = false -> L5.u64_at RSEGS M ((V 35%nat) + 8) ((V 70%nat) + 1) -> 0 <= (V 70%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x228f4 M) (st fx' R' 0x2291c M')
        /\ (forall x, In x KS_d7ug10i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 70%nat) + 1)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 70%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 35%nat) + 16)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV65l HV65r] [HV69l HV69r] [HV70l HV70r] G2 G9 G24 [K0l K0r] K1 K2 [K3l K3r] K4 K5 K6 [K7l K7r] K8 K9 [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 65%nat => (V 65%nat) | 69%nat => (V 69%nat) | 70%nat => (V 70%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 71%nat. }
  assert (HR: regs_ok E Pd7ug10i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7ug10i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7ug10i.kn0).
  { unfold know_ok, Pd7ug10i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K8) | clear - HV35l HV35r K3l K3r K5; lia | clear - HV35l HV35r K3l K3r K5; lia | byte_tac ltac:(clear - HV69l HV69r K7l K7r K8; lia) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_false (V 69%nat) ltac:(clear - HV69l HV69r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear - HV70l HV70r K10l K10r) | clear - HV35l HV35r K3l K3r K5; lia | clear - HV35l HV35r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (Pd7ug10i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7ug10i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd7ug10i.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd7ug10i.ps0) with 0x2291c in Hms. change (SR.ps_regs Pd7ug10i.ps0) with (map (fun i => (i, nth i Pd7ug10i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd7ug10i.ps0) with Pd7ug10i.cells0 in Hcells. unfold Pd7ug10i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ug10i.regs0 Pd7ug10i.regs_out0 80 KS_d7ug10i KS_d7ug10i_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd7ug10i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ug10i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug10i.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd7ug10i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug10i.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd7ug10i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV70l HV70r K10l K10r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K3l K3r K5) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd7ug10d := LibSegZ_d7ug10d.
Definition KS_d7ug10d : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ug10d.regs0 Pd7ug10d.regs_out0).
Lemma KS_d7ug10d_ok : BG.kept_ok 80 Pd7ug10d.regs0 Pd7ug10d.regs_out0 KS_d7ug10d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7ug10d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 (V 65%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 ->
  Z.testbit (V 69%nat) 0 = true -> L5.u64_at RSEGS M ((V 35%nat) + 24) (V 68%nat) -> L5.u64_at RSEGS M ((V 35%nat) + 8) ((V 70%nat) + 1) -> 0 <= (V 70%nat) <= 300 ->
  4096 <= (V 68%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x228f4 M) (st fx' R' 0x2291c M')
        /\ (forall x, In x KS_d7ug10d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 70%nat) + 1)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 70%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 68%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV65l HV65r] [HV68l HV68r] [HV69l HV69r] [HV70l HV70r] G2 G9 G24 [K0l K0r] K1 K2 [K3l K3r] K4 K5 K6 [K7l K7r] K8 K9 K10 [K11l K11r] [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 65%nat => (V 65%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | 70%nat => (V 70%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 71%nat. }
  assert (HR: regs_ok E Pd7ug10d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7ug10d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7ug10d.kn0).
  { unfold know_ok, Pd7ug10d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K8) | clear - HV35l HV35r K3l K3r K5; lia | clear - HV35l HV35r K3l K3r K5; lia | byte_tac ltac:(clear - HV69l HV69r K7l K7r K8; lia) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_true (V 69%nat) ltac:(clear - HV69l HV69r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear - HV68l HV68r K12l K12r) | clear - HV35l HV35r K3l K3r K5; lia | clear - HV35l HV35r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear - HV70l HV70r K11l K11r) | clear - HV35l HV35r K3l K3r K5; lia | clear - HV35l HV35r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  destruct (Pd7ug10d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7ug10d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd7ug10d.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd7ug10d.ps0) with 0x2291c in Hms. change (SR.ps_regs Pd7ug10d.ps0) with (map (fun i => (i, nth i Pd7ug10d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd7ug10d.ps0) with Pd7ug10d.cells0 in Hcells. unfold Pd7ug10d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ug10d.regs0 Pd7ug10d.regs_out0 80 KS_d7ug10d KS_d7ug10d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd7ug10d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ug10d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug10d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd7ug10d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ug10d.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd7ug10d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV70l HV70r K11l K11r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV68l HV68r K12l K12r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd7ux2 := LibSegZ_d7ux2.
Definition KS_d7ux2 : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ux2.regs0 Pd7ux2.regs_out0).
Lemma KS_d7ux2_ok : BG.kept_ok 80 Pd7ux2.regs0 Pd7ux2.regs_out0 KS_d7ux2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7ux2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 320) (V 62%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 328) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 336) 1 -> L5.u32_at RSEGS M ((V 2%nat) - 284) (V 77%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 344) (V 64%nat) ->
  1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) ->
  0 <= (V 69%nat) <= 255 -> L5.writable RSEGS M (V 35%nat) 32 -> 0 <= (V 61%nat) <= 1 -> 0 <= (V 62%nat) <= 2 ->
  0 <= (V 77%nat) <= 63 -> 0 <= (V 64%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 35%nat) + 0) <= i < ((V 35%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x229e8 M) (st fx' R' 0x23140 M')
        /\ (forall x, In x KS_d7ux2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141856
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 77%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 62%nat)
        /\ L5.u8_at RSEGS M' (V 35%nat) (Z.lor (Z.land (V 69%nat) 253) ((2 * (V 61%nat)) mod 2 ^ 64))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV36l HV36r] [HV61l HV61r] [HV62l HV62r] [HV64l HV64r] [HV69l HV69r] [HV77l HV77r] G2 G8 G9 G18 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 [K8l K8r] K9 K10 K11 [K12l K12r] K13 [K14l K14r] [K15l K15r] [K16l K16r] [K17l K17r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 64%nat => (V 64%nat) | 69%nat => (V 69%nat) | 77%nat => (V 77%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 78%nat. }
  assert (HR: regs_ok E Pd7ux2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7ux2.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7ux2.kn0).
  { unfold know_ok, Pd7ux2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV62l HV62r K15l K15r) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV61l HV61r K14l K14r) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV77l HV77r K16l K16r) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV64l HV64r K17l K17r) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8l K8r K10) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K8l K8r K10) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K8l K8r K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K8l K8r K10) | evalEk ZA ltac:(clear - HV69l HV69r K12l K12r) | clear - HV35l HV35r K8l K8r K10; lia | clear - HV35l HV35r K8l K8r K10; lia | byte_tac ltac:(clear - HV69l HV69r K12l K12r; lia) | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K8l K8r K10) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K8l K8r K10; lia | clear - HV35l HV35r K8l K8r K10; lia | clear - HV35l HV35r K8l K8r K10; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  destruct (Pd7ux2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7ux2.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd7ux2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K8l K8r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K8l K8r K10 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd7ux2.ps0) with 0x23140 in Hms. change (SR.ps_regs Pd7ux2.ps0) with (map (fun i => (i, nth i Pd7ux2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd7ux2.ps0) with Pd7ux2.cells0 in Hcells. unfold Pd7ux2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ux2.regs0 Pd7ux2.regs_out0 80 KS_d7ux2 KS_d7ux2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd7ux2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd7ux2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ux2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ux2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ux2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd7ux2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ux2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd7ux2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ux2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd7ux2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd7ux2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd7ux2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K8l K8r K10) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV61l HV61r K14l K14r HV69l HV69r K12l K12r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd7ux3 := LibSegZ_d7ux3.
Definition KS_d7ux3 : list nat := Eval vm_compute in (BG.kept_list 80 Pd7ux3.regs0 Pd7ux3.regs_out0).
Lemma KS_d7ux3_ok : BG.kept_ok 80 Pd7ux3.regs0 Pd7ux3.regs_out0 KS_d7ux3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d7ux3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 (V 62%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> L5.writable RSEGS M (V 36%nat) 32 ->
  0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22a20 M) (st fx' R' 0x22a30 M')
        /\ (forall x, In x KS_d7ux3 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (Z.land (V 71%nat) 253) (V 62%nat))
        /\ L5.u8_at RSEGS M' (V 36%nat) (Z.lor (Z.land (V 71%nat) 253) (V 62%nat))).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV62l HV62r] [HV71l HV71r] G2 G8 G19 [K0l K0r] K1 [K2l K2r] K3 K4 K5 [K6l K6r] K7 [K8l K8r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 62%nat => (V 62%nat) | 71%nat => (V 71%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 72%nat. }
  assert (HR: regs_ok E Pd7ux3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd7ux3.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd7ux3.kn0).
  { unfold know_ok, Pd7ux3.kn0.
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
  destruct (Pd7ux3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd7ux3.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd7ux3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K2l K2r K4) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K2l K2r K4 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd7ux3.ps0) with 0x22a30 in Hms. change (SR.ps_regs Pd7ux3.ps0) with (map (fun i => (i, nth i Pd7ux3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd7ux3.ps0) with Pd7ux3.cells0 in Hcells. unfold Pd7ux3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd7ux3.regs0 Pd7ux3.regs_out0 80 KS_d7ux3 KS_d7ux3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd7ux3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd7ux3.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K2l K2r K4) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV62l HV62r K8l K8r HV71l HV71r K6l K6r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End L5DIVO2PU.
