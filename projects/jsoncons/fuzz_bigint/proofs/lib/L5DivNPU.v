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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5DivNPU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVNPU.
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
Module Pd5ue1 := LibSegZ_d5ue1.
Definition KS_d5ue1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ue1.regs0 Pd5ue1.regs_out0).
Lemma KS_d5ue1_ok : BG.kept_ok 80 Pd5ue1.regs0 Pd5ue1.regs_out0 KS_d5ue1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ue1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 36%nat) -> getr R (reg 14) = Z_to_bv 64 (V 37%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 352) <= bv_unsigned a < ((V 2%nat) - 352) + 352) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 352) <= i < ((V 2%nat) - 352) + 352) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x224f4 M) (st fx' R' 0x23208 M')
        /\ (forall x, In x KS_d5ue1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 140616
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 352)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] G2 G10 G11 G12 G13 G14 [K0l K0r] K1 K2.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E Pd5ue1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ue1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ue1.kn0).
  { unfold know_ok, Pd5ue1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  destruct (Pd5ue1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ue1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 352) <= bv_unsigned a < ((V 2%nat) - 352) + 352) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5ue1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ue1.ps0) with 0x23208 in Hms. change (SR.ps_regs Pd5ue1.ps0) with (map (fun i => (i, nth i Pd5ue1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ue1.ps0) with Pd5ue1.cells0 in Hcells. unfold Pd5ue1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ue1.regs0 Pd5ue1.regs_out0 80 KS_d5ue1 KS_d5ue1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ue1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ue1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pd5ue1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5ue1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pd5ue1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ue1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ue1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pd5ue1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5ue1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ue2n := LibSegZ_d5ue2n.
Definition KS_d5ue2n : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ue2n.regs0 Pd5ue2n.regs_out0).
Lemma KS_d5ue2n_ok : BG.kept_ok 80 Pd5ue2n.regs0 Pd5ue2n.regs_out0 KS_d5ue2n = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ue2n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 42%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false -> 1 <= (V 42%nat) <= 1 ->
  1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 33%nat) (V 38%nat) ->
  0 <= (V 38%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22548 M) (st fx' R' 0x23208 M')
        /\ (forall x, In x KS_d5ue2n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 140676
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 216)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) ((V 2%nat) - 120)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV41l HV41r] [HV42l HV42r] G2 G8 G9 G18 G23 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6 [K7l K7r] [K8l K8r] K9 K10 K11 [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E Pd5ue2n.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ue2n.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ue2n.kn0).
  { unfold know_ok, Pd5ue2n.kn0.
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
  destruct (Pd5ue2n.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ue2n.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5ue2n.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ue2n.ps0) with 0x23208 in Hms. change (SR.ps_regs Pd5ue2n.ps0) with (map (fun i => (i, nth i Pd5ue2n.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ue2n.ps0) with Pd5ue2n.cells0 in Hcells. unfold Pd5ue2n.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ue2n.regs0 Pd5ue2n.regs_out0 80 KS_d5ue2n KS_d5ue2n_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ue2n.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ue2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue2n.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ue2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue2n.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ue2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue2n.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ue2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue2n.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5ue2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue2n.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pd5ue2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue2n.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5ue2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ue3 := LibSegZ_d5ue3.
Definition KS_d5ue3 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ue3.regs0 Pd5ue3.regs_out0).
Lemma KS_d5ue3_ok : BG.kept_ok 80 Pd5ue3.regs0 Pd5ue3.regs_out0 KS_d5ue3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ue3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 19) = Z_to_bv 64 (V 41%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 184) (V 44%nat) ->
  L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) -> 0 <= (V 44%nat) <= 255 -> 0 <= (V 41%nat) <= 255 -> 0 <= (V 38%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 184) <= bv_unsigned a < ((V 2%nat) - 184) + 1) -> ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 184) <= i < ((V 2%nat) - 184) + 1) -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22584 M) (st fx' R' 0x2211c M')
        /\ (forall x, In x KS_d5ue3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 140728
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (V 38%nat) 2)
        /\ bv_unsigned (getr R' (reg 26)) = ((Z.lxor (Z.land (V 41%nat) 2) (Z.land (V 38%nat) 2)) / 2)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 136) (Z.land (V 41%nat) 253)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 184) (Z.land (V 44%nat) 253)).
Proof.
  intros [HV2l HV2r] [HV38l HV38r] [HV41l HV41r] [HV44l HV44r] G2 G19 G20 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] [K7l K7r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 38%nat => (V 38%nat) | 41%nat => (V 41%nat) | 44%nat => (V 44%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E Pd5ue3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ue3.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ue3.kn0).
  { unfold know_ok, Pd5ue3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV44l HV44r K5l K5r; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K6l K6r; lia) | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  destruct (Pd5ue3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ue3.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 184) <= bv_unsigned a < ((V 2%nat) - 184) + 1) -> ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd5ue3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ue3.ps0) with 0x2211c in Hms. change (SR.ps_regs Pd5ue3.ps0) with (map (fun i => (i, nth i Pd5ue3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ue3.ps0) with Pd5ue3.cells0 in Hcells. unfold Pd5ue3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ue3.regs0 Pd5ue3.regs_out0 80 KS_d5ue3 KS_d5ue3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ue3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ue3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ue3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ue3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue3.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pd5ue3.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg Pd5ue3.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5ue3.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV41l HV41r K6l K6r; lia) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV44l HV44r K5l K5r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ue4n := LibSegZ_d5ue4n.
Definition KS_d5ue4n : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ue4n.regs0 Pd5ue4n.regs_out0).
Lemma KS_d5ue4n_ok : BG.kept_ok 80 Pd5ue4n.regs0 Pd5ue4n.regs_out0 KS_d5ue4n = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ue4n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 184) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 2%nat) - 120) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) 1 -> 0 <= (V 47%nat) <= 1 -> 0 <= (V 44%nat) <= 255 -> Z.testbit (V 44%nat) 0 = true ->
  2 <= (V 45%nat) <= 300 -> 4096 <= (V 46%nat) <= 140737488355328 -> 4294967296 <= (V 63%nat) <= 18446744073709551615 -> srl_range (V 63%nat) 4294967296 1 4294967295 ->
  1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 33%nat) (V 38%nat) ->
  0 <= (V 38%nat) <= 255 -> Z.testbit (V 38%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 39%nat) -> 0 <= (V 39%nat) <= 300 ->
  L5.u64_at RSEGS M ((V 33%nat) + 24) (V 40%nat) -> 4096 <= (V 40%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> ~ (((V 2%nat) - 248) <= bv_unsigned a < ((V 2%nat) - 248) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 16) -> ~ (((V 2%nat) - 248) <= i < ((V 2%nat) - 248) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x225b8 M) (st fx' R' 0x22798 M')
        /\ (forall x, In x KS_d5ue4n -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = ((V 63%nat) / 4294967296)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 21) = Z_to_bv 64 (V 63%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 40%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV63l HV63r] G2 G9 G10 G18 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 [K9l K9r] [K10l K10r] K11 [K12l K12r] [K13l K13r] [K14l K14r] K15 [K16l K16r] K17 K18 K19 [K20l K20r] K21 K22 [K23l K23r] K24 [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 63%nat => (V 63%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 64%nat. }
  assert (HR: regs_ok E Pd5ue4n.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ue4n.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ue4n.kn0).
  { unfold know_ok, Pd5ue4n.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K18; lia | clear - HV2l HV2r K0l K0r K18; lia | clear - HV2l HV2r K0l K0r K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk ZA ltac:(clear - HV44l HV44r K10l K10r K11) | clear - HV2l HV2r K0l K0r K18; lia | clear - HV2l HV2r K0l K0r K18; lia | byte_tac ltac:(clear - HV44l HV44r K10l K10r K11; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r) | clear - HV2l HV2r K0l K0r K18; lia | clear - HV2l HV2r K0l K0r K18; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk ZA ltac:(clear - HV46l HV46r K13l K13r) | clear - HV2l HV2r K0l K0r K18; lia | clear - HV2l HV2r K0l K0r K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk ZA ltac:(clear - HV63l HV63r K14l K14r K15) | clear - HV2l HV2r K0l K0r K18; lia | clear - HV2l HV2r K0l K0r K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18) | clear - HV2l HV2r K0l K0r K18; lia | clear - HV2l HV2r K0l K0r K18; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K18; lia | clear - HV2l HV2r K0l K0r K18; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K10l K10r K11) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV44l HV44r K10l K10r K11) | clear; lia | rewrite (L5K.land1_bit0_true (V 44%nat) ltac:(clear - HV44l HV44r K10l K10r K11; lia) K11); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K14l K14r K15) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K18) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K18) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K18) | evalEk ZA ltac:(clear - HV38l HV38r K20l K20r K21) | clear - HV33l HV33r K16l K16r K18; lia | clear - HV33l HV33r K16l K16r K18; lia | byte_tac ltac:(clear - HV38l HV38r K20l K20r K21; lia) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_true (V 38%nat) ltac:(clear - HV38l HV38r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K18) | evalEk ZA ltac:(clear - HV39l HV39r K23l K23r) | clear - HV33l HV33r K16l K16r K18; lia | clear - HV33l HV33r K16l K16r K18; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K18) | evalEk ZA ltac:(clear - HV40l HV40r K25l K25r) | clear - HV33l HV33r K16l K16r K18; lia | clear - HV33l HV33r K16l K16r K18; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (Pd5ue4n.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ue4n.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> ~ (((V 2%nat) - 248) <= bv_unsigned a < ((V 2%nat) - 248) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd5ue4n.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K18 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K18 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ue4n.ps0) with 0x22798 in Hms. change (SR.ps_regs Pd5ue4n.ps0) with (map (fun i => (i, nth i Pd5ue4n.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ue4n.ps0) with Pd5ue4n.cells0 in Hcells. unfold Pd5ue4n.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ue4n.regs0 Pd5ue4n.regs_out0 80 KS_d5ue4n KS_d5ue4n_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ue4n.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ue4n.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg Pd5ue4n.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ue4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue4n.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ue4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue4n.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5ue4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue4n.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5ue4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ue4n.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd5ue4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K23l K23r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K25l K25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K23l K23r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K25l K25r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug1 := LibSegZ_d5ug1.
Definition KS_d5ug1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug1.regs0 Pd5ug1.regs_out0).
Lemma KS_d5ug1_ok : BG.kept_ok 80 Pd5ug1.regs0 Pd5ug1.regs_out0 KS_d5ug1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22798 M) (st fx' R' 0x23208 M')
        /\ (forall x, In x KS_d5ug1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141224
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 216)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 280)).
Proof.
  intros [HV2l HV2r] G2 [K0l K0r] K1.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pd5ug1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug1.kn0).
  { unfold know_ok, Pd5ug1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_nil. }
  destruct (Pd5ug1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ug1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ug1.ps0) with 0x23208 in Hms. change (SR.ps_regs Pd5ug1.ps0) with (map (fun i => (i, nth i Pd5ug1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ug1.ps0) with Pd5ug1.cells0 in Hcells. unfold Pd5ug1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug1.regs0 Pd5ug1.regs_out0 80 KS_d5ug1 KS_d5ug1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ug1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ug1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ug1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5ug1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ug1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug2 := LibSegZ_d5ug2.
Definition KS_d5ug2 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug2.regs0 Pd5ug2.regs_out0).
Lemma KS_d5ug2_ok : BG.kept_ok 80 Pd5ug2.regs0 Pd5ug2.regs_out0 KS_d5ug2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x227a8 M) (st fx' R' 0x23208 M')
        /\ (forall x, In x KS_d5ug2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141240
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 280)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 304)).
Proof.
  intros [HV2l HV2r] G2 [K0l K0r] K1.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pd5ug2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug2.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug2.kn0).
  { unfold know_ok, Pd5ug2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_nil. }
  destruct (Pd5ug2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug2.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ug2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ug2.ps0) with 0x23208 in Hms. change (SR.ps_regs Pd5ug2.ps0) with (map (fun i => (i, nth i Pd5ug2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ug2.ps0) with Pd5ug2.cells0 in Hcells. unfold Pd5ug2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug2.regs0 Pd5ug2.regs_out0 80 KS_d5ug2 KS_d5ug2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ug2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ug2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ug2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5ug2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ug2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug3 := LibSegZ_d5ug3.
Definition KS_d5ug3 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug3.regs0 Pd5ug3.regs_out0).
Lemma KS_d5ug3_ok : BG.kept_ok 80 Pd5ug3.regs0 Pd5ug3.regs_out0 KS_d5ug3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 284) <= bv_unsigned a < ((V 2%nat) - 284) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 284) <= i < ((V 2%nat) - 284) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x227b8 M) (st fx' R' 0x22d2c M')
        /\ (forall x, In x KS_d5ug3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141264
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 284)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 284) 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] G2 G18 [K0l K0r] K1 K2.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 34%nat. }
  assert (HR: regs_ok E Pd5ug3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug3.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug3.kn0).
  { unfold know_ok, Pd5ug3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  destruct (Pd5ug3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug3.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 284) <= bv_unsigned a < ((V 2%nat) - 284) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5ug3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ug3.ps0) with 0x22d2c in Hms. change (SR.ps_regs Pd5ug3.ps0) with (map (fun i => (i, nth i Pd5ug3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ug3.ps0) with Pd5ug3.cells0 in Hcells. unfold Pd5ug3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug3.regs0 Pd5ug3.regs_out0 80 KS_d5ug3 KS_d5ug3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ug3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ug3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ug3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ug3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5ug3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u32_of_KWord4a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug4i := LibSegZ_d5ug4i.
Definition KS_d5ug4i : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug4i.regs0 Pd5ug4i.regs_out0).
Lemma KS_d5ug4i_ok : BG.kept_ok 80 Pd5ug4i.regs0 Pd5ug4i.regs_out0 KS_d5ug4i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug4i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 (V 64%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 120) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 65%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  0 <= (V 67%nat) <= 300 -> 0 <= (V 65%nat) <= 300 -> 0 <= (V 64%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 344) <= bv_unsigned a < ((V 2%nat) - 344) + 8) -> ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 344) <= i < ((V 2%nat) - 344) + 8) -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x227d0 M) (st fx' R' 0x214e4 M')
        /\ (forall x, In x KS_d5ug4i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141312
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 65%nat) - (V 67%nat))
        /\ getr R' (reg 21) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 344) (V 64%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV41l HV41r] [HV64l HV64r] [HV65l HV65r] [HV67l HV67r] G2 G9 G10 G22 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] [K9l K9r] [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 41%nat => (V 41%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | 67%nat => (V 67%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 68%nat. }
  assert (HR: regs_ok E Pd5ug4i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug4i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug4i.kn0).
  { unfold know_ok, Pd5ug4i.kn0.
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
  destruct (Pd5ug4i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug4i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 344) <= bv_unsigned a < ((V 2%nat) - 344) + 8) -> ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd5ug4i.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ug4i.ps0) with 0x214e4 in Hms. change (SR.ps_regs Pd5ug4i.ps0) with (map (fun i => (i, nth i Pd5ug4i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ug4i.ps0) with Pd5ug4i.cells0 in Hcells. unfold Pd5ug4i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug4i.regs0 Pd5ug4i.regs_out0 80 KS_d5ug4i KS_d5ug4i_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ug4i.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ug4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug4i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug4i.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ug4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug4i.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd5ug4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug4i.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd5ug4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV67l HV67r K8l K8r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV64l HV64r K10l K10r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug5d := LibSegZ_d5ug5d.
Definition KS_d5ug5d_0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug5d.regs0 Pd5ug5d.regs_out0).
Lemma KS_d5ug5d_0_ok : BG.kept_ok 80 Pd5ug5d.regs0 Pd5ug5d.regs_out0 KS_d5ug5d_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_d5ug5d_1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug5d.regs0 Pd5ug5d.regs_out1).
Lemma KS_d5ug5d_1_ok : BG.kept_ok 80 Pd5ug5d.regs0 Pd5ug5d.regs_out1 KS_d5ug5d_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug5d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 ->
  L5.u64_at RSEGS M ((V 35%nat) + 8) (V 70%nat) -> Z.testbit (V 69%nat) 0 = true -> 0 <= (V 70%nat) <= 300 -> L5.u64_at RSEGS M ((V 35%nat) + 24) (V 40%nat) ->
  4096 <= (V 40%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x22800 M) (st fx' R' 0x22830 M')
        /\ (forall x, In x KS_d5ug5d_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 70%nat) - 1)
        /\ 1 <= (V 70%nat) <= 300
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 40%nat))
      \/ (msteps RSEGS (st fx R 0x22800 M) (st fx' R' 0x22848 M')
        /\ (forall x, In x KS_d5ug5d_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 70%nat)
        /\ 0 <= (V 70%nat) <= 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 40%nat))).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV40l HV40r] [HV69l HV69r] [HV70l HV70r] G2 G9 [K0l K0r] K1 K2 [K3l K3r] K4 K5 K6 [K7l K7r] K8 K9 [K10l K10r] K11 [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 69%nat => (V 69%nat) | 70%nat => (V 70%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 71%nat. }
  assert (HR: regs_ok E Pd5ug5d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug5d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug5d.kn0).
  { unfold know_ok, Pd5ug5d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K9) | clear - HV35l HV35r K3l K3r K5; lia | clear - HV35l HV35r K3l K3r K5; lia | byte_tac ltac:(clear - HV69l HV69r K7l K7r K9; lia) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear - HV70l HV70r K10l K10r) | clear - HV35l HV35r K3l K3r K5; lia | clear - HV35l HV35r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K9) | clear; lia | rewrite (L5K.land1_bit0_true (V 69%nat) ltac:(clear - HV69l HV69r K7l K7r K9; lia) K9); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear - HV40l HV40r K12l K12r) | clear - HV35l HV35r K3l K3r K5; lia | clear - HV35l HV35r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  destruct (Pd5ug5d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug5d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5ug5d.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc Pd5ug5d.ps0) with 0x22830 in Hms. change (SR.ps_regs Pd5ug5d.ps0) with (map (fun i => (i, nth i Pd5ug5d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pd5ug5d.ps0) with Pd5ug5d.cells0 in Hcells. unfold Pd5ug5d.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug5d.regs0 Pd5ug5d.regs_out0 80 KS_d5ug5d_0 KS_d5ug5d_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pd5ug5d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug5d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5ug5d.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5ug5d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5ug5d.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5ug5d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV70l HV70r K10l K10r)]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV70l HV70r K10l K10r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K12l K12r) | clear; lia]. 
  - right.
    change (SR.ps_pc Pd5ug5d.ps1) with 0x22848 in Hms. change (SR.ps_regs Pd5ug5d.ps1) with (map (fun i => (i, nth i Pd5ug5d.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pd5ug5d.ps1) with Pd5ug5d.cells1 in Hcells. unfold Pd5ug5d.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug5d.regs0 Pd5ug5d.regs_out1 80 KS_d5ug5d_1 KS_d5ug5d_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pd5ug5d.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug5d.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5ug5d.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5ug5d.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV70l HV70r K10l K10r)]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV70l HV70r K10l K10r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K12l K12r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5uzln := LibSegZ_d5uzln.
Definition KS_d5uzln_0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5uzln.regs0 Pd5uzln.regs_out0).
Lemma KS_d5uzln_0_ok : BG.kept_ok 80 Pd5uzln.regs0 Pd5uzln.regs_out0 KS_d5uzln_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_d5uzln_1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5uzln.regs0 Pd5uzln.regs_out1).
Lemma KS_d5uzln_1_ok : BG.kept_ok 80 Pd5uzln.regs0 Pd5uzln.regs_out1 KS_d5uzln_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5uzln_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 19) = Z_to_bv 64 18446744073709551615 -> getr R (reg 22) = Z_to_bv 64 (V 75%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 224) (V 70%nat) -> 4096 <= (V 40%nat) <= 140737488355328 -> aligned (V 40%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 40%nat) \/ (V 40%nat) + 64 <= ((V 2%nat) - 352)) ->
  L5.writable RSEGS M (V 40%nat) 64 -> 0 <= (V 75%nat) <= 7 -> 0 <= (V 70%nat) <= 300 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x22830 M) (st fx' R' 0x22830 M')
        /\ (forall x, In x KS_d5uzln_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141372
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + (8 * (V 75%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 75%nat) - 1)
        /\ 1 <= (V 75%nat) <= 7
        /\ L5.u64_at RSEGS M' ((V 40%nat) + (8 * (V 75%nat))) 0)
      \/ (msteps RSEGS (st fx R 0x22830 M) (st fx' R' 0x22848 M')
        /\ (forall x, In x KS_d5uzln_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141372
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + (8 * (V 75%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 75%nat) - 1)
        /\ 0 <= (V 75%nat) <= 0
        /\ L5.u64_at RSEGS M' ((V 40%nat) + (8 * (V 75%nat))) 0)).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV70l HV70r] [HV75l HV75r] G2 G19 G22 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6 K7 K8 [K9l K9r] [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 70%nat => (V 70%nat) | 75%nat => (V 75%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E Pd5uzln.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5uzln.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5uzln.kn0).
  { unfold know_ok, Pd5uzln.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r K5l K5r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV70l HV70r K10l K10r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K5l K5r K7) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K5l K5r K7) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K5l K5r K7) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K5l K5r K7; lia | clear - HV40l HV40r K5l K5r K7; lia | clear - HV40l HV40r K5l K5r K7; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (Pd5uzln.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5uzln.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 64) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5uzln.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K5l K5r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K5l K5r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc Pd5uzln.ps0) with 0x22830 in Hms. change (SR.ps_regs Pd5uzln.ps0) with (map (fun i => (i, nth i Pd5uzln.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pd5uzln.ps0) with Pd5uzln.cells0 in Hcells. unfold Pd5uzln.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5uzln.regs0 Pd5uzln.regs_out0 80 KS_d5uzln_0 KS_d5uzln_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV75l HV75r K9l K9r)]. }
    eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K5l K5r K7 HV75l HV75r K9l K9r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  - right.
    change (SR.ps_pc Pd5uzln.ps1) with 0x22848 in Hms. change (SR.ps_regs Pd5uzln.ps1) with (map (fun i => (i, nth i Pd5uzln.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pd5uzln.ps1) with Pd5uzln.cells1 in Hcells. unfold Pd5uzln.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5uzln.regs0 Pd5uzln.regs_out1 80 KS_d5uzln_1 KS_d5uzln_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5uzln.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5uzln.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV75l HV75r K9l K9r)]. }
    eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K5l K5r K7 HV75l HV75r K9l K9r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug6 := LibSegZ_d5ug6.
Definition KS_d5ug6 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug6.regs0 Pd5ug6.regs_out0).
Lemma KS_d5ug6_ok : BG.kept_ok 80 Pd5ug6.regs0 Pd5ug6.regs_out0 KS_d5ug6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22848 M) (st fx' R' 0x21428 M')
        /\ (forall x, In x KS_d5ug6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141396
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] G2 G8 [K0l K0r] K1.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E Pd5ug6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug6.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug6.kn0).
  { unfold know_ok, Pd5ug6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_nil. }
  destruct (Pd5ug6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug6.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ug6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ug6.ps0) with 0x21428 in Hms. change (SR.ps_regs Pd5ug6.ps0) with (map (fun i => (i, nth i Pd5ug6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ug6.ps0) with Pd5ug6.cells0 in Hcells. unfold Pd5ug6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug6.regs0 Pd5ug6.regs_out0 80 KS_d5ug6 KS_d5ug6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ug6.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ug6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5ug6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ug6.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug7ni0 := LibSegZ_d5ug7ni0.
Definition KS_d5ug7ni0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug7ni0.regs0 Pd5ug7ni0.regs_out0).
Lemma KS_d5ug7ni0_ok : BG.kept_ok 80 Pd5ug7ni0.regs0 Pd5ug7ni0.regs_out0 KS_d5ug7ni0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug7ni0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) -> getr R (reg 24) = Z_to_bv 64 (V 65%nat) -> getr R (reg 25) = Z_to_bv 64 (V 62%nat) -> getr R (reg 26) = Z_to_bv 64 (V 61%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 74%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 2%nat) - 120) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 67%nat) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 ->
  L5.u64_at RSEGS M ((V 36%nat) + 8) (V 65%nat) -> Z.testbit (V 71%nat) 0 = false -> L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 65%nat))) + 8) (V 73%nat) -> 0 <= (V 73%nat) <= 18446744073709551615 ->
  (V 73%nat) < (V 74%nat) -> 1 <= (V 65%nat) <= 2 -> 1 <= (V 67%nat) <= 1 -> 0 <= (V 61%nat) <= 1 ->
  0 <= (V 62%nat) <= 2 -> 0 <= (V 37%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= i < ((V 2%nat) - 304) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22854 M) (st fx' R' 0x2291c M')
        /\ (forall x, In x KS_d5ug7ni0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141480
        /\ getr R' (reg 10) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) ((V 36%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 336) (V 37%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV37l HV37r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV67l HV67r] [HV71l HV71r] [HV73l HV73r] [HV74l HV74r] G2 G8 G21 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] [K7l K7r] K8 K9 K10 [K11l K11r] K12 K13 K14 [K15l K15r] K16 [K17l K17r] [K18l K18r] [K19l K19r] [K20l K20r] [K21l K21r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 67%nat => (V 67%nat) | 71%nat => (V 71%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd5ug7ni0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug7ni0.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug7ni0.kn0).
  { unfold know_ok, Pd5ug7ni0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV74l HV74r K6l K6r K16) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV67l HV67r K18l K18r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K6l K6r K16) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear - HV71l HV71r K11l K11r K13) | clear - HV36l HV36r K7l K7r K9; lia | clear - HV36l HV36r K7l K7r K9; lia | byte_tac ltac:(clear - HV71l HV71r K11l K11r K13; lia) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K11l K11r K13) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear - HV65l HV65r K17l K17r) | clear - HV36l HV36r K7l K7r K9; lia | clear - HV36l HV36r K7l K7r K9; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K11l K11r K13) | clear; lia | rewrite (L5K.land1_bit0_false (V 71%nat) ltac:(clear - HV71l HV71r K11l K11r K13; lia) K13); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 HV65l HV65r K17l K17r) | evalEk ZA ltac:(clear - HV73l HV73r K15l K15r K16) | clear - HV36l HV36r K7l K7r K9 HV65l HV65r K17l K17r; lia | clear - HV36l HV36r K7l K7r K9 HV65l HV65r K17l K17r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K15l K15r K16) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K16; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  destruct (Pd5ug7ni0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug7ni0.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd5ug7ni0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K9 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K9 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ug7ni0.ps0) with 0x2291c in Hms. change (SR.ps_regs Pd5ug7ni0.ps0) with (map (fun i => (i, nth i Pd5ug7ni0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ug7ni0.ps0) with Pd5ug7ni0.cells0 in Hcells. unfold Pd5ug7ni0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug7ni0.regs0 Pd5ug7ni0.regs_out0 80 KS_d5ug7ni0 KS_d5ug7ni0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ug7ni0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ug7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ug7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ug7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5ug7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5ug7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5ug7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5ug7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5ug7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear - HV65l HV65r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K20l K20r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K19l K19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K21l K21r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug7ni1 := LibSegZ_d5ug7ni1.
Definition KS_d5ug7ni1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug7ni1.regs0 Pd5ug7ni1.regs_out0).
Lemma KS_d5ug7ni1_ok : BG.kept_ok 80 Pd5ug7ni1.regs0 Pd5ug7ni1.regs_out0 KS_d5ug7ni1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug7ni1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) -> getr R (reg 24) = Z_to_bv 64 (V 65%nat) -> getr R (reg 25) = Z_to_bv 64 (V 62%nat) -> getr R (reg 26) = Z_to_bv 64 (V 61%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 74%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 2%nat) - 120) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 67%nat) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 ->
  L5.u64_at RSEGS M ((V 36%nat) + 8) (V 65%nat) -> Z.testbit (V 71%nat) 0 = false -> L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 65%nat))) + 8) (V 73%nat) -> 0 <= (V 73%nat) <= 18446744073709551615 ->
  (V 74%nat) <= (V 73%nat) -> 1 <= (V 65%nat) <= 2 -> 1 <= (V 67%nat) <= 1 -> 0 <= (V 61%nat) <= 1 ->
  0 <= (V 62%nat) <= 2 -> 0 <= (V 37%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= i < ((V 2%nat) - 304) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22854 M) (st fx' R' 0x228b0 M')
        /\ (forall x, In x KS_d5ug7ni1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141480
        /\ getr R' (reg 10) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) ((V 36%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 336) (V 37%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV37l HV37r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV67l HV67r] [HV71l HV71r] [HV73l HV73r] [HV74l HV74r] G2 G8 G21 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] [K7l K7r] K8 K9 K10 [K11l K11r] K12 K13 K14 [K15l K15r] K16 [K17l K17r] [K18l K18r] [K19l K19r] [K20l K20r] [K21l K21r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 67%nat => (V 67%nat) | 71%nat => (V 71%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd5ug7ni1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug7ni1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug7ni1.kn0).
  { unfold know_ok, Pd5ug7ni1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV74l HV74r K6l K6r K16) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV67l HV67r K18l K18r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K6l K6r K16) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear - HV71l HV71r K11l K11r K13) | clear - HV36l HV36r K7l K7r K9; lia | clear - HV36l HV36r K7l K7r K9; lia | byte_tac ltac:(clear - HV71l HV71r K11l K11r K13; lia) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K11l K11r K13) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear - HV65l HV65r K17l K17r) | clear - HV36l HV36r K7l K7r K9; lia | clear - HV36l HV36r K7l K7r K9; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K11l K11r K13) | clear; lia | rewrite (L5K.land1_bit0_false (V 71%nat) ltac:(clear - HV71l HV71r K11l K11r K13; lia) K13); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 HV65l HV65r K17l K17r) | evalEk ZA ltac:(clear - HV73l HV73r K15l K15r K16) | clear - HV36l HV36r K7l K7r K9 HV65l HV65r K17l K17r; lia | clear - HV36l HV36r K7l K7r K9 HV65l HV65r K17l K17r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K15l K15r K16) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K16; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  destruct (Pd5ug7ni1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug7ni1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd5ug7ni1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K9 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K9 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ug7ni1.ps0) with 0x228b0 in Hms. change (SR.ps_regs Pd5ug7ni1.ps0) with (map (fun i => (i, nth i Pd5ug7ni1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ug7ni1.ps0) with Pd5ug7ni1.cells0 in Hcells. unfold Pd5ug7ni1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug7ni1.regs0 Pd5ug7ni1.regs_out0 80 KS_d5ug7ni1 KS_d5ug7ni1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ug7ni1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ug7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ug7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ug7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5ug7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5ug7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5ug7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5ug7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7ni1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5ug7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear - HV65l HV65r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K20l K20r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K19l K19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K21l K21r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug7nd0 := LibSegZ_d5ug7nd0.
Definition KS_d5ug7nd0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug7nd0.regs0 Pd5ug7nd0.regs_out0).
Lemma KS_d5ug7nd0_ok : BG.kept_ok 80 Pd5ug7nd0.regs0 Pd5ug7nd0.regs_out0 KS_d5ug7nd0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug7nd0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) -> getr R (reg 24) = Z_to_bv 64 (V 65%nat) -> getr R (reg 25) = Z_to_bv 64 (V 62%nat) -> getr R (reg 26) = Z_to_bv 64 (V 61%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 74%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 2%nat) - 120) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 67%nat) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 ->
  L5.u64_at RSEGS M ((V 36%nat) + 8) (V 65%nat) -> Z.testbit (V 71%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 24) (V 72%nat) -> 4096 <= (V 72%nat) <= 140737488355328 ->
  aligned (V 72%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 72%nat) \/ (V 72%nat) + 64 <= ((V 2%nat) - 352)) -> L5.u64_at RSEGS M (((8 * (V 65%nat)) + (V 72%nat)) - 8) (V 73%nat) -> 0 <= (V 73%nat) <= 18446744073709551615 ->
  (V 73%nat) < (V 74%nat) -> 1 <= (V 65%nat) <= 7 -> 1 <= (V 67%nat) <= 1 -> 0 <= (V 61%nat) <= 1 ->
  0 <= (V 62%nat) <= 2 -> 0 <= (V 37%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= i < ((V 2%nat) - 304) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22854 M) (st fx' R' 0x2291c M')
        /\ (forall x, In x KS_d5ug7nd0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141480
        /\ getr R' (reg 10) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 336) (V 37%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV37l HV37r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV67l HV67r] [HV71l HV71r] [HV72l HV72r] [HV73l HV73r] [HV74l HV74r] G2 G8 G21 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] [K7l K7r] K8 K9 K10 [K11l K11r] K12 K13 K14 [K15l K15r] K16 K17 K18 [K19l K19r] K20 [K21l K21r] [K22l K22r] [K23l K23r] [K24l K24r] [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 67%nat => (V 67%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd5ug7nd0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug7nd0.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug7nd0.kn0).
  { unfold know_ok, Pd5ug7nd0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9 K17; lia | clear - HV2l HV2r K0l K0r K9 K17; lia | clear - HV2l HV2r K0l K0r K9 K17; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk ZA ltac:(clear - HV74l HV74r K6l K6r K20) | clear - HV2l HV2r K0l K0r K9 K17; lia | clear - HV2l HV2r K0l K0r K9 K17; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | clear - HV2l HV2r K0l K0r K9 K17; lia | clear - HV2l HV2r K0l K0r K9 K17; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk ZA ltac:(clear - HV67l HV67r K22l K22r) | clear - HV2l HV2r K0l K0r K9 K17; lia | clear - HV2l HV2r K0l K0r K9 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K6l K6r K20) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear - HV71l HV71r K11l K11r K13) | clear - HV36l HV36r K7l K7r K9; lia | clear - HV36l HV36r K7l K7r K9; lia | byte_tac ltac:(clear - HV71l HV71r K11l K11r K13; lia) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K11l K11r K13) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear - HV65l HV65r K21l K21r) | clear - HV36l HV36r K7l K7r K9; lia | clear - HV36l HV36r K7l K7r K9; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K11l K11r K13) | clear; lia | rewrite (L5K.land1_bit0_true (V 71%nat) ltac:(clear - HV71l HV71r K11l K11r K13; lia) K13); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear - HV72l HV72r K15l K15r K17) | clear - HV36l HV36r K7l K7r K9; lia | clear - HV36l HV36r K7l K7r K9; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K15l K15r K17) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV72l HV72r K15l K15r K17) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV72l HV72r K15l K15r K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV65l HV65r K21l K21r HV72l HV72r K15l K15r K17) | evalEk ZA ltac:(clear - HV73l HV73r K19l K19r K20) | clear - HV65l HV65r K21l K21r HV72l HV72r K15l K15r K17; lia | clear - HV65l HV65r K21l K21r HV72l HV72r K15l K15r K17; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K19l K19r K20) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K20; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (Pd5ug7nd0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug7nd0.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd5ug7nd0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K9 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K9 K17 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ug7nd0.ps0) with 0x2291c in Hms. change (SR.ps_regs Pd5ug7nd0.ps0) with (map (fun i => (i, nth i Pd5ug7nd0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ug7nd0.ps0) with Pd5ug7nd0.cells0 in Hcells. unfold Pd5ug7nd0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug7nd0.regs0 Pd5ug7nd0.regs_out0 80 KS_d5ug7nd0 KS_d5ug7nd0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ug7nd0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ug7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ug7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ug7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5ug7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5ug7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5ug7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5ug7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5ug7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear - HV65l HV65r K21l K21r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear - HV72l HV72r K15l K15r K17) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K24l K24r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K23l K23r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K25l K25r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug7nd1 := LibSegZ_d5ug7nd1.
Definition KS_d5ug7nd1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug7nd1.regs0 Pd5ug7nd1.regs_out0).
Lemma KS_d5ug7nd1_ok : BG.kept_ok 80 Pd5ug7nd1.regs0 Pd5ug7nd1.regs_out0 KS_d5ug7nd1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug7nd1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) -> getr R (reg 24) = Z_to_bv 64 (V 65%nat) -> getr R (reg 25) = Z_to_bv 64 (V 62%nat) -> getr R (reg 26) = Z_to_bv 64 (V 61%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 74%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 2%nat) - 120) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 67%nat) -> 0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 ->
  L5.u64_at RSEGS M ((V 36%nat) + 8) (V 65%nat) -> Z.testbit (V 71%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 24) (V 72%nat) -> 4096 <= (V 72%nat) <= 140737488355328 ->
  aligned (V 72%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 72%nat) \/ (V 72%nat) + 64 <= ((V 2%nat) - 352)) -> L5.u64_at RSEGS M (((8 * (V 65%nat)) + (V 72%nat)) - 8) (V 73%nat) -> 0 <= (V 73%nat) <= 18446744073709551615 ->
  (V 74%nat) <= (V 73%nat) -> 1 <= (V 65%nat) <= 7 -> 1 <= (V 67%nat) <= 1 -> 0 <= (V 61%nat) <= 1 ->
  0 <= (V 62%nat) <= 2 -> 0 <= (V 37%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= i < ((V 2%nat) - 304) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22854 M) (st fx' R' 0x228b0 M')
        /\ (forall x, In x KS_d5ug7nd1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141480
        /\ getr R' (reg 10) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 336) (V 37%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV37l HV37r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV67l HV67r] [HV71l HV71r] [HV72l HV72r] [HV73l HV73r] [HV74l HV74r] G2 G8 G21 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] [K7l K7r] K8 K9 K10 [K11l K11r] K12 K13 K14 [K15l K15r] K16 K17 K18 [K19l K19r] K20 [K21l K21r] [K22l K22r] [K23l K23r] [K24l K24r] [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 67%nat => (V 67%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd5ug7nd1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug7nd1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug7nd1.kn0).
  { unfold know_ok, Pd5ug7nd1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9 K17; lia | clear - HV2l HV2r K0l K0r K9 K17; lia | clear - HV2l HV2r K0l K0r K9 K17; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk ZA ltac:(clear - HV74l HV74r K6l K6r K20) | clear - HV2l HV2r K0l K0r K9 K17; lia | clear - HV2l HV2r K0l K0r K9 K17; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | clear - HV2l HV2r K0l K0r K9 K17; lia | clear - HV2l HV2r K0l K0r K9 K17; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk ZA ltac:(clear - HV67l HV67r K22l K22r) | clear - HV2l HV2r K0l K0r K9 K17; lia | clear - HV2l HV2r K0l K0r K9 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K6l K6r K20) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear - HV71l HV71r K11l K11r K13) | clear - HV36l HV36r K7l K7r K9; lia | clear - HV36l HV36r K7l K7r K9; lia | byte_tac ltac:(clear - HV71l HV71r K11l K11r K13; lia) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K11l K11r K13) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear - HV65l HV65r K21l K21r) | clear - HV36l HV36r K7l K7r K9; lia | clear - HV36l HV36r K7l K7r K9; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K11l K11r K13) | clear; lia | rewrite (L5K.land1_bit0_true (V 71%nat) ltac:(clear - HV71l HV71r K11l K11r K13; lia) K13); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9) | evalEk ZA ltac:(clear - HV72l HV72r K15l K15r K17) | clear - HV36l HV36r K7l K7r K9; lia | clear - HV36l HV36r K7l K7r K9; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K15l K15r K17) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV72l HV72r K15l K15r K17) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV72l HV72r K15l K15r K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV65l HV65r K21l K21r HV72l HV72r K15l K15r K17) | evalEk ZA ltac:(clear - HV73l HV73r K19l K19r K20) | clear - HV65l HV65r K21l K21r HV72l HV72r K15l K15r K17; lia | clear - HV65l HV65r K21l K21r HV72l HV72r K15l K15r K17; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K19l K19r K20) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K20; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (Pd5ug7nd1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug7nd1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 24) -> ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd5ug7nd1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K9 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K9 K17 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ug7nd1.ps0) with 0x228b0 in Hms. change (SR.ps_regs Pd5ug7nd1.ps0) with (map (fun i => (i, nth i Pd5ug7nd1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ug7nd1.ps0) with Pd5ug7nd1.cells0 in Hcells. unfold Pd5ug7nd1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug7nd1.regs0 Pd5ug7nd1.regs_out0 80 KS_d5ug7nd1 KS_d5ug7nd1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ug7nd1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ug7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ug7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ug7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5ug7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5ug7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5ug7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5ug7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug7nd1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5ug7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear - HV65l HV65r K21l K21r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear - HV72l HV72r K15l K15r K17) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K24l K24r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K23l K23r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9 K17) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K25l K25r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug8 := LibSegZ_d5ug8.
Definition KS_d5ug8 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug8.regs0 Pd5ug8.regs_out0).
Lemma KS_d5ug8_ok : BG.kept_ok 80 Pd5ug8.regs0 Pd5ug8.regs_out0 KS_d5ug8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 65%nat) ->
  0 <= (V 65%nat) <= 300 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x228b0 M) (st fx' R' 0x214e4 M')
        /\ (forall x, In x KS_d5ug8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141504
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 65%nat) + 1)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV65l HV65r] G2 G8 [K0l K0r] K1 K2 K3 [K4l K4r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 65%nat => (V 65%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 66%nat. }
  assert (HR: regs_ok E Pd5ug8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug8.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug8.kn0).
  { unfold know_ok, Pd5ug8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV65l HV65r K4l K4r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  destruct (Pd5ug8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug8.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ug8.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ug8.ps0) with 0x214e4 in Hms. change (SR.ps_regs Pd5ug8.ps0) with (map (fun i => (i, nth i Pd5ug8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ug8.ps0) with Pd5ug8.cells0 in Hcells. unfold Pd5ug8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug8.regs0 Pd5ug8.regs_out0 80 KS_d5ug8 KS_d5ug8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ug8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ug8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5ug8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ug8.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug9 := LibSegZ_d5ug9.
Definition KS_d5ug9 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug9.regs0 Pd5ug9.regs_out0).
Lemma KS_d5ug9_ok : BG.kept_ok 80 Pd5ug9.regs0 Pd5ug9.regs_out0 KS_d5ug9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 70%nat) ->
  1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) ->
  0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 24) (V 72%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 8) ((V 65%nat) + 1) ->
  0 <= (V 70%nat) <= 300 -> 0 <= (V 65%nat) <= 300 -> 4096 <= (V 72%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 304) <= i < ((V 2%nat) - 304) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x228c0 M) (st fx' R' 0x214e4 M')
        /\ (forall x, In x KS_d5ug9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141556
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 70%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) ((V 65%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) (V 72%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV36l HV36r] [HV65l HV65r] [HV70l HV70r] [HV71l HV71r] [HV72l HV72r] G2 G8 G9 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 [K8l K8r] K9 K10 K11 [K12l K12r] [K13l K13r] [K14l K14r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 65%nat => (V 65%nat) | 70%nat => (V 70%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E Pd5ug9.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug9.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug9.kn0).
  { unfold know_ok, Pd5ug9.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV70l HV70r K12l K12r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9) | clear - HV36l HV36r K4l K4r K6; lia | clear - HV36l HV36r K4l K4r K6; lia | byte_tac ltac:(clear - HV71l HV71r K8l K8r K9; lia) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9) | clear; lia | rewrite (L5K.land1_bit0_true (V 71%nat) ltac:(clear - HV71l HV71r K8l K8r K9; lia) K9); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | evalEk ZA ltac:(clear - HV72l HV72r K14l K14r) | clear - HV36l HV36r K4l K4r K6; lia | clear - HV36l HV36r K4l K4r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | evalEk ZA ltac:(clear - HV65l HV65r K13l K13r) | clear - HV36l HV36r K4l K4r K6; lia | clear - HV36l HV36r K4l K4r K6; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_nil. }
  destruct (Pd5ug9.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug9.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5ug9.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ug9.ps0) with 0x214e4 in Hms. change (SR.ps_regs Pd5ug9.ps0) with (map (fun i => (i, nth i Pd5ug9.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ug9.ps0) with Pd5ug9.cells0 in Hcells. unfold Pd5ug9.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug9.regs0 Pd5ug9.regs_out0 80 KS_d5ug9 KS_d5ug9_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ug9.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ug9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug9.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug9.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ug9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug9.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ug9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV65l HV65r K13l K13r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV72l HV72r K14l K14r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug9i := LibSegZ_d5ug9i.
Definition KS_d5ug9i : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug9i.regs0 Pd5ug9i.regs_out0).
Lemma KS_d5ug9i_ok : BG.kept_ok 80 Pd5ug9i.regs0 Pd5ug9i.regs_out0 KS_d5ug9i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug9i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 70%nat) ->
  1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) ->
  0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = false -> L5.u64_at RSEGS M ((V 36%nat) + 8) ((V 65%nat) + 1) -> 0 <= (V 70%nat) <= 300 ->
  0 <= (V 65%nat) <= 300 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 304) <= i < ((V 2%nat) - 304) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x228c0 M) (st fx' R' 0x214e4 M')
        /\ (forall x, In x KS_d5ug9i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141556
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 70%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) ((V 65%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) ((V 36%nat) + 16)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV36l HV36r] [HV65l HV65r] [HV70l HV70r] [HV71l HV71r] G2 G8 G9 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 [K8l K8r] K9 K10 [K11l K11r] [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 65%nat => (V 65%nat) | 70%nat => (V 70%nat) | 71%nat => (V 71%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 72%nat. }
  assert (HR: regs_ok E Pd5ug9i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug9i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug9i.kn0).
  { unfold know_ok, Pd5ug9i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV70l HV70r K11l K11r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9) | clear - HV36l HV36r K4l K4r K6; lia | clear - HV36l HV36r K4l K4r K6; lia | byte_tac ltac:(clear - HV71l HV71r K8l K8r K9; lia) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9) | clear; lia | rewrite (L5K.land1_bit0_false (V 71%nat) ltac:(clear - HV71l HV71r K8l K8r K9; lia) K9); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | evalEk ZA ltac:(clear - HV65l HV65r K12l K12r) | clear - HV36l HV36r K4l K4r K6; lia | clear - HV36l HV36r K4l K4r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  destruct (Pd5ug9i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug9i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5ug9i.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ug9i.ps0) with 0x214e4 in Hms. change (SR.ps_regs Pd5ug9i.ps0) with (map (fun i => (i, nth i Pd5ug9i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ug9i.ps0) with Pd5ug9i.cells0 in Hcells. unfold Pd5ug9i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug9i.regs0 Pd5ug9i.regs_out0 80 KS_d5ug9i KS_d5ug9i_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ug9i.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ug9i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug9i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug9i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug9i.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ug9i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug9i.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ug9i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV65l HV65r K12l K12r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K4l K4r K6) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ug10 := LibSegZ_d5ug10.
Definition KS_d5ug10 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ug10.regs0 Pd5ug10.regs_out0).
Lemma KS_d5ug10_ok : BG.kept_ok 80 Pd5ug10.regs0 Pd5ug10.regs_out0 KS_d5ug10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ug10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 (V 65%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 ->
  Z.testbit (V 69%nat) 0 = true -> L5.u64_at RSEGS M ((V 35%nat) + 24) (V 40%nat) -> L5.u64_at RSEGS M ((V 35%nat) + 8) ((V 70%nat) + 1) -> 0 <= (V 70%nat) <= 300 ->
  4096 <= (V 40%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x228f4 M) (st fx' R' 0x2291c M')
        /\ (forall x, In x KS_d5ug10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 70%nat) + 1)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 70%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 40%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV40l HV40r] [HV65l HV65r] [HV69l HV69r] [HV70l HV70r] G2 G9 G24 [K0l K0r] K1 K2 [K3l K3r] K4 K5 K6 [K7l K7r] K8 K9 K10 [K11l K11r] [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 65%nat => (V 65%nat) | 69%nat => (V 69%nat) | 70%nat => (V 70%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 71%nat. }
  assert (HR: regs_ok E Pd5ug10.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ug10.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ug10.kn0).
  { unfold know_ok, Pd5ug10.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K8) | clear - HV35l HV35r K3l K3r K5; lia | clear - HV35l HV35r K3l K3r K5; lia | byte_tac ltac:(clear - HV69l HV69r K7l K7r K8; lia) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_true (V 69%nat) ltac:(clear - HV69l HV69r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear - HV40l HV40r K12l K12r) | clear - HV35l HV35r K3l K3r K5; lia | clear - HV35l HV35r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5) | evalEk ZA ltac:(clear - HV70l HV70r K11l K11r) | clear - HV35l HV35r K3l K3r K5; lia | clear - HV35l HV35r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  destruct (Pd5ug10.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ug10.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5ug10.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ug10.ps0) with 0x2291c in Hms. change (SR.ps_regs Pd5ug10.ps0) with (map (fun i => (i, nth i Pd5ug10.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ug10.ps0) with Pd5ug10.cells0 in Hcells. unfold Pd5ug10.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ug10.regs0 Pd5ug10.regs_out0 80 KS_d5ug10 KS_d5ug10_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ug10.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ug10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug10.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ug10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ug10.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5ug10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV70l HV70r K11l K11r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K12l K12r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5upre := LibSegZ_d5upre.
Definition KS_d5upre : list nat := Eval vm_compute in (BG.kept_list 80 Pd5upre.regs0 Pd5upre.regs_out0).
Lemma KS_d5upre_ok : BG.kept_ok 80 Pd5upre.regs0 Pd5upre.regs_out0 KS_d5upre = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5upre_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 22) = Z_to_bv 64 (V 78%nat) -> getr R (reg 23) = Z_to_bv 64 (V 75%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 67%nat) -> 4096 <= (V 66%nat) <= 140737488355328 -> aligned (V 66%nat) 8 -> L5.u64_at RSEGS M ((V 66%nat) + (8 * (V 78%nat))) (V 74%nat) ->
  0 <= (V 74%nat) <= 18446744073709551615 -> (V 78%nat) < (V 75%nat) -> 0 <= (V 78%nat) <= 300 -> 0 <= (V 75%nat) <= 300 ->
  1 <= (V 67%nat) <= 301 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x2291c M) (st fx' R' 0x2294c M')
        /\ (forall x, In x KS_d5upre -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141608
        /\ getr R' (reg 10) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 75%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (8 * (V 67%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 (((-8) * (V 67%nat)) + (8 * (V 75%nat)))
        /\ getr R' (reg 20) = Z_to_bv 64 (((-1) * (V 67%nat)) + 1152921504606846976)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 ((-1) * (V 67%nat))).
Proof.
  intros [HV2l HV2r] [HV66l HV66r] [HV67l HV67r] [HV74l HV74r] [HV75l HV75r] [HV78l HV78r] G2 G21 G22 G23 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6 K7 [K8l K8r] K9 [K10l K10r] [K11l K11r] [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 74%nat => (V 74%nat) | 75%nat => (V 75%nat) | 78%nat => (V 78%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 79%nat. }
  assert (HR: regs_ok E Pd5upre.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5upre.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5upre.kn0).
  { unfold know_ok, Pd5upre.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV66l HV66r K5l K5r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV67l HV67r K12l K12r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r HV78l HV78r K9 K10l K10r) | evalEk ZA ltac:(clear - HV74l HV74r K8l K8r) | clear - HV66l HV66r K5l K5r HV78l HV78r K9 K10l K10r; lia | clear - HV66l HV66r K5l K5r HV78l HV78r K9 K10l K10r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K9; clear; intro; destruct (Z.ltb_spec0 (V 78%nat) (V 75%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K9 K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K9 K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  destruct (Pd5upre.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5upre.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5upre.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5upre.ps0) with 0x2294c in Hms. change (SR.ps_regs Pd5upre.ps0) with (map (fun i => (i, nth i Pd5upre.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5upre.ps0) with Pd5upre.cells0 in Hcells. unfold Pd5upre.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5upre.regs0 Pd5upre.regs_out0 80 KS_d5upre KS_d5upre_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5upre.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5upre.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5upre.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5upre.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5upre.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5upre.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5upre.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5upre.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5upre.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5upre.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5upre.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5upre.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5upre.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5upre.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5upre.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pd5upre.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5upre.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd5upre.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5upre.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pd5upre.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5uprx := LibSegZ_d5uprx.
Definition KS_d5uprx : list nat := Eval vm_compute in (BG.kept_list 80 Pd5uprx.regs0 Pd5uprx.regs_out0).
Lemma KS_d5uprx_ok : BG.kept_ok 80 Pd5uprx.regs0 Pd5uprx.regs_out0 KS_d5uprx = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5uprx_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 22) = Z_to_bv 64 (V 78%nat) -> getr R (reg 23) = Z_to_bv 64 (V 75%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 67%nat) -> 4096 <= (V 66%nat) <= 140737488355328 -> aligned (V 66%nat) 8 -> (V 75%nat) <= (V 78%nat) ->
  0 <= (V 78%nat) <= 300 -> 0 <= (V 75%nat) <= 300 -> 1 <= (V 67%nat) <= 301 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x2291c M) (st fx' R' 0x229e0 M')
        /\ (forall x, In x KS_d5uprx -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141608
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 66%nat) + (8 * (V 78%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV66l HV66r] [HV67l HV67r] [HV75l HV75r] [HV78l HV78r] G2 G21 G22 G23 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6 K7 [K8l K8r] [K9l K9r] [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 75%nat => (V 75%nat) | 78%nat => (V 78%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 79%nat. }
  assert (HR: regs_ok E Pd5uprx.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5uprx.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5uprx.kn0).
  { unfold know_ok, Pd5uprx.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV66l HV66r K5l K5r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV67l HV67r K10l K10r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV66l HV66r K5l K5r) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K7; clear; intro; destruct (Z.ltb_spec0 (V 78%nat) (V 75%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K7 K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K7 K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (Pd5uprx.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5uprx.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5uprx.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5uprx.ps0) with 0x229e0 in Hms. change (SR.ps_regs Pd5uprx.ps0) with (map (fun i => (i, nth i Pd5uprx.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5uprx.ps0) with Pd5uprx.cells0 in Hcells. unfold Pd5uprx.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5uprx.regs0 Pd5uprx.regs_out0 80 KS_d5uprx KS_d5uprx_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5uprx.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5uprx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uprx.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5uprx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uprx.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5uprx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uprx.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5uprx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uprx.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5uprx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5uprx.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5uprx.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ul1 := LibSegZ_d5ul1.
Definition KS_d5ul1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ul1.regs0 Pd5ul1.regs_out0).
Lemma KS_d5ul1_ok : BG.kept_ok 80 Pd5ul1.regs0 Pd5ul1.regs_out0 KS_d5ul1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ul1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 67%nat) + (V 77%nat)) -> getr R (reg 24) = Z_to_bv 64 (V 74%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 304) (V 79%nat) ->
  4096 <= (V 79%nat) <= 140737488355328 -> aligned (V 79%nat) 8 -> L5.u64_at RSEGS M ((8 * (V 67%nat)) + ((8 * (V 77%nat)) + (V 79%nat))) (V 73%nat) -> L5.u64_at RSEGS M (((8 * (V 67%nat)) + ((8 * (V 77%nat)) + (V 79%nat))) - 8) (V 76%nat) ->
  1 <= (V 67%nat) <= 301 -> 0 <= (V 77%nat) <= 299 -> 0 <= (V 73%nat) <= 18446744073709551615 -> 0 <= (V 76%nat) <= 18446744073709551615 ->
  0 <= (V 74%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x2294c M) (st fx' R' 0x22e6c M')
        /\ (forall x, In x KS_d5ul1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141696
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 76%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 67%nat) + (V 77%nat)) - 1)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 73%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV67l HV67r] [HV73l HV73r] [HV74l HV74r] [HV76l HV76r] [HV77l HV77r] [HV79l HV79r] G2 G18 G21 G23 G24 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 [K8l K8r] [K9l K9r] [K10l K10r] [K11l K11r] [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 67%nat => (V 67%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | 76%nat => (V 76%nat) | 77%nat => (V 77%nat) | 79%nat => (V 79%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E Pd5ul1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ul1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ul1.kn0).
  { unfold know_ok, Pd5ul1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV79l HV79r K4l K4r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV79l HV79r K4l K4r) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV67l HV67r K8l K8r HV77l HV77r K9l K9r HV79l HV79r K4l K4r) | evalEk ZA ltac:(clear - HV73l HV73r K10l K10r) | clear - HV67l HV67r K8l K8r HV77l HV77r K9l K9r HV79l HV79r K4l K4r; lia | clear - HV67l HV67r K8l K8r HV77l HV77r K9l K9r HV79l HV79r K4l K4r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV67l HV67r K8l K8r HV77l HV77r K9l K9r HV79l HV79r K4l K4r) | evalEk ZA ltac:(clear - HV76l HV76r K11l K11r) | clear - HV67l HV67r K8l K8r HV77l HV77r K9l K9r HV79l HV79r K4l K4r; lia | clear - HV67l HV67r K8l K8r HV77l HV77r K9l K9r HV79l HV79r K4l K4r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  destruct (Pd5ul1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ul1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ul1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ul1.ps0) with 0x22e6c in Hms. change (SR.ps_regs Pd5ul1.ps0) with (map (fun i => (i, nth i Pd5ul1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ul1.ps0) with Pd5ul1.cells0 in Hcells. unfold Pd5ul1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ul1.regs0 Pd5ul1.regs_out0 80 KS_d5ul1 KS_d5ul1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ul1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ul1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ul1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ul1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ul1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5ul1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5ul1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pd5ul1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5ul1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5ul1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ul2 := LibSegZ_d5ul2.
Definition KS_d5ul2 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ul2.regs0 Pd5ul2.regs_out0).
Lemma KS_d5ul2_ok : BG.kept_ok 80 Pd5ul2.regs0 Pd5ul2.regs_out0 KS_d5ul2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ul2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 10) = Z_to_bv 64 (V 76%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (8 * (V 77%nat)) -> getr R (reg 20) = Z_to_bv 64 (((-1) * (V 67%nat)) + 1152921504606846976) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 67%nat) + (V 77%nat)) -> getr R (reg 27) = Z_to_bv 64 ((-1) * (V 67%nat)) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 304) (V 79%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 67%nat) -> 4096 <= (V 79%nat) <= 140737488355328 -> aligned (V 79%nat) 8 ->
  1 <= (V 67%nat) <= 301 -> 0 <= (V 77%nat) <= 299 -> 0 <= (V 76%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 312) <= bv_unsigned a < ((V 2%nat) - 312) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 312) <= i < ((V 2%nat) - 312) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22980 M) (st fx' R' 0x22f68 M')
        /\ (forall x, In x KS_d5ul2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141760
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((8 * (V 77%nat)) + (V 79%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 312)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 77%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) (V 76%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV66l HV66r] [HV67l HV67r] [HV76l HV76r] [HV77l HV77r] [HV79l HV79r] G2 G10 G18 G19 G20 G21 G23 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] [K9l K9r] [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 76%nat => (V 76%nat) | 77%nat => (V 77%nat) | 79%nat => (V 79%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E Pd5ul2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ul2.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ul2.kn0).
  { unfold know_ok, Pd5ul2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV79l HV79r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV67l HV67r K8l K8r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV79l HV79r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (Pd5ul2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ul2.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 312) <= bv_unsigned a < ((V 2%nat) - 312) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5ul2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ul2.ps0) with 0x22f68 in Hms. change (SR.ps_regs Pd5ul2.ps0) with (map (fun i => (i, nth i Pd5ul2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ul2.ps0) with Pd5ul2.cells0 in Hcells. unfold Pd5ul2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ul2.regs0 Pd5ul2.regs_out0 80 KS_d5ul2 KS_d5ul2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ul2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ul2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ul2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ul2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ul2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5ul2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5ul2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5ul2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV76l HV76r K10l K10r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ul3c := LibSegZ_d5ul3c.
Definition KS_d5ul3c : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ul3c.regs0 Pd5ul3c.regs_out0).
Lemma KS_d5ul3c_ok : BG.kept_ok 80 Pd5ul3c.regs0 Pd5ul3c.regs_out0 KS_d5ul3c = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ul3c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 19) = Z_to_bv 64 (8 * (V 77%nat)) -> getr R (reg 22) = Z_to_bv 64 (V 78%nat) -> getr R (reg 23) = Z_to_bv 64 (V 77%nat) -> getr R (reg 25) = Z_to_bv 64 (V 75%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 312) (V 76%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 232) (V 68%nat) -> 4096 <= (V 68%nat) <= 140737488355328 -> aligned (V 68%nat) 8 -> L5.writable RSEGS M ((V 68%nat) + (8 * (V 77%nat))) 8 ->
  (((V 2%nat) - 352) + 352 <= ((V 68%nat) + (8 * (V 77%nat))) \/ ((V 68%nat) + (8 * (V 77%nat))) + 8 <= ((V 2%nat) - 352)) -> (V 78%nat) < (V 75%nat) -> 0 <= (V 78%nat) <= 300 -> 0 <= (V 75%nat) <= 300 ->
  0 <= (V 77%nat) <= 299 -> 0 <= (V 76%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 68%nat) + (8 * (V 77%nat))) + 0) <= bv_unsigned a < (((V 68%nat) + (8 * (V 77%nat))) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 68%nat) + (8 * (V 77%nat))) + 0) <= i < (((V 68%nat) + (8 * (V 77%nat))) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x229c0 M) (st fx' R' 0x2294c M')
        /\ (forall x, In x KS_d5ul3c -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141776
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 68%nat) + (8 * (V 77%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 ((8 * (V 77%nat)) - 8)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 76%nat)
        /\ L5.u64_at RSEGS M' ((V 68%nat) + (8 * (V 77%nat))) (V 76%nat)).
Proof.
  intros [HV2l HV2r] [HV68l HV68r] [HV75l HV75r] [HV76l HV76r] [HV77l HV77r] [HV78l HV78r] G2 G19 G22 G23 G25 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6 K7 K8 K9 [K10l K10r] [K11l K11r] [K12l K12r] [K13l K13r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 68%nat => (V 68%nat) | 75%nat => (V 75%nat) | 76%nat => (V 76%nat) | 77%nat => (V 77%nat) | 78%nat => (V 78%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 79%nat. }
  assert (HR: regs_ok E Pd5ul3c.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ul3c.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ul3c.kn0).
  { unfold know_ok, Pd5ul3c.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear - HV76l HV76r K13l K13r) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r) | evalEk ZA ltac:(clear) | clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r; lia | clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r; lia | clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K9; clear; intro; destruct (Z.ltb_spec0 (V 78%nat) (V 75%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K9 K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K9 K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K8 K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_nil. }
  destruct (Pd5ul3c.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ul3c.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 68%nat) + (8 * (V 77%nat))) + 0) <= bv_unsigned a < (((V 68%nat) + (8 * (V 77%nat))) + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5ul3c.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r) | evalEk' ZA Hag ltac:(clear) | clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ul3c.ps0) with 0x2294c in Hms. change (SR.ps_regs Pd5ul3c.ps0) with (map (fun i => (i, nth i Pd5ul3c.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ul3c.ps0) with Pd5ul3c.cells0 in Hcells. unfold Pd5ul3c.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ul3c.regs0 Pd5ul3c.regs_out0 80 KS_d5ul3c KS_d5ul3c_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ul3c.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ul3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3c.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ul3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3c.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ul3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3c.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ul3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3c.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5ul3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3c.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5ul3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3c.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5ul3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3c.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5ul3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3c.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5ul3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r) | evalEk' ZA Hag ltac:(clear - HV76l HV76r K13l K13r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ul3x := LibSegZ_d5ul3x.
Definition KS_d5ul3x : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ul3x.regs0 Pd5ul3x.regs_out0).
Lemma KS_d5ul3x_ok : BG.kept_ok 80 Pd5ul3x.regs0 Pd5ul3x.regs_out0 KS_d5ul3x = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ul3x_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 19) = Z_to_bv 64 (8 * (V 77%nat)) -> getr R (reg 22) = Z_to_bv 64 (V 78%nat) -> getr R (reg 23) = Z_to_bv 64 (V 77%nat) -> getr R (reg 25) = Z_to_bv 64 (V 75%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 312) (V 76%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 232) (V 68%nat) -> 4096 <= (V 68%nat) <= 140737488355328 -> aligned (V 68%nat) 8 -> L5.writable RSEGS M ((V 68%nat) + (8 * (V 77%nat))) 8 ->
  (((V 2%nat) - 352) + 352 <= ((V 68%nat) + (8 * (V 77%nat))) \/ ((V 68%nat) + (8 * (V 77%nat))) + 8 <= ((V 2%nat) - 352)) -> (V 75%nat) <= (V 78%nat) -> 0 <= (V 78%nat) <= 300 -> 0 <= (V 75%nat) <= 300 ->
  0 <= (V 77%nat) <= 299 -> 0 <= (V 76%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 68%nat) + (8 * (V 77%nat))) + 0) <= bv_unsigned a < (((V 68%nat) + (8 * (V 77%nat))) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 68%nat) + (8 * (V 77%nat))) + 0) <= i < (((V 68%nat) + (8 * (V 77%nat))) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x229c0 M) (st fx' R' 0x229e0 M')
        /\ (forall x, In x KS_d5ul3x -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141776
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 68%nat) + (8 * (V 77%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 ((8 * (V 77%nat)) - 8)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 76%nat)
        /\ L5.u64_at RSEGS M' ((V 68%nat) + (8 * (V 77%nat))) (V 76%nat)).
Proof.
  intros [HV2l HV2r] [HV68l HV68r] [HV75l HV75r] [HV76l HV76r] [HV77l HV77r] [HV78l HV78r] G2 G19 G22 G23 G25 [K0l K0r] K1 K2 K3 K4 [K5l K5r] K6 K7 K8 K9 [K10l K10r] [K11l K11r] [K12l K12r] [K13l K13r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 68%nat => (V 68%nat) | 75%nat => (V 75%nat) | 76%nat => (V 76%nat) | 77%nat => (V 77%nat) | 78%nat => (V 78%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 79%nat. }
  assert (HR: regs_ok E Pd5ul3x.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ul3x.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ul3x.kn0).
  { unfold know_ok, Pd5ul3x.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear - HV76l HV76r K13l K13r) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r) | evalEk ZA ltac:(clear) | clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r; lia | clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r; lia | clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K9; clear; intro; destruct (Z.ltb_spec0 (V 78%nat) (V 75%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K9 K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K9 K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K8 K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_nil. }
  destruct (Pd5ul3x.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ul3x.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 68%nat) + (8 * (V 77%nat))) + 0) <= bv_unsigned a < (((V 68%nat) + (8 * (V 77%nat))) + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5ul3x.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r) | evalEk' ZA Hag ltac:(clear) | clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ul3x.ps0) with 0x229e0 in Hms. change (SR.ps_regs Pd5ul3x.ps0) with (map (fun i => (i, nth i Pd5ul3x.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ul3x.ps0) with Pd5ul3x.cells0 in Hcells. unfold Pd5ul3x.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ul3x.regs0 Pd5ul3x.regs_out0 80 KS_d5ul3x KS_d5ul3x_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ul3x.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ul3x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3x.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ul3x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3x.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ul3x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3x.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5ul3x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3x.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5ul3x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3x.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5ul3x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3x.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5ul3x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3x.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5ul3x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ul3x.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5ul3x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV68l HV68r K5l K5r K8 HV77l HV77r K12l K12r) | evalEk' ZA Hag ltac:(clear - HV76l HV76r K13l K13r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ux1 := LibSegZ_d5ux1.
Definition KS_d5ux1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ux1.regs0 Pd5ux1.regs_out0).
Lemma KS_d5ux1_ok : BG.kept_ok 80 Pd5ux1.regs0 Pd5ux1.regs_out0 KS_d5ux1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ux1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x229e0 M) (st fx' R' 0x21abc M')
        /\ (forall x, In x KS_d5ux1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141800
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] G2 G9 [K0l K0r] K1.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E Pd5ux1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ux1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ux1.kn0).
  { unfold know_ok, Pd5ux1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_nil. }
  destruct (Pd5ux1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ux1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ux1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ux1.ps0) with 0x21abc in Hms. change (SR.ps_regs Pd5ux1.ps0) with (map (fun i => (i, nth i Pd5ux1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ux1.ps0) with Pd5ux1.cells0 in Hcells. unfold Pd5ux1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ux1.regs0 Pd5ux1.regs_out0 80 KS_d5ux1 KS_d5ux1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ux1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ux1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5ux1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ux1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ux2n := LibSegZ_d5ux2n.
Definition KS_d5ux2n : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ux2n.regs0 Pd5ux2n.regs_out0).
Lemma KS_d5ux2n_ok : BG.kept_ok 80 Pd5ux2n.regs0 Pd5ux2n.regs_out0 KS_d5ux2n = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ux2n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 320) (V 62%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 328) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 336) 0 -> 1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 -> L5.writable RSEGS M (V 35%nat) 32 ->
  0 <= (V 61%nat) <= 1 -> 0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 35%nat) + 0) <= i < ((V 35%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x229e8 M) (st fx' R' 0x22a30 M')
        /\ (forall x, In x KS_d5ux2n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (2 * (V 61%nat))
        /\ getr R' (reg 19) = Z_to_bv 64 (V 62%nat)
        /\ L5.u8_at RSEGS M' (V 35%nat) (Z.lor (Z.land (V 69%nat) 253) ((2 * (V 61%nat)) mod 2 ^ 64))).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV61l HV61r] [HV62l HV62r] [HV69l HV69r] G2 G9 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 [K10l K10r] K11 [K12l K12r] [K13l K13r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 69%nat => (V 69%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E Pd5ux2n.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ux2n.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ux2n.kn0).
  { unfold know_ok, Pd5ux2n.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear - HV62l HV62r K13l K13r) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear - HV61l HV61r K12l K12r) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | evalEk ZA ltac:(clear - HV69l HV69r K10l K10r) | clear - HV35l HV35r K6l K6r K8; lia | clear - HV35l HV35r K6l K6r K8; lia | byte_tac ltac:(clear - HV69l HV69r K10l K10r; lia) | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K6l K6r K8; lia | clear - HV35l HV35r K6l K6r K8; lia | clear - HV35l HV35r K6l K6r K8; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_nil. }
  destruct (Pd5ux2n.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ux2n.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5ux2n.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K6l K6r K8) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K6l K6r K8 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ux2n.ps0) with 0x22a30 in Hms. change (SR.ps_regs Pd5ux2n.ps0) with (map (fun i => (i, nth i Pd5ux2n.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ux2n.ps0) with Pd5ux2n.cells0 in Hcells. unfold Pd5ux2n.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ux2n.regs0 Pd5ux2n.regs_out0 80 KS_d5ux2n KS_d5ux2n_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ux2n.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ux2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ux2n.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ux2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ux2n.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5ux2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K6l K6r K8) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV61l HV61r K12l K12r HV69l HV69r K10l K10r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ut0i := LibSegZ_d5ut0i.
Definition KS_d5ut0i : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ut0i.regs0 Pd5ut0i.regs_out0).
Lemma KS_d5ut0i_ok : BG.kept_ok 80 Pd5ut0i.regs0 Pd5ut0i.regs_out0 KS_d5ut0i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ut0i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 280) (V 41%nat) ->
  0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22a30 M) (st fx' R' 0x22a50 M')
        /\ (forall x, In x KS_d5ut0i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] G2 [K0l K0r] K1 K2 K3 [K4l K4r] K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E Pd5ut0i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ut0i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ut0i.kn0).
  { unfold know_ok, Pd5ut0i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K4l K4r K5; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false (V 41%nat) ltac:(clear - HV41l HV41r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_nil. }
  destruct (Pd5ut0i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ut0i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ut0i.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ut0i.ps0) with 0x22a50 in Hms. change (SR.ps_regs Pd5ut0i.ps0) with (map (fun i => (i, nth i Pd5ut0i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ut0i.ps0) with Pd5ut0i.cells0 in Hcells. unfold Pd5ut0i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ut0i.regs0 Pd5ut0i.regs_out0 80 KS_d5ut0i KS_d5ut0i_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg Pd5ut0i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ut0i.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ut0d := LibSegZ_d5ut0d.
Definition KS_d5ut0d : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ut0d.regs0 Pd5ut0d.regs_out0).
Lemma KS_d5ut0d_ok : BG.kept_ok 80 Pd5ut0d.regs0 Pd5ut0d.regs_out0 KS_d5ut0d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ut0d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 280) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 264) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 256) (V 43%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = true ->
  1 <= (V 42%nat) <= 4096 -> 4096 <= (V 43%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22a30 M) (st fx' R' 0x3f724 M')
        /\ (forall x, In x KS_d5ut0d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141904
        /\ getr R' (reg 10) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 42%nat))).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] G2 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] [K9l K9r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E Pd5ut0d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ut0d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ut0d.kn0).
  { unfold know_ok, Pd5ut0d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K6l K6r K7; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV42l HV42r K8l K8r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV43l HV43r K9l K9r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | clear; lia | rewrite (L5K.land1_bit0_true (V 41%nat) ltac:(clear - HV41l HV41r K6l K6r K7; lia) K7); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  destruct (Pd5ut0d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ut0d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ut0d.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ut0d.ps0) with 0x3f724 in Hms. change (SR.ps_regs Pd5ut0d.ps0) with (map (fun i => (i, nth i Pd5ut0d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ut0d.ps0) with Pd5ut0d.cells0 in Hcells. unfold Pd5ut0d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ut0d.regs0 Pd5ut0d.regs_out0 80 KS_d5ut0d KS_d5ut0d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ut0d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ut0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ut0d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ut0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5ut0d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ut0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ut1i := LibSegZ_d5ut1i.
Definition KS_d5ut1i : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ut1i.regs0 Pd5ut1i.regs_out0).
Lemma KS_d5ut1i_ok : BG.kept_ok 80 Pd5ut1i.regs0 Pd5ut1i.regs_out0 KS_d5ut1i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ut1i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 216) (V 41%nat) ->
  0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22a50 M) (st fx' R' 0x22b80 M')
        /\ (forall x, In x KS_d5ut1i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] G2 [K0l K0r] K1 K2 K3 [K4l K4r] K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E Pd5ut1i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ut1i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ut1i.kn0).
  { unfold know_ok, Pd5ut1i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K4l K4r K5; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false (V 41%nat) ltac:(clear - HV41l HV41r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_nil. }
  destruct (Pd5ut1i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ut1i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ut1i.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ut1i.ps0) with 0x22b80 in Hms. change (SR.ps_regs Pd5ut1i.ps0) with (map (fun i => (i, nth i Pd5ut1i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ut1i.ps0) with Pd5ut1i.cells0 in Hcells. unfold Pd5ut1i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ut1i.regs0 Pd5ut1i.regs_out0 80 KS_d5ut1i KS_d5ut1i_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg Pd5ut1i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ut1i.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ut1d := LibSegZ_d5ut1d.
Definition KS_d5ut1d : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ut1d.regs0 Pd5ut1d.regs_out0).
Lemma KS_d5ut1d_ok : BG.kept_ok 80 Pd5ut1d.regs0 Pd5ut1d.regs_out0 KS_d5ut1d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ut1d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 216) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 200) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 43%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = true ->
  1 <= (V 42%nat) <= 4096 -> 4096 <= (V 43%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22a50 M) (st fx' R' 0x3f724 M')
        /\ (forall x, In x KS_d5ut1d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141936
        /\ getr R' (reg 10) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 42%nat))).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] G2 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] [K9l K9r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E Pd5ut1d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ut1d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ut1d.kn0).
  { unfold know_ok, Pd5ut1d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K6l K6r K7; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV42l HV42r K8l K8r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV43l HV43r K9l K9r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | clear; lia | rewrite (L5K.land1_bit0_true (V 41%nat) ltac:(clear - HV41l HV41r K6l K6r K7; lia) K7); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  destruct (Pd5ut1d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ut1d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ut1d.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ut1d.ps0) with 0x3f724 in Hms. change (SR.ps_regs Pd5ut1d.ps0) with (map (fun i => (i, nth i Pd5ut1d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ut1d.ps0) with Pd5ut1d.cells0 in Hcells. unfold Pd5ut1d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ut1d.regs0 Pd5ut1d.regs_out0 80 KS_d5ut1d KS_d5ut1d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ut1d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ut1d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ut1d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ut1d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5ut1d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ut1d.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ut1j := LibSegZ_d5ut1j.
Definition KS_d5ut1j : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ut1j.regs0 Pd5ut1j.regs_out0).
Lemma KS_d5ut1j_ok : BG.kept_ok 80 Pd5ut1j.regs0 Pd5ut1j.regs_out0 KS_d5ut1j = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ut1j_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22a70 M) (st fx' R' 0x22b80 M')
        /\ (forall x, In x KS_d5ut1j -> getr R' (reg x) = getr R (reg x))).
Proof.
  intros [HV2l HV2r] G2 [K0l K0r] K1.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pd5ut1j.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ut1j.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ut1j.kn0).
  { unfold know_ok, Pd5ut1j.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_nil. }
  destruct (Pd5ut1j.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ut1j.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ut1j.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ut1j.ps0) with 0x22b80 in Hms. change (SR.ps_regs Pd5ut1j.ps0) with (map (fun i => (i, nth i Pd5ut1j.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ut1j.ps0) with Pd5ut1j.cells0 in Hcells. unfold Pd5ut1j.cells0 in Hcells.
  split. { exact Hms. }
  intros j Hj. apply (BG.kept_regs E E' R R' Pd5ut1j.regs0 Pd5ut1j.regs_out0 80 KS_d5ut1j KS_d5ut1j_ok HR Hag Hregs j Hj). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ut2i := LibSegZ_d5ut2i.
Definition KS_d5ut2i : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ut2i.regs0 Pd5ut2i.regs_out0).
Lemma KS_d5ut2i_ok : BG.kept_ok 80 Pd5ut2i.regs0 Pd5ut2i.regs_out0 KS_d5ut2i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ut2i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 184) (V 41%nat) ->
  0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22b80 M) (st fx' R' 0x22ba0 M')
        /\ (forall x, In x KS_d5ut2i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] G2 [K0l K0r] K1 K2 K3 [K4l K4r] K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E Pd5ut2i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ut2i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ut2i.kn0).
  { unfold know_ok, Pd5ut2i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K4l K4r K5; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false (V 41%nat) ltac:(clear - HV41l HV41r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_nil. }
  destruct (Pd5ut2i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ut2i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ut2i.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ut2i.ps0) with 0x22ba0 in Hms. change (SR.ps_regs Pd5ut2i.ps0) with (map (fun i => (i, nth i Pd5ut2i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ut2i.ps0) with Pd5ut2i.cells0 in Hcells. unfold Pd5ut2i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ut2i.regs0 Pd5ut2i.regs_out0 80 KS_d5ut2i KS_d5ut2i_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg Pd5ut2i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ut2i.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ut2d := LibSegZ_d5ut2d.
Definition KS_d5ut2d : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ut2d.regs0 Pd5ut2d.regs_out0).
Lemma KS_d5ut2d_ok : BG.kept_ok 80 Pd5ut2d.regs0 Pd5ut2d.regs_out0 KS_d5ut2d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ut2d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 184) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 43%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = true ->
  1 <= (V 42%nat) <= 4096 -> 4096 <= (V 43%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22b80 M) (st fx' R' 0x3f724 M')
        /\ (forall x, In x KS_d5ut2d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 142240
        /\ getr R' (reg 10) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 42%nat))).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] G2 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] [K9l K9r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E Pd5ut2d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ut2d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ut2d.kn0).
  { unfold know_ok, Pd5ut2d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K6l K6r K7; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV42l HV42r K8l K8r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV43l HV43r K9l K9r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | clear; lia | rewrite (L5K.land1_bit0_true (V 41%nat) ltac:(clear - HV41l HV41r K6l K6r K7; lia) K7); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  destruct (Pd5ut2d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ut2d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ut2d.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ut2d.ps0) with 0x3f724 in Hms. change (SR.ps_regs Pd5ut2d.ps0) with (map (fun i => (i, nth i Pd5ut2d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ut2d.ps0) with Pd5ut2d.cells0 in Hcells. unfold Pd5ut2d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ut2d.regs0 Pd5ut2d.regs_out0 80 KS_d5ut2d KS_d5ut2d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ut2d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ut2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ut2d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ut2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5ut2d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ut2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ut3i := LibSegZ_d5ut3i.
Definition KS_d5ut3i : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ut3i.regs0 Pd5ut3i.regs_out0).
Lemma KS_d5ut3i_ok : BG.kept_ok 80 Pd5ut3i.regs0 Pd5ut3i.regs_out0 KS_d5ut3i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ut3i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22ba0 M) (st fx' R' 0x22bc0 M')
        /\ (forall x, In x KS_d5ut3i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] G2 [K0l K0r] K1 K2 K3 [K4l K4r] K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E Pd5ut3i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ut3i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ut3i.kn0).
  { unfold know_ok, Pd5ut3i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K4l K4r K5; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false (V 41%nat) ltac:(clear - HV41l HV41r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_nil. }
  destruct (Pd5ut3i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ut3i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ut3i.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ut3i.ps0) with 0x22bc0 in Hms. change (SR.ps_regs Pd5ut3i.ps0) with (map (fun i => (i, nth i Pd5ut3i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ut3i.ps0) with Pd5ut3i.cells0 in Hcells. unfold Pd5ut3i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ut3i.regs0 Pd5ut3i.regs_out0 80 KS_d5ut3i KS_d5ut3i_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg Pd5ut3i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ut3i.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5ut3d := LibSegZ_d5ut3d.
Definition KS_d5ut3d : list nat := Eval vm_compute in (BG.kept_list 80 Pd5ut3d.regs0 Pd5ut3d.regs_out0).
Lemma KS_d5ut3d_ok : BG.kept_ok 80 Pd5ut3d.regs0 Pd5ut3d.regs_out0 KS_d5ut3d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5ut3d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 43%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = true ->
  1 <= (V 42%nat) <= 4096 -> 4096 <= (V 43%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22ba0 M) (st fx' R' 0x3f724 M')
        /\ (forall x, In x KS_d5ut3d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 142272
        /\ getr R' (reg 10) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 42%nat))).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] G2 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] [K9l K9r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E Pd5ut3d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5ut3d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5ut3d.kn0).
  { unfold know_ok, Pd5ut3d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K6l K6r K7; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV42l HV42r K8l K8r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV43l HV43r K9l K9r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r K7) | clear; lia | rewrite (L5K.land1_bit0_true (V 41%nat) ltac:(clear - HV41l HV41r K6l K6r K7; lia) K7); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  destruct (Pd5ut3d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5ut3d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5ut3d.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5ut3d.ps0) with 0x3f724 in Hms. change (SR.ps_regs Pd5ut3d.ps0) with (map (fun i => (i, nth i Pd5ut3d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5ut3d.ps0) with Pd5ut3d.cells0 in Hcells. unfold Pd5ut3d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5ut3d.regs0 Pd5ut3d.regs_out0 80 KS_d5ut3d KS_d5ut3d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5ut3d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5ut3d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5ut3d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5ut3d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5ut3d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5ut3d.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5uepi := LibSegZ_d5uepi.
Definition KS_d5uepi : list nat := Eval vm_compute in (BG.kept_list 80 Pd5uepi.regs0 Pd5uepi.regs_out0).
Lemma KS_d5uepi_ok : BG.kept_ok 80 Pd5uepi.regs0 Pd5uepi.regs_out0 KS_d5uepi = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5uepi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22bc0 M) (st fx' R' 0x22bf8 M')
        /\ (forall x, In x KS_d5uepi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 60%nat)).
Proof.
  intros [HV2l HV2r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] [HV55l HV55r] [HV56l HV56r] [HV57l HV57r] [HV58l HV58r] [HV59l HV59r] [HV60l HV60r] G2 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | 55%nat => Z_to_bv 64 (V 55%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | 55%nat => (V 55%nat) | 56%nat => (V 56%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | 59%nat => (V 59%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E Pd5uepi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5uepi.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5uepi.kn0).
  { unfold know_ok, Pd5uepi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K15]. }
    apply Forall_nil. }
  destruct (Pd5uepi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5uepi.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5uepi.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5uepi.ps0) with 0x22bf8 in Hms. change (SR.ps_regs Pd5uepi.ps0) with (map (fun i => (i, nth i Pd5uepi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5uepi.ps0) with Pd5uepi.cells0 in Hcells. unfold Pd5uepi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5uepi.regs0 Pd5uepi.regs_out0 80 KS_d5uepi KS_d5uepi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5uepi.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pd5uepi.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End L5DIVNPU.
