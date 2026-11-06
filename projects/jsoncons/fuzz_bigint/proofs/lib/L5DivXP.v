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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5DivXP.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVXP.
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
Module Pdxe1 := LibSegZ_dxe1.
Definition KS_dxe1 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxe1.regs0 Pdxe1.regs_out0).
Lemma KS_dxe1_ok : BG.kept_ok 80 Pdxe1.regs0 Pdxe1.regs_out0 KS_dxe1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxe1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 200) <= bv_unsigned a < ((V 2%nat) - 200) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 200) <= i < ((V 2%nat) - 200) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21e54 M) (st fx' R' 0x21010 M')
        /\ (forall x, In x KS_dxe1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 138864
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 200)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 200) 0).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] G2 G9 [K0l K0r] K1 K2.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E Pdxe1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxe1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxe1.kn0).
  { unfold know_ok, Pdxe1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  destruct (Pdxe1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxe1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 200) <= bv_unsigned a < ((V 2%nat) - 200) + 32) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pdxe1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxe1.ps0) with 0x21010 in Hms. change (SR.ps_regs Pdxe1.ps0) with (map (fun i => (i, nth i Pdxe1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxe1.ps0) with Pdxe1.cells0 in Hcells. unfold Pdxe1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxe1.regs0 Pdxe1.regs_out0 80 KS_dxe1 KS_dxe1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxe1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pdxe1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxe1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxe1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxe1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pdxe1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pdxe2 := LibSegZ_dxe2.
Definition KS_dxe2 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxe2.regs0 Pdxe2.regs_out0).
Lemma KS_dxe2_ok : BG.kept_ok 80 Pdxe2.regs0 Pdxe2.regs_out0 KS_dxe2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxe2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 61%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 27) = Z_to_bv 64 (V 33%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 200) 0 ->
  1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) ->
  0 <= (V 69%nat) <= 255 -> L5.writable RSEGS M (V 35%nat) 32 -> 0 <= (V 61%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 35%nat) + 0) <= i < ((V 35%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21e70 M) (st fx' R' 0x21010 M')
        /\ (forall x, In x KS_dxe2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 138928
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 168)
        /\ L5.u8_at RSEGS M' (V 35%nat) (Z.lor (Z.land (V 69%nat) 253) ((2 * (V 61%nat)) mod 2 ^ 64))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV61l HV61r] [HV69l HV69r] G2 G8 G9 G27 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 [K8l K8r] K9 [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 61%nat => (V 61%nat) | 69%nat => (V 69%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E Pdxe2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxe2.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxe2.kn0).
  { unfold know_ok, Pdxe2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | byte_tac ltac:(clear; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r) | clear - HV35l HV35r K4l K4r K6; lia | clear - HV35l HV35r K4l K4r K6; lia | byte_tac ltac:(clear - HV69l HV69r K8l K8r; lia) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K4l K4r K6; lia | clear - HV35l HV35r K4l K4r K6; lia | clear - HV35l HV35r K4l K4r K6; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (Pdxe2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxe2.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pdxe2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K4l K4r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K4l K4r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxe2.ps0) with 0x21010 in Hms. change (SR.ps_regs Pdxe2.ps0) with (map (fun i => (i, nth i Pdxe2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxe2.ps0) with Pdxe2.cells0 in Hcells. unfold Pdxe2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxe2.regs0 Pdxe2.regs_out0 80 KS_dxe2 KS_dxe2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxe2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pdxe2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxe2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxe2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxe2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pdxe2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K4l K4r K6) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV61l HV61r K10l K10r HV69l HV69r K8l K8r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pdxe3 := LibSegZ_dxe3.
Definition KS_dxe3 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxe3.regs0 Pdxe3.regs_out0).
Lemma KS_dxe3_ok : BG.kept_ok 80 Pdxe3.regs0 Pdxe3.regs_out0 KS_dxe3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxe3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 26) = Z_to_bv 64 (V 62%nat) -> getr R (reg 27) = Z_to_bv 64 (V 33%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (((V 2%nat) - 304) + 304 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 33%nat) (V 38%nat) -> 0 <= (V 38%nat) <= 255 -> L5.writable RSEGS M (V 33%nat) 32 ->
  0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21eb0 M) (st fx' R' 0x222d0 M')
        /\ (forall x, In x KS_dxe3 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (Z.land (V 38%nat) 253) (V 62%nat))
        /\ L5.u8_at RSEGS M' (V 33%nat) (Z.lor (Z.land (V 38%nat) 253) (V 62%nat))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV38l HV38r] [HV62l HV62r] G2 G26 G27 [K0l K0r] K1 [K2l K2r] K3 K4 K5 [K6l K6r] K7 [K8l K8r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 38%nat => (V 38%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E Pdxe3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxe3.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxe3.kn0).
  { unfold know_ok, Pdxe3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K2l K2r K4) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K2l K2r K4) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K2l K2r K4) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K2l K2r K4) | evalEk ZA ltac:(clear - HV38l HV38r K6l K6r) | clear - HV33l HV33r K2l K2r K4; lia | clear - HV33l HV33r K2l K2r K4; lia | byte_tac ltac:(clear - HV38l HV38r K6l K6r; lia) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K2l K2r K4) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K2l K2r K4; lia | clear - HV33l HV33r K2l K2r K4; lia | clear - HV33l HV33r K2l K2r K4; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  destruct (Pdxe3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxe3.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pdxe3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K2l K2r K4) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K2l K2r K4 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxe3.ps0) with 0x222d0 in Hms. change (SR.ps_regs Pdxe3.ps0) with (map (fun i => (i, nth i Pdxe3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxe3.ps0) with Pdxe3.cells0 in Hcells. unfold Pdxe3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxe3.regs0 Pdxe3.regs_out0 80 KS_dxe3 KS_dxe3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxe3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxe3.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K2l K2r K4) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV38l HV38r K6l K6r HV62l HV62r K8l K8r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pdxh1 := LibSegZ_dxh1.
Definition KS_dxh1 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxh1.regs0 Pdxh1.regs_out0).
Lemma KS_dxh1_ok : BG.kept_ok 80 Pdxh1.regs0 Pdxh1.regs_out0 KS_dxh1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxh1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 61%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (((V 2%nat) - 304) + 304 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u64_at RSEGS M ((V 33%nat) + 8) 2 -> 0 <= (V 61%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21f9c M) (st fx' R' 0x210bc M')
        /\ (forall x, In x KS_dxh1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139184
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 2
        /\ getr R' (reg 20) = Z_to_bv 64 (V 61%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV61l HV61r] G2 G8 G9 G18 [K0l K0r] K1 [K2l K2r] K3 K4 K5 [K6l K6r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 61%nat => (V 61%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 62%nat. }
  assert (HR: regs_ok E Pdxh1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxh1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxh1.kn0).
  { unfold know_ok, Pdxh1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K2l K2r K4) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K2l K2r K4) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K2l K2r K4) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K2l K2r K4) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K2l K2r K4; lia | clear - HV33l HV33r K2l K2r K4; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  destruct (Pdxh1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxh1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pdxh1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxh1.ps0) with 0x210bc in Hms. change (SR.ps_regs Pdxh1.ps0) with (map (fun i => (i, nth i Pdxh1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxh1.ps0) with Pdxh1.cells0 in Hcells. unfold Pdxh1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxh1.regs0 Pdxh1.regs_out0 80 KS_dxh1 KS_dxh1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxh1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pdxh1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxh1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxh1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxh1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pdxh1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxh1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pdxh1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pdxh1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pdxh1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pdxh2 := LibSegZ_dxh2.
Definition KS_dxh2 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxh2.regs0 Pdxh2.regs_out0).
Lemma KS_dxh2_ok : BG.kept_ok 80 Pdxh2.regs0 Pdxh2.regs_out0 KS_dxh2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxh2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 2 -> getr R (reg 19) = Z_to_bv 64 (V 63%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 24) = Z_to_bv 64 ((V 35%nat) + 16) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (((V 2%nat) - 304) + 304 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 -> Z.testbit (V 69%nat) 0 = false ->
  L5.writable RSEGS M ((V 35%nat) + 16) 16 -> 1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 304)) ->
  ((V 33%nat) + 32 <= (V 35%nat) \/ (V 35%nat) + 32 <= (V 33%nat)) -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 70%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 71%nat) -> 0 <= (V 70%nat) <= 18446744073709551615 ->
  0 <= (V 71%nat) <= 18446744073709551615 -> 1 <= (V 63%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 35%nat) + 16) <= bv_unsigned a < ((V 35%nat) + 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 35%nat) + 16) <= i < ((V 35%nat) + 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21fb0 M) (st fx' R' 0x215d0 M')
        /\ (forall x, In x KS_dxh2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139316
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 18) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV63l HV63r] [HV69l HV69r] [HV70l HV70r] [HV71l HV71r] G2 G9 G18 G19 G23 G24 [K0l K0r] K1 [K2l K2r] K3 K4 K5 [K6l K6r] K7 K8 [K9l K9r] K10 K11 K12 K13 K14 [K15l K15r] [K16l K16r] [K17l K17r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 63%nat => (V 63%nat) | 69%nat => (V 69%nat) | 70%nat => (V 70%nat) | 71%nat => (V 71%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 72%nat. }
  assert (HR: regs_ok E Pdxh2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxh2.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxh2.kn0).
  { unfold know_ok, Pdxh2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4 K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4 K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K2l K2r K4 K12) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K2l K2r K4 K12) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K2l K2r K4 K12) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K2l K2r K4 K12) | evalEk ZA ltac:(clear - HV69l HV69r K6l K6r K7) | clear - HV35l HV35r K2l K2r K4 K12; lia | clear - HV35l HV35r K2l K2r K4 K12; lia | byte_tac ltac:(clear - HV69l HV69r K6l K6r K7; lia) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K6l K6r K7) | clear; lia | rewrite (L5K.land1_bit0_false (V 69%nat) ltac:(clear - HV69l HV69r K6l K6r K7; lia) K7); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K2l K2r K4 K12) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K2l K2r K4 K12; lia | clear - HV35l HV35r K2l K2r K4 K12; lia | clear - HV35l HV35r K2l K2r K4 K12; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K9l K9r K11 K12) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K9l K9r K11 K12) | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K9l K9r K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K9l K9r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K2l K2r K4 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K9l K9r K11 K12) | evalEk ZA ltac:(clear - HV70l HV70r K15l K15r) | clear - HV33l HV33r K9l K9r K11 K12; lia | clear - HV33l HV33r K9l K9r K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K9l K9r K11 K12) | evalEk ZA ltac:(clear - HV71l HV71r K16l K16r) | clear - HV33l HV33r K9l K9r K11 K12; lia | clear - HV33l HV33r K9l K9r K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  destruct (Pdxh2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxh2.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 35%nat) + 16) <= bv_unsigned a < ((V 35%nat) + 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pdxh2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K2l K2r K4 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K2l K2r K4 K12 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxh2.ps0) with 0x215d0 in Hms. change (SR.ps_regs Pdxh2.ps0) with (map (fun i => (i, nth i Pdxh2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxh2.ps0) with Pdxh2.cells0 in Hcells. unfold Pdxh2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxh2.regs0 Pdxh2.regs_out0 80 KS_dxh2 KS_dxh2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxh2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pdxh2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxh2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxh2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxh2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pdxh2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pdxh2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pdxh2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pdxh3 := LibSegZ_dxh3.
Definition KS_dxh3 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxh3.regs0 Pdxh3.regs_out0).
Lemma KS_dxh3_ok : BG.kept_ok 80 Pdxh3.regs0 Pdxh3.regs_out0 KS_dxh3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxh3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 72%nat) -> getr R (reg 27) = Z_to_bv 64 (V 33%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> 0 <= (V 72%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 200) <= bv_unsigned a < ((V 2%nat) - 200) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 200) <= i < ((V 2%nat) - 200) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22034 M) (st fx' R' 0x21010 M')
        /\ (forall x, In x KS_dxh3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139348
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 200)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (if 0 <? (V 72%nat) then 1 else 0)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 200) 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV72l HV72r] G2 G8 G27 [K0l K0r] K1 K2 [K3l K3r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 72%nat => (V 72%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E Pdxh3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxh3.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxh3.kn0).
  { unfold know_ok, Pdxh3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  destruct (Pdxh3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxh3.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 200) <= bv_unsigned a < ((V 2%nat) - 200) + 32) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pdxh3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxh3.ps0) with 0x21010 in Hms. change (SR.ps_regs Pdxh3.ps0) with (map (fun i => (i, nth i Pdxh3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxh3.ps0) with Pdxh3.cells0 in Hcells. unfold Pdxh3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxh3.regs0 Pdxh3.regs_out0 80 KS_dxh3 KS_dxh3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxh3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pdxh3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxh3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxh3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxh3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pdxh3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV72l HV72r K3l K3r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pdxh4 := LibSegZ_dxh4.
Definition KS_dxh4 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxh4.regs0 Pdxh4.regs_out0).
Lemma KS_dxh4_ok : BG.kept_ok 80 Pdxh4.regs0 Pdxh4.regs_out0 KS_dxh4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxh4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 (V 61%nat) -> getr R (reg 26) = Z_to_bv 64 (V 62%nat) -> getr R (reg 27) = Z_to_bv 64 (V 33%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 200) 0 ->
  1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) ->
  0 <= (V 69%nat) <= 255 -> L5.writable RSEGS M (V 35%nat) 32 -> 1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (((V 2%nat) - 304) + 304 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 33%nat) (V 38%nat) -> 0 <= (V 38%nat) <= 255 -> L5.writable RSEGS M (V 33%nat) 32 ->
  ((V 33%nat) + 32 <= (V 35%nat) \/ (V 35%nat) + 32 <= (V 33%nat)) -> 0 <= (V 61%nat) <= 1 -> 0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 35%nat) + 0) <= i < ((V 35%nat) + 0) + 1) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22054 M) (st fx' R' 0x222d0 M')
        /\ (forall x, In x KS_dxh4 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (Z.land (V 38%nat) 253) (V 62%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (2 * (V 61%nat))
        /\ L5.u8_at RSEGS M' (V 33%nat) (Z.lor (Z.land (V 38%nat) 253) (V 62%nat))
        /\ L5.u8_at RSEGS M' (V 35%nat) (Z.lor (Z.land (V 69%nat) 253) ((2 * (V 61%nat)) mod 2 ^ 64))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV38l HV38r] [HV61l HV61r] [HV62l HV62r] [HV69l HV69r] G2 G9 G20 G26 G27 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 [K8l K8r] K9 [K10l K10r] K11 K12 K13 [K14l K14r] K15 K16 [K17l K17r] [K18l K18r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 38%nat => (V 38%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 69%nat => (V 69%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E Pdxh4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxh4.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxh4.kn0).
  { unfold know_ok, Pdxh4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | byte_tac ltac:(clear; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6 K16) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6 K16) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6 K16) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r) | clear - HV35l HV35r K4l K4r K6 K16; lia | clear - HV35l HV35r K4l K4r K6 K16; lia | byte_tac ltac:(clear - HV69l HV69r K8l K8r; lia) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6 K16) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K4l K4r K6 K16; lia | clear - HV35l HV35r K4l K4r K6 K16; lia | clear - HV35l HV35r K4l K4r K6 K16; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K16) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K16) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K16) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K16) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear - HV33l HV33r K10l K10r K12 K16; lia | clear - HV33l HV33r K10l K10r K12 K16; lia | byte_tac ltac:(clear - HV38l HV38r K14l K14r; lia) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K16) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K10l K10r K12 K16; lia | clear - HV33l HV33r K10l K10r K12 K16; lia | clear - HV33l HV33r K10l K10r K12 K16; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_nil. }
  destruct (Pdxh4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxh4.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pdxh4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K4l K4r K6 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K4l K4r K6 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K12 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K10l K10r K12 K16 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxh4.ps0) with 0x222d0 in Hms. change (SR.ps_regs Pdxh4.ps0) with (map (fun i => (i, nth i Pdxh4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxh4.ps0) with Pdxh4.cells0 in Hcells. unfold Pdxh4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxh4.regs0 Pdxh4.regs_out0 80 KS_dxh4 KS_dxh4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxh4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxh4.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg Pdxh4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pdxh4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K12 K16) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV38l HV38r K14l K14r HV62l HV62r K18l K18r; lia) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K4l K4r K6 K16) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV61l HV61r K17l K17r HV69l HV69r K8l K8r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End L5DIVXP.
