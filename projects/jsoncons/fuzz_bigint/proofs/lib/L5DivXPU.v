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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5DivXPU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVXPU.
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
Module Pdxeu1 := LibSegZ_dxeu1.
Definition KS_dxeu1 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxeu1.regs0 Pdxeu1.regs_out0).
Lemma KS_dxeu1_ok : BG.kept_ok 80 Pdxeu1.regs0 Pdxeu1.regs_out0 KS_dxeu1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxeu1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 216) <= bv_unsigned a < ((V 2%nat) - 216) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 216) <= i < ((V 2%nat) - 216) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x225d0 M) (st fx' R' 0x21428 M')
        /\ (forall x, In x KS_dxeu1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 140788
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 216)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 216) 0).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] G2 G9 [K0l K0r] K1 K2.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E Pdxeu1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxeu1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxeu1.kn0).
  { unfold know_ok, Pdxeu1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  destruct (Pdxeu1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxeu1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 216) <= bv_unsigned a < ((V 2%nat) - 216) + 32) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pdxeu1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxeu1.ps0) with 0x21428 in Hms. change (SR.ps_regs Pdxeu1.ps0) with (map (fun i => (i, nth i Pdxeu1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxeu1.ps0) with Pdxeu1.cells0 in Hcells. unfold Pdxeu1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxeu1.regs0 Pdxeu1.regs_out0 80 KS_dxeu1 KS_dxeu1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxeu1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pdxeu1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxeu1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxeu1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxeu1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pdxeu1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pdxeu2 := LibSegZ_dxeu2.
Definition KS_dxeu2 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxeu2.regs0 Pdxeu2.regs_out0).
Lemma KS_dxeu2_ok : BG.kept_ok 80 Pdxeu2.regs0 Pdxeu2.regs_out0 KS_dxeu2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxeu2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 26) = Z_to_bv 64 (V 61%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 216) 0 ->
  1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) ->
  0 <= (V 69%nat) <= 255 -> L5.writable RSEGS M (V 35%nat) 32 -> 0 <= (V 61%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 35%nat) + 0) <= i < ((V 35%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x225f4 M) (st fx' R' 0x21428 M')
        /\ (forall x, In x KS_dxeu2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 140852
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ L5.u8_at RSEGS M' (V 35%nat) (Z.lor (Z.land (V 69%nat) 253) ((2 * (V 61%nat)) mod 2 ^ 64))).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV36l HV36r] [HV61l HV61r] [HV69l HV69r] G2 G8 G9 G26 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 [K8l K8r] K9 [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 61%nat => (V 61%nat) | 69%nat => (V 69%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E Pdxeu2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxeu2.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxeu2.kn0).
  { unfold know_ok, Pdxeu2.kn0.
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
  destruct (Pdxeu2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxeu2.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pdxeu2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K4l K4r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K4l K4r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxeu2.ps0) with 0x21428 in Hms. change (SR.ps_regs Pdxeu2.ps0) with (map (fun i => (i, nth i Pdxeu2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxeu2.ps0) with Pdxeu2.cells0 in Hcells. unfold Pdxeu2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxeu2.regs0 Pdxeu2.regs_out0 80 KS_dxeu2 KS_dxeu2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxeu2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pdxeu2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxeu2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxeu2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxeu2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pdxeu2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K4l K4r K6) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV61l HV61r K10l K10r HV69l HV69r K8l K8r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pdxeu3 := LibSegZ_dxeu3.
Definition KS_dxeu3 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxeu3.regs0 Pdxeu3.regs_out0).
Lemma KS_dxeu3_ok : BG.kept_ok 80 Pdxeu3.regs0 Pdxeu3.regs_out0 KS_dxeu3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxeu3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (V 62%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> L5.writable RSEGS M (V 36%nat) 32 ->
  0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22634 M) (st fx' R' 0x22b80 M')
        /\ (forall x, In x KS_dxeu3 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (Z.land (V 71%nat) 253) (V 62%nat))
        /\ L5.u8_at RSEGS M' (V 36%nat) (Z.lor (Z.land (V 71%nat) 253) (V 62%nat))).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV62l HV62r] [HV71l HV71r] G2 G8 G25 [K0l K0r] K1 [K2l K2r] K3 K4 K5 [K6l K6r] K7 [K8l K8r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 62%nat => (V 62%nat) | 71%nat => (V 71%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 72%nat. }
  assert (HR: regs_ok E Pdxeu3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxeu3.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxeu3.kn0).
  { unfold know_ok, Pdxeu3.kn0.
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
  destruct (Pdxeu3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxeu3.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pdxeu3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K2l K2r K4) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K2l K2r K4 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxeu3.ps0) with 0x22b80 in Hms. change (SR.ps_regs Pdxeu3.ps0) with (map (fun i => (i, nth i Pdxeu3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxeu3.ps0) with Pdxeu3.cells0 in Hcells. unfold Pdxeu3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxeu3.regs0 Pdxeu3.regs_out0 80 KS_dxeu3 KS_dxeu3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxeu3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxeu3.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K2l K2r K4) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV62l HV62r K8l K8r HV71l HV71r K6l K6r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pdxhu1 := LibSegZ_dxhu1.
Definition KS_dxhu1 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxhu1.regs0 Pdxhu1.regs_out0).
Lemma KS_dxhu1_ok : BG.kept_ok 80 Pdxhu1.regs0 Pdxhu1.regs_out0 KS_dxhu1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxhu1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 11) = Z_to_bv 64 2 ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x2277c M) (st fx' R' 0x214e4 M')
        /\ (forall x, In x KS_dxhu1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 141188
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] G2 G9 G11 [K0l K0r] K1.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E Pdxhu1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxhu1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxhu1.kn0).
  { unfold know_ok, Pdxhu1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_nil. }
  destruct (Pdxhu1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxhu1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pdxhu1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxhu1.ps0) with 0x214e4 in Hms. change (SR.ps_regs Pdxhu1.ps0) with (map (fun i => (i, nth i Pdxhu1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxhu1.ps0) with Pdxhu1.cells0 in Hcells. unfold Pdxhu1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxhu1.regs0 Pdxhu1.regs_out0 80 KS_dxhu1 KS_dxhu1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxhu1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pdxhu1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pdxhu1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxhu1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pdxhu2 := LibSegZ_dxhu2.
Definition KS_dxhu2 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxhu2.regs0 Pdxhu2.regs_out0).
Lemma KS_dxhu2_ok : BG.kept_ok 80 Pdxhu2.regs0 Pdxhu2.regs_out0 KS_dxhu2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxhu2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 (V 63%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 ->
  Z.testbit (V 69%nat) 0 = false -> L5.u64_at RSEGS M ((V 35%nat) + 8) 2 -> L5.writable RSEGS M ((V 35%nat) + 16) 16 -> 1048576 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) -> ((V 33%nat) + 32 <= (V 35%nat) \/ (V 35%nat) + 32 <= (V 33%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 248) ((V 33%nat) + 16) ->
  L5.u64_at RSEGS M ((V 2%nat) - 240) 2 -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 70%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 71%nat) -> 0 <= (V 70%nat) <= 18446744073709551615 ->
  0 <= (V 71%nat) <= 18446744073709551615 -> 1 <= (V 63%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> ~ (((V 35%nat) + 16) <= bv_unsigned a < ((V 35%nat) + 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 16) -> ~ (((V 35%nat) + 16) <= i < ((V 35%nat) + 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22784 M) (st fx' R' 0x21abc M')
        /\ (forall x, In x KS_dxhu2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 142096
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 20) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 22) = Z_to_bv 64 (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 35%nat) + 16)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV63l HV63r] [HV69l HV69r] [HV70l HV70r] [HV71l HV71r] G2 G9 G21 [K0l K0r] K1 K2 [K3l K3r] K4 K5 K6 [K7l K7r] K8 K9 K10 [K11l K11r] K12 K13 K14 K15 K16 K17 K18 [K19l K19r] [K20l K20r] [K21l K21r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 63%nat => (V 63%nat) | 69%nat => (V 69%nat) | 70%nat => (V 70%nat) | 71%nat => (V 71%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 72%nat. }
  assert (HR: regs_ok E Pdxhu2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxhu2.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxhu2.kn0).
  { unfold know_ok, Pdxhu2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K13) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K13) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K13; lia | clear - HV2l HV2r K0l K0r K5 K13; lia | clear - HV2l HV2r K0l K0r K5 K13; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5 K14) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5 K14) | evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K8) | clear - HV35l HV35r K3l K3r K5 K14; lia | clear - HV35l HV35r K3l K3r K5 K14; lia | byte_tac ltac:(clear - HV69l HV69r K7l K7r K8; lia) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_false (V 69%nat) ltac:(clear - HV69l HV69r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5 K14) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K3l K3r K5 K14; lia | clear - HV35l HV35r K3l K3r K5 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5 K14) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K3l K3r K5 K14; lia | clear - HV35l HV35r K3l K3r K5 K14; lia | clear - HV35l HV35r K3l K3r K5 K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13 K14) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13 K14) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K3l K3r K5 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K13) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13 K14) | clear - HV2l HV2r K0l K0r K5 K13; lia | clear - HV2l HV2r K0l K0r K5 K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K13; lia | clear - HV2l HV2r K0l K0r K5 K13; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13 K14) | evalEk ZA ltac:(clear - HV70l HV70r K19l K19r) | clear - HV33l HV33r K11l K11r K13 K14; lia | clear - HV33l HV33r K11l K11r K13 K14; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13 K14) | evalEk ZA ltac:(clear - HV71l HV71r K20l K20r) | clear - HV33l HV33r K11l K11r K13 K14; lia | clear - HV33l HV33r K11l K11r K13 K14; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  destruct (Pdxhu2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxhu2.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> ~ (((V 35%nat) + 16) <= bv_unsigned a < ((V 35%nat) + 16) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pdxhu2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K13 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K3l K3r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K3l K3r K5 K14 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxhu2.ps0) with 0x21abc in Hms. change (SR.ps_regs Pdxhu2.ps0) with (map (fun i => (i, nth i Pdxhu2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxhu2.ps0) with Pdxhu2.cells0 in Hcells. unfold Pdxhu2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxhu2.regs0 Pdxhu2.regs_out0 80 KS_dxhu2 KS_dxhu2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxhu2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pdxhu2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxhu2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxhu2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxhu2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pdxhu2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxhu2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pdxhu2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxhu2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pdxhu2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxhu2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pdxhu2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K13) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K13) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K3l K3r K5 K14) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pdxhu3 := LibSegZ_dxhu3.
Definition KS_dxhu3 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxhu3.regs0 Pdxhu3.regs_out0).
Lemma KS_dxhu3_ok : BG.kept_ok 80 Pdxhu3.regs0 Pdxhu3.regs_out0 KS_dxhu3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxhu3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 (V 72%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> 0 <= (V 72%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 216) <= bv_unsigned a < ((V 2%nat) - 216) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 216) <= i < ((V 2%nat) - 216) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22b10 M) (st fx' R' 0x21428 M')
        /\ (forall x, In x KS_dxhu3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 142140
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 216)
        /\ getr R' (reg 12) = Z_to_bv 64 18446744073709551608
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (if 0 <? (V 72%nat) then 1 else 0)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 216) 0).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV72l HV72r] G2 G8 G19 [K0l K0r] K1 K2 [K3l K3r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 72%nat => (V 72%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E Pdxhu3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxhu3.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxhu3.kn0).
  { unfold know_ok, Pdxhu3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  destruct (Pdxhu3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxhu3.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 216) <= bv_unsigned a < ((V 2%nat) - 216) + 32) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pdxhu3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxhu3.ps0) with 0x21428 in Hms. change (SR.ps_regs Pdxhu3.ps0) with (map (fun i => (i, nth i Pdxhu3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxhu3.ps0) with Pdxhu3.cells0 in Hcells. unfold Pdxhu3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxhu3.regs0 Pdxhu3.regs_out0 80 KS_dxhu3 KS_dxhu3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxhu3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pdxhu3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxhu3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxhu3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxhu3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pdxhu3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pdxhu3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pdxhu3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV72l HV72r K3l K3r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pdxhu4 := LibSegZ_dxhu4.
Definition KS_dxhu4 : list nat := Eval vm_compute in (BG.kept_list 80 Pdxhu4.regs0 Pdxhu4.regs_out0).
Lemma KS_dxhu4_ok : BG.kept_ok 80 Pdxhu4.regs0 Pdxhu4.regs_out0 KS_dxhu4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dxhu4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 25) = Z_to_bv 64 (V 62%nat) -> getr R (reg 26) = Z_to_bv 64 (V 61%nat) ->
  1048928 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.u8_at RSEGS M ((V 2%nat) - 216) 0 ->
  1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 -> (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) ->
  0 <= (V 69%nat) <= 255 -> L5.writable RSEGS M (V 35%nat) 32 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M (V 36%nat) (V 38%nat) -> 0 <= (V 38%nat) <= 255 -> L5.writable RSEGS M (V 36%nat) 32 ->
  ((V 36%nat) + 32 <= (V 35%nat) \/ (V 35%nat) + 32 <= (V 36%nat)) -> 0 <= (V 61%nat) <= 1 -> 0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 35%nat) + 0) <= i < ((V 35%nat) + 0) + 1) -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22b3c M) (st fx' R' 0x22b80 M')
        /\ (forall x, In x KS_dxhu4 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (Z.land (V 38%nat) 253) (V 62%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (2 * (V 61%nat))
        /\ L5.u8_at RSEGS M' (V 36%nat) (Z.lor (Z.land (V 38%nat) 253) (V 62%nat))
        /\ L5.u8_at RSEGS M' (V 35%nat) (Z.lor (Z.land (V 69%nat) 253) ((2 * (V 61%nat)) mod 2 ^ 64))).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV36l HV36r] [HV38l HV38r] [HV61l HV61r] [HV62l HV62r] [HV69l HV69r] G2 G8 G9 G25 G26 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 [K8l K8r] K9 [K10l K10r] K11 K12 K13 [K14l K14r] K15 K16 [K17l K17r] [K18l K18r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 38%nat => (V 38%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 69%nat => (V 69%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E Pdxhu4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pdxhu4.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pdxhu4.kn0).
  { unfold know_ok, Pdxhu4.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K16) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K16) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K16) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K16) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear - HV36l HV36r K10l K10r K12 K16; lia | clear - HV36l HV36r K10l K10r K12 K16; lia | byte_tac ltac:(clear - HV38l HV38r K14l K14r; lia) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K10l K10r K12 K16; lia | clear - HV36l HV36r K10l K10r K12 K16; lia | clear - HV36l HV36r K10l K10r K12 K16; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K12 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_nil. }
  destruct (Pdxhu4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pdxhu4.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pdxhu4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K4l K4r K6 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K4l K4r K6 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K10l K10r K12 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K10l K10r K12 K16 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pdxhu4.ps0) with 0x22b80 in Hms. change (SR.ps_regs Pdxhu4.ps0) with (map (fun i => (i, nth i Pdxhu4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pdxhu4.ps0) with Pdxhu4.cells0 in Hcells. unfold Pdxhu4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pdxhu4.regs0 Pdxhu4.regs_out0 80 KS_dxhu4 KS_dxhu4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pdxhu4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pdxhu4.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg Pdxhu4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pdxhu4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K10l K10r K12 K16) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV38l HV38r K14l K14r HV62l HV62r K18l K18r; lia) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K4l K4r K6 K16) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV61l HV61r K17l K17r HV69l HV69r K8l K8r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End L5DIVXPU.
