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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5DivNP.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVNP.
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
Module Pd5e1 := LibSegZ_d5e1.
Definition KS_d5e1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5e1.regs0 Pd5e1.regs_out0).
Lemma KS_d5e1_ok : BG.kept_ok 80 Pd5e1.regs0 Pd5e1.regs_out0 KS_d5e1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5e1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 36%nat) -> getr R (reg 14) = Z_to_bv 64 (V 37%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 304) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 304) <= i < ((V 2%nat) - 304) + 304) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21d80 M) (st fx' R' 0x22848 M')
        /\ (forall x, In x KS_d5e1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 138708
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 304)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 168)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 36%nat)
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
  assert (HR: regs_ok E Pd5e1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5e1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5e1.kn0).
  { unfold know_ok, Pd5e1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  destruct (Pd5e1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5e1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 304) <= bv_unsigned a < ((V 2%nat) - 304) + 304) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5e1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5e1.ps0) with 0x22848 in Hms. change (SR.ps_regs Pd5e1.ps0) with (map (fun i => (i, nth i Pd5e1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5e1.ps0) with Pd5e1.cells0 in Hcells. unfold Pd5e1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5e1.regs0 Pd5e1.regs_out0 80 KS_d5e1 KS_d5e1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5e1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pd5e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pd5e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pd5e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e1.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pd5e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
Module Pd5e2n := LibSegZ_d5e2n.
Definition KS_d5e2n : list nat := Eval vm_compute in (BG.kept_list 80 Pd5e2n.regs0 Pd5e2n.regs_out0).
Lemma KS_d5e2n_ok : BG.kept_ok 80 Pd5e2n.regs0 Pd5e2n.regs_out0 KS_d5e2n = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5e2n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 (V 36%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) ->
  L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 42%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  1 <= (V 42%nat) <= 1 -> 1048576 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 304)) ->
  L5.u8_at RSEGS M (V 33%nat) (V 38%nat) -> 0 <= (V 38%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21dd4 M) (st fx' R' 0x22848 M')
        /\ (forall x, In x KS_d5e2n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 138760
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 168)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 200)
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 38%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV41l HV41r] [HV42l HV42r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] [HV55l HV55r] [HV56l HV56r] [HV57l HV57r] [HV58l HV58r] [HV59l HV59r] [HV60l HV60r] G2 G9 G18 G23 G27 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 [K18l K18r] K19 [K20l K20r] [K21l K21r] K22 K23 K24 [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | 55%nat => Z_to_bv 64 (V 55%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | 55%nat => (V 55%nat) | 56%nat => (V 56%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | 59%nat => (V 59%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E Pd5e2n.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5e2n.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5e2n.kn0).
  { unfold know_ok, Pd5e2n.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV41l HV41r K18l K18r K19) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | byte_tac ltac:(clear - HV41l HV41r K18l K18r K19; lia) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear - HV42l HV42r K20l K20r) | clear - HV2l HV2r K0l K0r K23; lia | clear - HV2l HV2r K0l K0r K23; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K18l K18r K19) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K18l K18r K19) | clear; lia | rewrite (L5K.land1_bit0_false (V 41%nat) ltac:(clear - HV41l HV41r K18l K18r K19; lia) K19); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K21l K21r K23) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K21l K21r K23) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K21l K21r K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K21l K21r K23) | evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | clear - HV33l HV33r K21l K21r K23; lia | clear - HV33l HV33r K21l K21r K23; lia | byte_tac ltac:(clear - HV38l HV38r K25l K25r; lia) | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (Pd5e2n.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5e2n.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5e2n.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5e2n.ps0) with 0x22848 in Hms. change (SR.ps_regs Pd5e2n.ps0) with (map (fun i => (i, nth i Pd5e2n.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5e2n.ps0) with Pd5e2n.cells0 in Hcells. unfold Pd5e2n.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5e2n.regs0 Pd5e2n.regs_out0 80 KS_d5e2n KS_d5e2n_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5e2n.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5e2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e2n.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5e2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e2n.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5e2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e2n.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5e2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e2n.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5e2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e2n.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5e2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e2n.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pd5e2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e2n.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd5e2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5e2n.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5e2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5e3 := LibSegZ_d5e3.
Definition KS_d5e3 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5e3.regs0 Pd5e3.regs_out0).
Lemma KS_d5e3_ok : BG.kept_ok 80 Pd5e3.regs0 Pd5e3.regs_out0 KS_d5e3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5e3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 41%nat) -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 168) (V 44%nat) ->
  L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) -> 0 <= (V 44%nat) <= 255 -> 0 <= (V 41%nat) <= 255 -> 0 <= (V 38%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 168) <= bv_unsigned a < ((V 2%nat) - 168) + 1) -> ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 168) <= i < ((V 2%nat) - 168) + 1) -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21e08 M) (st fx' R' 0x21a7c M')
        /\ (forall x, In x KS_d5e3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 138812
        /\ bv_unsigned (getr R' (reg 8)) = ((Z.lxor (Z.land (V 41%nat) 2) (Z.land (V 38%nat) 2)) / 2)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 168)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ bv_unsigned (getr R' (reg 26)) = (Z.land (V 38%nat) 2)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 136) (Z.land (V 41%nat) 253)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 168) (Z.land (V 44%nat) 253)).
Proof.
  intros [HV2l HV2r] [HV38l HV38r] [HV41l HV41r] [HV44l HV44r] G2 G8 G22 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] [K7l K7r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 38%nat => (V 38%nat) | 41%nat => (V 41%nat) | 44%nat => (V 44%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E Pd5e3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5e3.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5e3.kn0).
  { unfold know_ok, Pd5e3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV44l HV44r K5l K5r; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K6l K6r; lia) | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  destruct (Pd5e3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5e3.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 168) <= bv_unsigned a < ((V 2%nat) - 168) + 1) -> ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd5e3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5e3.ps0) with 0x21a7c in Hms. change (SR.ps_regs Pd5e3.ps0) with (map (fun i => (i, nth i Pd5e3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5e3.ps0) with Pd5e3.cells0 in Hcells. unfold Pd5e3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5e3.regs0 Pd5e3.regs_out0 80 KS_d5e3 KS_d5e3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5e3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5e3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5e3.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg Pd5e3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5e3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5e3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e3.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5e3.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV41l HV41r K6l K6r; lia) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV44l HV44r K5l K5r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5e4n := LibSegZ_d5e4n.
Definition KS_d5e4n : list nat := Eval vm_compute in (BG.kept_list 80 Pd5e4n.regs0 Pd5e4n.regs_out0).
Lemma KS_d5e4n_ok : BG.kept_ok 80 Pd5e4n.regs0 Pd5e4n.regs_out0 KS_d5e4n = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5e4n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 42%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 168) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 160) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 63%nat) -> 0 <= (V 47%nat) <= 1 ->
  0 <= (V 44%nat) <= 255 -> Z.testbit (V 44%nat) 0 = true -> 2 <= (V 45%nat) <= 300 -> 1 <= (V 42%nat) <= 1 ->
  4294967296 <= (V 63%nat) <= 18446744073709551615 -> srl_range (V 63%nat) 4294967296 1 4294967295 -> 0 <= (V 37%nat) <= 1 -> 1048576 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 33%nat) (V 38%nat) -> 0 <= (V 38%nat) <= 255 ->
  Z.testbit (V 38%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 40%nat) -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x21e3c M) (st fx' R' 0x2209c M')
        /\ (forall x, In x KS_d5e4n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 35%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 37%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV37l HV37r] [HV38l HV38r] [HV40l HV40r] [HV42l HV42r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV63l HV63r] G2 G9 G10 G18 G19 G21 G23 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r] [K8l K8r] K9 [K10l K10r] [K11l K11r] [K12l K12r] K13 [K14l K14r] [K15l K15r] K16 K17 K18 [K19l K19r] K20 K21 [K22l K22r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 40%nat => (V 40%nat) | 42%nat => (V 42%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 63%nat => (V 63%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 64%nat. }
  assert (HR: regs_ok E Pd5e4n.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5e4n.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5e4n.kn0).
  { unfold know_ok, Pd5e4n.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17; lia | clear - HV2l HV2r K0l K0r K17; lia | clear - HV2l HV2r K0l K0r K17; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17) | evalEk ZA ltac:(clear - HV44l HV44r K8l K8r K9) | clear - HV2l HV2r K0l K0r K17; lia | clear - HV2l HV2r K0l K0r K17; lia | byte_tac ltac:(clear - HV44l HV44r K8l K8r K9; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17) | evalEk ZA ltac:(clear - HV45l HV45r K10l K10r) | clear - HV2l HV2r K0l K0r K17; lia | clear - HV2l HV2r K0l K0r K17; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K17; lia | clear - HV2l HV2r K0l K0r K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17) | evalEk ZA ltac:(clear - HV63l HV63r K12l K12r K13) | clear - HV2l HV2r K0l K0r K17; lia | clear - HV2l HV2r K0l K0r K17; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K8l K8r K9) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV44l HV44r K8l K8r K9) | clear; lia | rewrite (L5K.land1_bit0_true (V 44%nat) ltac:(clear - HV44l HV44r K8l K8r K9; lia) K9); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K12l K12r K13) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K17) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K17) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K17) | evalEk ZA ltac:(clear - HV38l HV38r K19l K19r K20) | clear - HV33l HV33r K15l K15r K17; lia | clear - HV33l HV33r K15l K15r K17; lia | byte_tac ltac:(clear - HV38l HV38r K19l K19r K20; lia) | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K19l K19r K20) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K19l K19r K20) | clear; lia | rewrite (L5K.land1_bit0_true (V 38%nat) ltac:(clear - HV38l HV38r K19l K19r K20; lia) K20); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K17) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV33l HV33r K15l K15r K17; lia | clear - HV33l HV33r K15l K15r K17; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_nil. }
  destruct (Pd5e4n.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5e4n.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5e4n.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5e4n.ps0) with 0x2209c in Hms. change (SR.ps_regs Pd5e4n.ps0) with (map (fun i => (i, nth i Pd5e4n.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5e4n.ps0) with Pd5e4n.cells0 in Hcells. unfold Pd5e4n.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5e4n.regs0 Pd5e4n.regs_out0 80 KS_d5e4n KS_d5e4n_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5e4n.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5e4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e4n.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5e4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e4n.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5e4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e4n.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5e4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5e4n.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd5e4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K14l K14r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g1 := LibSegZ_d5g1.
Definition KS_d5g1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g1.regs0 Pd5g1.regs_out0).
Lemma KS_d5g1_ok : BG.kept_ok 80 Pd5g1.regs0 Pd5g1.regs_out0 KS_d5g1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x2209c M) (st fx' R' 0x22848 M')
        /\ (forall x, In x KS_d5g1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139436
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 200)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 168)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 232)).
Proof.
  intros [HV2l HV2r] G2 [K0l K0r] K1.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pd5g1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g1.kn0).
  { unfold know_ok, Pd5g1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_nil. }
  destruct (Pd5g1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5g1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5g1.ps0) with 0x22848 in Hms. change (SR.ps_regs Pd5g1.ps0) with (map (fun i => (i, nth i Pd5g1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5g1.ps0) with Pd5g1.cells0 in Hcells. unfold Pd5g1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g1.regs0 Pd5g1.regs_out0 80 KS_d5g1 KS_d5g1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5g1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5g1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5g1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5g1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5g1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g2 := LibSegZ_d5g2.
Definition KS_d5g2 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g2.regs0 Pd5g2.regs_out0).
Lemma KS_d5g2_ok : BG.kept_ok 80 Pd5g2.regs0 Pd5g2.regs_out0 KS_d5g2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x220ac M) (st fx' R' 0x22848 M')
        /\ (forall x, In x KS_d5g2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139452
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 232)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 248)).
Proof.
  intros [HV2l HV2r] G2 [K0l K0r] K1.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pd5g2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g2.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g2.kn0).
  { unfold know_ok, Pd5g2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_nil. }
  destruct (Pd5g2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g2.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5g2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5g2.ps0) with 0x22848 in Hms. change (SR.ps_regs Pd5g2.ps0) with (map (fun i => (i, nth i Pd5g2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5g2.ps0) with Pd5g2.cells0 in Hcells. unfold Pd5g2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g2.regs0 Pd5g2.regs_out0 80 KS_d5g2 KS_d5g2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5g2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5g2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5g2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5g2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5g2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g3 := LibSegZ_d5g3.
Definition KS_d5g3 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g3.regs0 Pd5g3.regs_out0).
Lemma KS_d5g3_ok : BG.kept_ok 80 Pd5g3.regs0 Pd5g3.regs_out0 KS_d5g3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 236) <= bv_unsigned a < ((V 2%nat) - 236) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 236) <= i < ((V 2%nat) - 236) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x220bc M) (st fx' R' 0x2246c M')
        /\ (forall x, In x KS_d5g3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139476
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 168)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 236)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 236) 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] G2 G18 [K0l K0r] K1 K2.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 34%nat. }
  assert (HR: regs_ok E Pd5g3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g3.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g3.kn0).
  { unfold know_ok, Pd5g3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  destruct (Pd5g3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g3.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 236) <= bv_unsigned a < ((V 2%nat) - 236) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5g3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5g3.ps0) with 0x2246c in Hms. change (SR.ps_regs Pd5g3.ps0) with (map (fun i => (i, nth i Pd5g3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5g3.ps0) with Pd5g3.cells0 in Hcells. unfold Pd5g3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g3.regs0 Pd5g3.regs_out0 80 KS_d5g3 KS_d5g3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5g3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5g3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5g3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5g3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5g3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u32_of_KWord4a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g4i := LibSegZ_d5g4i.
Definition KS_d5g4i : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g4i.regs0 Pd5g4i.regs_out0).
Lemma KS_d5g4i_ok : BG.kept_ok 80 Pd5g4i.regs0 Pd5g4i.regs_out0 KS_d5g4i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g4i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 (V 64%nat) -> getr R (reg 24) = Z_to_bv 64 (V 68%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 65%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  0 <= (V 67%nat) <= 300 -> 0 <= (V 65%nat) <= 300 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> ~ (((V 2%nat) - 264) <= bv_unsigned a < ((V 2%nat) - 264) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 296) <= i < ((V 2%nat) - 296) + 8) -> ~ (((V 2%nat) - 264) <= i < ((V 2%nat) - 264) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x220d4 M) (st fx' R' 0x210bc M')
        /\ (forall x, In x KS_d5g4i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139520
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 65%nat) - (V 67%nat))
        /\ getr R' (reg 19) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) (V 68%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 64%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV41l HV41r] [HV64l HV64r] [HV65l HV65r] [HV67l HV67r] [HV68l HV68r] G2 G9 G10 G24 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] [K9l K9r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 41%nat => (V 41%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | 67%nat => (V 67%nat) | 68%nat => (V 68%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E Pd5g4i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g4i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g4i.kn0).
  { unfold know_ok, Pd5g4i.kn0.
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
    apply Forall_nil. }
  destruct (Pd5g4i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g4i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> ~ (((V 2%nat) - 264) <= bv_unsigned a < ((V 2%nat) - 264) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pd5g4i.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5g4i.ps0) with 0x210bc in Hms. change (SR.ps_regs Pd5g4i.ps0) with (map (fun i => (i, nth i Pd5g4i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5g4i.ps0) with Pd5g4i.cells0 in Hcells. unfold Pd5g4i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g4i.regs0 Pd5g4i.regs_out0 80 KS_d5g4i KS_d5g4i_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5g4i.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5g4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g4i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g4i.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5g4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g4i.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5g4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g4i.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd5g4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV68l HV68r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV64l HV64r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g5d := LibSegZ_d5g5d.
Definition KS_d5g5d_0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g5d.regs0 Pd5g5d.regs_out0).
Lemma KS_d5g5d_0_ok : BG.kept_ok 80 Pd5g5d.regs0 Pd5g5d.regs_out0 KS_d5g5d_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_d5g5d_1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g5d.regs0 Pd5g5d.regs_out1).
Lemma KS_d5g5d_1_ok : BG.kept_ok 80 Pd5g5d.regs0 Pd5g5d.regs_out1 KS_d5g5d_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g5d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 264) (V 68%nat) ->
  1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) ->
  0 <= (V 69%nat) <= 255 -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 70%nat) -> Z.testbit (V 69%nat) 0 = true -> 0 <= (V 70%nat) <= 300 ->
  L5.u64_at RSEGS M ((V 35%nat) + 24) (V 40%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x22100 M) (st fx' R' 0x58ea4 M')
        /\ (forall x, In x KS_d5g5d_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139564
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (8 * (V 70%nat))
        /\ getr R' (reg 24) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 70%nat)
        /\ 1 <= (V 70%nat) <= 300)
      \/ (msteps RSEGS (st fx R 0x22100 M) (st fx' R' 0x2212c M')
        /\ (forall x, In x KS_d5g5d_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 24) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 70%nat)
        /\ 0 <= (V 70%nat) <= 0)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV40l HV40r] [HV68l HV68r] [HV69l HV69r] [HV70l HV70r] G2 G9 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 [K8l K8r] K9 K10 [K11l K11r] K12.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | 70%nat => (V 70%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 71%nat. }
  assert (HR: regs_ok E Pd5g5d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g5d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g5d.kn0).
  { unfold know_ok, Pd5g5d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K10) | clear - HV35l HV35r K4l K4r K6; lia | clear - HV35l HV35r K4l K4r K6; lia | byte_tac ltac:(clear - HV69l HV69r K8l K8r K10; lia) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K10) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | evalEk ZA ltac:(clear - HV70l HV70r K11l K11r) | clear - HV35l HV35r K4l K4r K6; lia | clear - HV35l HV35r K4l K4r K6; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K10) | clear; lia | rewrite (L5K.land1_bit0_true (V 69%nat) ltac:(clear - HV69l HV69r K8l K8r K10; lia) K10); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K6) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV35l HV35r K4l K4r K6; lia | clear - HV35l HV35r K4l K4r K6; lia | exactA K12]. }
    apply Forall_nil. }
  destruct (Pd5g5d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g5d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5g5d.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc Pd5g5d.ps0) with 0x58ea4 in Hms. change (SR.ps_regs Pd5g5d.ps0) with (map (fun i => (i, nth i Pd5g5d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pd5g5d.ps0) with Pd5g5d.cells0 in Hcells. unfold Pd5g5d.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g5d.regs0 Pd5g5d.regs_out0 80 KS_d5g5d_0 KS_d5g5d_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pd5g5d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5g5d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5g5d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g5d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5g5d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5g5d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5g5d.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5g5d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5g5d.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd5g5d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5g5d.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pd5g5d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV70l HV70r K11l K11r)]. 
  - right.
    change (SR.ps_pc Pd5g5d.ps1) with 0x2212c in Hms. change (SR.ps_regs Pd5g5d.ps1) with (map (fun i => (i, nth i Pd5g5d.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pd5g5d.ps1) with Pd5g5d.cells1 in Hcells. unfold Pd5g5d.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g5d.regs0 Pd5g5d.regs_out1 80 KS_d5g5d_1 KS_d5g5d_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pd5g5d.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g5d.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5g5d.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd5g5d.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pd5g5d.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth Pd5g5d.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV70l HV70r K11l K11r)]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g6 := LibSegZ_d5g6.
Definition KS_d5g6 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g6.regs0 Pd5g6.regs_out0).
Lemma KS_d5g6_ok : BG.kept_ok 80 Pd5g6.regs0 Pd5g6.regs_out0 KS_d5g6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 27) = Z_to_bv 64 (V 36%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x2212c M) (st fx' R' 0x21010 M')
        /\ (forall x, In x KS_d5g6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139576
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 168)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] G2 G27 [K0l K0r] K1.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E Pd5g6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g6.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g6.kn0).
  { unfold know_ok, Pd5g6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_nil. }
  destruct (Pd5g6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g6.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5g6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5g6.ps0) with 0x21010 in Hms. change (SR.ps_regs Pd5g6.ps0) with (map (fun i => (i, nth i Pd5g6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5g6.ps0) with Pd5g6.cells0 in Hcells. unfold Pd5g6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g6.regs0 Pd5g6.regs_out0 80 KS_d5g6 KS_d5g6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5g6.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5g6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5g6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5g6.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g7ni0 := LibSegZ_d5g7ni0.
Definition KS_d5g7ni0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g7ni0.regs0 Pd5g7ni0.regs_out0).
Lemma KS_d5g7ni0_ok : BG.kept_ok 80 Pd5g7ni0.regs0 Pd5g7ni0.regs_out0 KS_d5g7ni0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g7ni0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 61%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 21) = Z_to_bv 64 1 -> getr R (reg 26) = Z_to_bv 64 (V 62%nat) -> getr R (reg 27) = Z_to_bv 64 (V 36%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 74%nat) ->
  0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 304)) ->
  L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = false -> L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 65%nat))) + 8) (V 73%nat) ->
  0 <= (V 73%nat) <= 18446744073709551615 -> (V 73%nat) < (V 74%nat) -> 1 <= (V 65%nat) <= 2 -> 0 <= (V 61%nat) <= 1 ->
  0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 288) <= i < ((V 2%nat) - 288) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22138 M) (st fx' R' 0x221d4 M')
        /\ (forall x, In x KS_d5g7ni0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (V 61%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV71l HV71r] [HV73l HV73r] [HV74l HV74r] G2 G8 G19 G20 G21 G26 G27 [K0l K0r] K1 K2 K3 [K4l K4r] [K5l K5r] K6 K7 K8 [K9l K9r] K10 K11 [K12l K12r] K13 [K14l K14r] [K15l K15r] [K16l K16r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 71%nat => (V 71%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd5g7ni0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g7ni0.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g7ni0.kn0).
  { unfold know_ok, Pd5g7ni0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV74l HV74r K4l K4r K13) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K4l K4r K13) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | evalEk ZA ltac:(clear - HV71l HV71r K9l K9r K10) | clear - HV36l HV36r K5l K5r K7; lia | clear - HV36l HV36r K5l K5r K7; lia | byte_tac ltac:(clear - HV71l HV71r K9l K9r K10; lia) | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K9l K9r K10) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K9l K9r K10) | clear; lia | rewrite (L5K.land1_bit0_false (V 71%nat) ltac:(clear - HV71l HV71r K9l K9r K10; lia) K10); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7 HV65l HV65r K14l K14r) | evalEk ZA ltac:(clear - HV73l HV73r K12l K12r K13) | clear - HV36l HV36r K5l K5r K7 HV65l HV65r K14l K14r; lia | clear - HV36l HV36r K5l K5r K7 HV65l HV65r K14l K14r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K12l K12r K13) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K13; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_nil. }
  destruct (Pd5g7ni0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g7ni0.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5g7ni0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5g7ni0.ps0) with 0x221d4 in Hms. change (SR.ps_regs Pd5g7ni0.ps0) with (map (fun i => (i, nth i Pd5g7ni0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5g7ni0.ps0) with Pd5g7ni0.cells0 in Hcells. unfold Pd5g7ni0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g7ni0.regs0 Pd5g7ni0.regs_out0 80 KS_d5g7ni0 KS_d5g7ni0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5g7ni0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5g7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7ni0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7ni0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5g7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7ni0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5g7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7ni0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5g7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7ni0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5g7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7ni0.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pd5g7ni0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K5l K5r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K16l K16r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K15l K15r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g7ni1 := LibSegZ_d5g7ni1.
Definition KS_d5g7ni1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g7ni1.regs0 Pd5g7ni1.regs_out0).
Lemma KS_d5g7ni1_ok : BG.kept_ok 80 Pd5g7ni1.regs0 Pd5g7ni1.regs_out0 KS_d5g7ni1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g7ni1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 61%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 21) = Z_to_bv 64 1 -> getr R (reg 26) = Z_to_bv 64 (V 62%nat) -> getr R (reg 27) = Z_to_bv 64 (V 36%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 74%nat) ->
  0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 304)) ->
  L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = false -> L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 65%nat))) + 8) (V 73%nat) ->
  0 <= (V 73%nat) <= 18446744073709551615 -> (V 74%nat) <= (V 73%nat) -> 1 <= (V 65%nat) <= 2 -> 0 <= (V 61%nat) <= 1 ->
  0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 288) <= i < ((V 2%nat) - 288) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22138 M) (st fx' R' 0x22180 M')
        /\ (forall x, In x KS_d5g7ni1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (V 61%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV71l HV71r] [HV73l HV73r] [HV74l HV74r] G2 G8 G19 G20 G21 G26 G27 [K0l K0r] K1 K2 K3 [K4l K4r] [K5l K5r] K6 K7 K8 [K9l K9r] K10 K11 [K12l K12r] K13 [K14l K14r] [K15l K15r] [K16l K16r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 71%nat => (V 71%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd5g7ni1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g7ni1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g7ni1.kn0).
  { unfold know_ok, Pd5g7ni1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV74l HV74r K4l K4r K13) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K4l K4r K13) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | evalEk ZA ltac:(clear - HV71l HV71r K9l K9r K10) | clear - HV36l HV36r K5l K5r K7; lia | clear - HV36l HV36r K5l K5r K7; lia | byte_tac ltac:(clear - HV71l HV71r K9l K9r K10; lia) | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K9l K9r K10) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K9l K9r K10) | clear; lia | rewrite (L5K.land1_bit0_false (V 71%nat) ltac:(clear - HV71l HV71r K9l K9r K10; lia) K10); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7 HV65l HV65r K14l K14r) | evalEk ZA ltac:(clear - HV73l HV73r K12l K12r K13) | clear - HV36l HV36r K5l K5r K7 HV65l HV65r K14l K14r; lia | clear - HV36l HV36r K5l K5r K7 HV65l HV65r K14l K14r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K12l K12r K13) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K13; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_nil. }
  destruct (Pd5g7ni1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g7ni1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5g7ni1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5g7ni1.ps0) with 0x22180 in Hms. change (SR.ps_regs Pd5g7ni1.ps0) with (map (fun i => (i, nth i Pd5g7ni1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5g7ni1.ps0) with Pd5g7ni1.cells0 in Hcells. unfold Pd5g7ni1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g7ni1.regs0 Pd5g7ni1.regs_out0 80 KS_d5g7ni1 KS_d5g7ni1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5g7ni1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5g7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7ni1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7ni1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5g7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7ni1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5g7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7ni1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5g7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7ni1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5g7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7ni1.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pd5g7ni1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K5l K5r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K16l K16r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K15l K15r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g7nd0 := LibSegZ_d5g7nd0.
Definition KS_d5g7nd0 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g7nd0.regs0 Pd5g7nd0.regs_out0).
Lemma KS_d5g7nd0_ok : BG.kept_ok 80 Pd5g7nd0.regs0 Pd5g7nd0.regs_out0 KS_d5g7nd0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g7nd0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 61%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 21) = Z_to_bv 64 1 -> getr R (reg 26) = Z_to_bv 64 (V 62%nat) -> getr R (reg 27) = Z_to_bv 64 (V 36%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 74%nat) ->
  0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 304)) ->
  L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 24) (V 72%nat) ->
  4096 <= (V 72%nat) <= 140737488355328 -> aligned (V 72%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 72%nat) \/ (V 72%nat) + 64 <= ((V 2%nat) - 304)) -> L5.u64_at RSEGS M (((8 * (V 65%nat)) + (V 72%nat)) - 8) (V 73%nat) ->
  0 <= (V 73%nat) <= 18446744073709551615 -> (V 73%nat) < (V 74%nat) -> 1 <= (V 65%nat) <= 7 -> 0 <= (V 61%nat) <= 1 ->
  0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 288) <= i < ((V 2%nat) - 288) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22138 M) (st fx' R' 0x221d4 M')
        /\ (forall x, In x KS_d5g7nd0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (V 61%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV71l HV71r] [HV72l HV72r] [HV73l HV73r] [HV74l HV74r] G2 G8 G19 G20 G21 G26 G27 [K0l K0r] K1 K2 K3 [K4l K4r] [K5l K5r] K6 K7 K8 [K9l K9r] K10 K11 [K12l K12r] K13 K14 K15 [K16l K16r] K17 [K18l K18r] [K19l K19r] [K20l K20r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd5g7nd0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g7nd0.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g7nd0.kn0).
  { unfold know_ok, Pd5g7nd0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K14; lia | clear - HV2l HV2r K0l K0r K7 K14; lia | clear - HV2l HV2r K0l K0r K7 K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk ZA ltac:(clear - HV74l HV74r K4l K4r K17) | clear - HV2l HV2r K0l K0r K7 K14; lia | clear - HV2l HV2r K0l K0r K7 K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K4l K4r K17) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | evalEk ZA ltac:(clear - HV71l HV71r K9l K9r K10) | clear - HV36l HV36r K5l K5r K7; lia | clear - HV36l HV36r K5l K5r K7; lia | byte_tac ltac:(clear - HV71l HV71r K9l K9r K10; lia) | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K9l K9r K10) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K9l K9r K10) | clear; lia | rewrite (L5K.land1_bit0_true (V 71%nat) ltac:(clear - HV71l HV71r K9l K9r K10; lia) K10); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | evalEk ZA ltac:(clear - HV72l HV72r K12l K12r K14) | clear - HV36l HV36r K5l K5r K7; lia | clear - HV36l HV36r K5l K5r K7; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV72l HV72r K12l K12r K14) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV72l HV72r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV65l HV65r K18l K18r HV72l HV72r K12l K12r K14) | evalEk ZA ltac:(clear - HV73l HV73r K16l K16r K17) | clear - HV65l HV65r K18l K18r HV72l HV72r K12l K12r K14; lia | clear - HV65l HV65r K18l K18r HV72l HV72r K12l K12r K14; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K16l K16r K17) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K17; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  destruct (Pd5g7nd0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g7nd0.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5g7nd0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5g7nd0.ps0) with 0x221d4 in Hms. change (SR.ps_regs Pd5g7nd0.ps0) with (map (fun i => (i, nth i Pd5g7nd0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5g7nd0.ps0) with Pd5g7nd0.cells0 in Hcells. unfold Pd5g7nd0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g7nd0.regs0 Pd5g7nd0.regs_out0 80 KS_d5g7nd0 KS_d5g7nd0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5g7nd0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5g7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7nd0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7nd0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5g7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7nd0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5g7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7nd0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5g7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7nd0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5g7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7nd0.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pd5g7nd0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K5l K5r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K20l K20r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K19l K19r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g7nd1 := LibSegZ_d5g7nd1.
Definition KS_d5g7nd1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g7nd1.regs0 Pd5g7nd1.regs_out0).
Lemma KS_d5g7nd1_ok : BG.kept_ok 80 Pd5g7nd1.regs0 Pd5g7nd1.regs_out0 KS_d5g7nd1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g7nd1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 61%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 21) = Z_to_bv 64 1 -> getr R (reg 26) = Z_to_bv 64 (V 62%nat) -> getr R (reg 27) = Z_to_bv 64 (V 36%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 74%nat) ->
  0 <= (V 74%nat) <= 18446744073709551615 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 304)) ->
  L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 24) (V 72%nat) ->
  4096 <= (V 72%nat) <= 140737488355328 -> aligned (V 72%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 72%nat) \/ (V 72%nat) + 64 <= ((V 2%nat) - 304)) -> L5.u64_at RSEGS M (((8 * (V 65%nat)) + (V 72%nat)) - 8) (V 73%nat) ->
  0 <= (V 73%nat) <= 18446744073709551615 -> (V 74%nat) <= (V 73%nat) -> 1 <= (V 65%nat) <= 7 -> 0 <= (V 61%nat) <= 1 ->
  0 <= (V 62%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 288) <= i < ((V 2%nat) - 288) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22138 M) (st fx' R' 0x22180 M')
        /\ (forall x, In x KS_d5g7nd1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 65%nat) - 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) (V 62%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (V 61%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV61l HV61r] [HV62l HV62r] [HV65l HV65r] [HV71l HV71r] [HV72l HV72r] [HV73l HV73r] [HV74l HV74r] G2 G8 G19 G20 G21 G26 G27 [K0l K0r] K1 K2 K3 [K4l K4r] [K5l K5r] K6 K7 K8 [K9l K9r] K10 K11 [K12l K12r] K13 K14 K15 [K16l K16r] K17 [K18l K18r] [K19l K19r] [K20l K20r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 65%nat => (V 65%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pd5g7nd1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g7nd1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g7nd1.kn0).
  { unfold know_ok, Pd5g7nd1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K14; lia | clear - HV2l HV2r K0l K0r K7 K14; lia | clear - HV2l HV2r K0l K0r K7 K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk ZA ltac:(clear - HV74l HV74r K4l K4r K17) | clear - HV2l HV2r K0l K0r K7 K14; lia | clear - HV2l HV2r K0l K0r K7 K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K4l K4r K17) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | evalEk ZA ltac:(clear - HV71l HV71r K9l K9r K10) | clear - HV36l HV36r K5l K5r K7; lia | clear - HV36l HV36r K5l K5r K7; lia | byte_tac ltac:(clear - HV71l HV71r K9l K9r K10; lia) | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K9l K9r K10) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K9l K9r K10) | clear; lia | rewrite (L5K.land1_bit0_true (V 71%nat) ltac:(clear - HV71l HV71r K9l K9r K10; lia) K10); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r K7) | evalEk ZA ltac:(clear - HV72l HV72r K12l K12r K14) | clear - HV36l HV36r K5l K5r K7; lia | clear - HV36l HV36r K5l K5r K7; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV72l HV72r K12l K12r K14) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV72l HV72r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV65l HV65r K18l K18r HV72l HV72r K12l K12r K14) | evalEk ZA ltac:(clear - HV73l HV73r K16l K16r K17) | clear - HV65l HV65r K18l K18r HV72l HV72r K12l K12r K14; lia | clear - HV65l HV65r K18l K18r HV72l HV72r K12l K12r K14; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K16l K16r K17) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K17; clear; intro; destruct (Z.ltb_spec0 (V 73%nat) (V 74%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  destruct (Pd5g7nd1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g7nd1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 288) <= bv_unsigned a < ((V 2%nat) - 288) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5g7nd1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5g7nd1.ps0) with 0x22180 in Hms. change (SR.ps_regs Pd5g7nd1.ps0) with (map (fun i => (i, nth i Pd5g7nd1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5g7nd1.ps0) with Pd5g7nd1.cells0 in Hcells. unfold Pd5g7nd1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g7nd1.regs0 Pd5g7nd1.regs_out0 80 KS_d5g7nd1 KS_d5g7nd1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5g7nd1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5g7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7nd1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7nd1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5g7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7nd1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5g7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7nd1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5g7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7nd1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5g7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g7nd1.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pd5g7nd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K5l K5r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk' ZA Hag ltac:(clear - HV62l HV62r K20l K20r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 K14) | evalEk' ZA Hag ltac:(clear - HV61l HV61r K19l K19r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g8 := LibSegZ_d5g8.
Definition KS_d5g8 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g8.regs0 Pd5g8.regs_out0).
Lemma KS_d5g8_ok : BG.kept_ok 80 Pd5g8.regs0 Pd5g8.regs_out0 KS_d5g8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 272) (V 36%nat) ->
  1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u64_at RSEGS M ((V 36%nat) + 8) (V 65%nat) ->
  0 <= (V 65%nat) <= 300 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22180 M) (st fx' R' 0x210bc M')
        /\ (forall x, In x KS_d5g8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139668
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 65%nat) + 1)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 36%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV65l HV65r] G2 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 [K8l K8r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 65%nat => (V 65%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 66%nat. }
  assert (HR: regs_ok E Pd5g8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g8.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g8.kn0).
  { unfold know_ok, Pd5g8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r K6) | evalEk ZA ltac:(clear - HV65l HV65r K8l K8r) | clear - HV36l HV36r K4l K4r K6; lia | clear - HV36l HV36r K4l K4r K6; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  destruct (Pd5g8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g8.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5g8.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5g8.ps0) with 0x210bc in Hms. change (SR.ps_regs Pd5g8.ps0) with (map (fun i => (i, nth i Pd5g8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5g8.ps0) with Pd5g8.cells0 in Hcells. unfold Pd5g8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g8.regs0 Pd5g8.regs_out0 80 KS_d5g8 KS_d5g8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5g8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5g8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5g8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5g8.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5g8.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g9 := LibSegZ_d5g9.
Definition KS_d5g9 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g9.regs0 Pd5g9.regs_out0).
Lemma KS_d5g9_ok : BG.kept_ok 80 Pd5g9.regs0 Pd5g9.regs_out0 KS_d5g9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (V 70%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 1048576 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (((V 2%nat) - 304) + 304 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 36%nat) (V 71%nat) -> 0 <= (V 71%nat) <= 255 -> L5.u64_at RSEGS M ((V 36%nat) + 24) (V 72%nat) ->
  0 <= (V 70%nat) <= 300 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22194 M) (st fx' R' 0x210bc M')
        /\ (forall x, In x KS_d5g9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139688
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 70%nat) + 1)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 71%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV36l HV36r] [HV70l HV70r] [HV71l HV71r] [HV72l HV72r] G2 G9 G23 G25 [K0l K0r] K1 [K2l K2r] K3 K4 K5 [K6l K6r] K7 [K8l K8r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 70%nat => (V 70%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E Pd5g9.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g9.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g9.kn0).
  { unfold know_ok, Pd5g9.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r K4) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r K4) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K4) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K2l K2r K4) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r K4) | evalEk ZA ltac:(clear - HV71l HV71r K6l K6r) | clear - HV36l HV36r K2l K2r K4; lia | clear - HV36l HV36r K2l K2r K4; lia | byte_tac ltac:(clear - HV71l HV71r K6l K6r; lia) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r K4) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV36l HV36r K2l K2r K4; lia | clear - HV36l HV36r K2l K2r K4; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  destruct (Pd5g9.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g9.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5g9.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5g9.ps0) with 0x210bc in Hms. change (SR.ps_regs Pd5g9.ps0) with (map (fun i => (i, nth i Pd5g9.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5g9.ps0) with Pd5g9.cells0 in Hcells. unfold Pd5g9.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g9.regs0 Pd5g9.regs_out0 80 KS_d5g9 KS_d5g9_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5g9.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5g9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g9.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g9.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5g9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g9.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5g9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5g9.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd5g9.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g10i := LibSegZ_d5g10i.
Definition KS_d5g10i : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g10i.regs0 Pd5g10i.regs_out0).
Lemma KS_d5g10i_ok : BG.kept_ok 80 Pd5g10i.regs0 Pd5g10i.regs_out0 KS_d5g10i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g10i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 ((V 36%nat) + 16) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 23) = Z_to_bv 64 (V 72%nat) -> getr R (reg 24) = Z_to_bv 64 (V 71%nat) -> getr R (reg 27) = Z_to_bv 64 (V 79%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 264) (V 68%nat) ->
  0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = false -> 1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (((V 2%nat) - 304) + 304 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 -> Z.testbit (V 69%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 35%nat) + 24) (V 40%nat) -> 1048576 <= (V 79%nat) <= 140737488355328 -> aligned (V 79%nat) 8 -> L5.u64_at RSEGS M (V 79%nat) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x221a8 M) (st fx' R' 0x221d4 M')
        /\ (forall x, In x KS_d5g10i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 16)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 65%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV36l HV36r] [HV40l HV40r] [HV65l HV65r] [HV68l HV68r] [HV69l HV69r] [HV71l HV71r] [HV72l HV72r] [HV74l HV74r] [HV79l HV79r] G2 G8 G9 G19 G23 G24 G27 [K0l K0r] K1 K2 K3 [K4l K4r] K5 [K6l K6r] K7 K8 K9 [K10l K10r] K11 K12 [K13l K13r] K14 K15.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 40%nat => (V 40%nat) | 65%nat => (V 65%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 74%nat => (V 74%nat) | 79%nat => (V 79%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E Pd5g10i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g10i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g10i.kn0).
  { unfold know_ok, Pd5g10i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false (V 71%nat) ltac:(clear - HV71l HV71r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | evalEk ZA ltac:(clear - HV69l HV69r K10l K10r K11) | clear - HV35l HV35r K6l K6r K8; lia | clear - HV35l HV35r K6l K6r K8; lia | byte_tac ltac:(clear - HV69l HV69r K10l K10r K11; lia) | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K10l K10r K11) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K10l K10r K11) | clear; lia | rewrite (L5K.land1_bit0_true (V 69%nat) ltac:(clear - HV69l HV69r K10l K10r K11; lia) K11); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV35l HV35r K6l K6r K8; lia | clear - HV35l HV35r K6l K6r K8; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV79l HV79r K13l K13r) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV79l HV79r K13l K13r) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV79l HV79r K13l K13r; lia | clear - HV79l HV79r K13l K13r; lia | exactA K15]. }
    apply Forall_nil. }
  destruct (Pd5g10i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g10i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5g10i.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5g10i.ps0) with 0x221d4 in Hms. change (SR.ps_regs Pd5g10i.ps0) with (map (fun i => (i, nth i Pd5g10i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5g10i.ps0) with Pd5g10i.cells0 in Hcells. unfold Pd5g10i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g10i.regs0 Pd5g10i.regs_out0 80 KS_d5g10i KS_d5g10i_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5g10i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g10i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g10i.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5g10i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g10i.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd5g10i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5g10i.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5g10i.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5g10d := LibSegZ_d5g10d.
Definition KS_d5g10d : list nat := Eval vm_compute in (BG.kept_list 80 Pd5g10d.regs0 Pd5g10d.regs_out0).
Lemma KS_d5g10d_ok : BG.kept_ok 80 Pd5g10d.regs0 Pd5g10d.regs_out0 KS_d5g10d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5g10d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 65%nat) -> getr R (reg 23) = Z_to_bv 64 (V 72%nat) -> getr R (reg 24) = Z_to_bv 64 (V 71%nat) -> getr R (reg 27) = Z_to_bv 64 (V 79%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 264) (V 68%nat) ->
  0 <= (V 71%nat) <= 255 -> Z.testbit (V 71%nat) 0 = true -> 1048576 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (((V 2%nat) - 304) + 304 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 -> Z.testbit (V 69%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 35%nat) + 24) (V 40%nat) -> 1048576 <= (V 79%nat) <= 140737488355328 -> aligned (V 79%nat) 8 -> L5.u64_at RSEGS M (V 79%nat) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x221a8 M) (st fx' R' 0x221d4 M')
        /\ (forall x, In x KS_d5g10d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 65%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV40l HV40r] [HV65l HV65r] [HV68l HV68r] [HV69l HV69r] [HV71l HV71r] [HV72l HV72r] [HV74l HV74r] [HV79l HV79r] G2 G9 G19 G23 G24 G27 [K0l K0r] K1 K2 K3 [K4l K4r] K5 [K6l K6r] K7 K8 K9 [K10l K10r] K11 K12 [K13l K13r] K14 K15.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 65%nat => (V 65%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 74%nat => (V 74%nat) | 79%nat => (V 79%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E Pd5g10d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5g10d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5g10d.kn0).
  { unfold know_ok, Pd5g10d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV71l HV71r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_true (V 71%nat) ltac:(clear - HV71l HV71r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | evalEk ZA ltac:(clear - HV69l HV69r K10l K10r K11) | clear - HV35l HV35r K6l K6r K8; lia | clear - HV35l HV35r K6l K6r K8; lia | byte_tac ltac:(clear - HV69l HV69r K10l K10r K11; lia) | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K10l K10r K11) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K10l K10r K11) | clear; lia | rewrite (L5K.land1_bit0_true (V 69%nat) ltac:(clear - HV69l HV69r K10l K10r K11; lia) K11); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV35l HV35r K6l K6r K8; lia | clear - HV35l HV35r K6l K6r K8; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV79l HV79r K13l K13r) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV79l HV79r K13l K13r) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV79l HV79r K13l K13r; lia | clear - HV79l HV79r K13l K13r; lia | exactA K15]. }
    apply Forall_nil. }
  destruct (Pd5g10d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5g10d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5g10d.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5g10d.ps0) with 0x221d4 in Hms. change (SR.ps_regs Pd5g10d.ps0) with (map (fun i => (i, nth i Pd5g10d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5g10d.ps0) with Pd5g10d.cells0 in Hcells. unfold Pd5g10d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5g10d.regs0 Pd5g10d.regs_out0 80 KS_d5g10d KS_d5g10d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5g10d.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5g10d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g10d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5g10d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g10d.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5g10d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5g10d.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd5g10d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5g10d.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5g10d.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5l0e := LibSegZ_d5l0e.
Definition KS_d5l0e : list nat := Eval vm_compute in (BG.kept_list 80 Pd5l0e.regs0 Pd5l0e.regs_out0).
Lemma KS_d5l0e_ok : BG.kept_ok 80 Pd5l0e.regs0 Pd5l0e.regs_out0 KS_d5l0e = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5l0e_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 10) = Z_to_bv 64 (V 72%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 22) = Z_to_bv 64 (V 78%nat) -> getr R (reg 24) = Z_to_bv 64 (V 68%nat) -> getr R (reg 26) = Z_to_bv 64 (V 75%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> (V 78%nat) < (V 75%nat) -> 0 <= (V 78%nat) <= 300 ->
  0 <= (V 75%nat) <= 300 -> 1 <= (V 67%nat) <= 301 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x221d4 M) (st fx' R' 0x221f0 M')
        /\ (forall x, In x KS_d5l0e -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 (((-8) * (V 67%nat)) + ((V 68%nat) + (8 * (V 75%nat))))
        /\ getr R' (reg 10) = Z_to_bv 64 (((-8) * (V 67%nat)) + (V 68%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 67%nat))
        /\ getr R' (reg 19) = Z_to_bv 64 ((-8) * (V 67%nat))
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 72%nat) + (8 * (V 75%nat)))).
Proof.
  intros [HV2l HV2r] [HV67l HV67r] [HV68l HV68r] [HV72l HV72r] [HV75l HV75r] [HV78l HV78r] G2 G10 G21 G22 G24 G26 [K0l K0r] K1 K2 [K3l K3r] [K4l K4r] [K5l K5r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 67%nat => (V 67%nat) | 68%nat => (V 68%nat) | 72%nat => (V 72%nat) | 75%nat => (V 75%nat) | 78%nat => (V 78%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 79%nat. }
  assert (HR: regs_ok E Pd5l0e.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5l0e.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5l0e.kn0).
  { unfold know_ok, Pd5l0e.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K2; clear; intro; destruct (Z.ltb_spec0 (V 78%nat) (V 75%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K2 K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K2 K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_nil. }
  destruct (Pd5l0e.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5l0e.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5l0e.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5l0e.ps0) with 0x221f0 in Hms. change (SR.ps_regs Pd5l0e.ps0) with (map (fun i => (i, nth i Pd5l0e.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5l0e.ps0) with Pd5l0e.cells0 in Hcells. unfold Pd5l0e.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5l0e.regs0 Pd5l0e.regs_out0 80 KS_d5l0e KS_d5l0e_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5l0e.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5l0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l0e.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5l0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l0e.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5l0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l0e.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5l0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5l0e.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pd5l0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5l0x := LibSegZ_d5l0x.
Definition KS_d5l0x : list nat := Eval vm_compute in (BG.kept_list 80 Pd5l0x.regs0 Pd5l0x.regs_out0).
Lemma KS_d5l0x_ok : BG.kept_ok 80 Pd5l0x.regs0 Pd5l0x.regs_out0 KS_d5l0x = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5l0x_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 10) = Z_to_bv 64 (V 72%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 22) = Z_to_bv 64 (V 78%nat) -> getr R (reg 24) = Z_to_bv 64 (V 68%nat) -> getr R (reg 26) = Z_to_bv 64 (V 75%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> (V 75%nat) <= (V 78%nat) -> 0 <= (V 78%nat) <= 300 ->
  0 <= (V 75%nat) <= 300 -> 1 <= (V 67%nat) <= 301 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x221d4 M) (st fx' R' 0x2223c M')
        /\ (forall x, In x KS_d5l0x -> getr R' (reg x) = getr R (reg x))).
Proof.
  intros [HV2l HV2r] [HV67l HV67r] [HV68l HV68r] [HV72l HV72r] [HV75l HV75r] [HV78l HV78r] G2 G10 G21 G22 G24 G26 [K0l K0r] K1 K2 [K3l K3r] [K4l K4r] [K5l K5r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 67%nat => (V 67%nat) | 68%nat => (V 68%nat) | 72%nat => (V 72%nat) | 75%nat => (V 75%nat) | 78%nat => (V 78%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 79%nat. }
  assert (HR: regs_ok E Pd5l0x.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5l0x.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5l0x.kn0).
  { unfold know_ok, Pd5l0x.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K2; clear; intro; destruct (Z.ltb_spec0 (V 78%nat) (V 75%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K2 K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K2 K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_nil. }
  destruct (Pd5l0x.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5l0x.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5l0x.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5l0x.ps0) with 0x2223c in Hms. change (SR.ps_regs Pd5l0x.ps0) with (map (fun i => (i, nth i Pd5l0x.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5l0x.ps0) with Pd5l0x.cells0 in Hcells. unfold Pd5l0x.cells0 in Hcells.
  split. { exact Hms. }
  intros j Hj. apply (BG.kept_regs E E' R R' Pd5l0x.regs0 Pd5l0x.regs_out0 80 KS_d5l0x KS_d5l0x_ok HR Hag Hregs j Hj). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5l1 := LibSegZ_d5l1.
Definition KS_d5l1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5l1.regs0 Pd5l1.regs_out0).
Lemma KS_d5l1_ok : BG.kept_ok 80 Pd5l1.regs0 Pd5l1.regs_out0 KS_d5l1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5l1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (V 74%nat) -> getr R (reg 25) = Z_to_bv 64 (V 79%nat) -> getr R (reg 26) = Z_to_bv 64 (V 75%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 4096 <= (V 79%nat) <= 140737488355328 -> aligned (V 79%nat) 8 ->
  L5.u64_at RSEGS M (V 79%nat) (V 73%nat) -> L5.u64_at RSEGS M ((V 79%nat) - 8) (V 76%nat) -> 1 <= (V 75%nat) <= 300 -> 0 <= (V 73%nat) <= 18446744073709551615 ->
  0 <= (V 76%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x221f0 M) (st fx' R' 0x22578 M')
        /\ (forall x, In x KS_d5l1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139788
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 76%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 79%nat) - 8)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 75%nat) - 1)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV73l HV73r] [HV74l HV74r] [HV75l HV75r] [HV76l HV76r] [HV79l HV79r] G2 G18 G23 G25 G26 [K0l K0r] K1 [K2l K2r] K3 K4 K5 [K6l K6r] [K7l K7r] [K8l K8r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | 75%nat => (V 75%nat) | 76%nat => (V 76%nat) | 79%nat => (V 79%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E Pd5l1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5l1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5l1.kn0).
  { unfold know_ok, Pd5l1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV79l HV79r K2l K2r) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV79l HV79r K2l K2r) | evalEk ZA ltac:(clear - HV73l HV73r K7l K7r) | clear - HV79l HV79r K2l K2r; lia | clear - HV79l HV79r K2l K2r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV79l HV79r K2l K2r) | evalEk ZA ltac:(clear - HV76l HV76r K8l K8r) | clear - HV79l HV79r K2l K2r; lia | clear - HV79l HV79r K2l K2r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  destruct (Pd5l1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5l1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5l1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5l1.ps0) with 0x22578 in Hms. change (SR.ps_regs Pd5l1.ps0) with (map (fun i => (i, nth i Pd5l1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5l1.ps0) with Pd5l1.cells0 in Hcells. unfold Pd5l1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5l1.regs0 Pd5l1.regs_out0 80 KS_d5l1 KS_d5l1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5l1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5l1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5l1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5l1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5l1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5l1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd5l1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5l1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5l1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5l2 := LibSegZ_d5l2.
Definition KS_d5l2 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5l2.regs0 Pd5l2.regs_out0).
Lemma KS_d5l2_ok : BG.kept_ok 80 Pd5l2.regs0 Pd5l2.regs_out0 KS_d5l2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5l2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 10) = Z_to_bv 64 (V 76%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 77%nat) -> getr R (reg 20) = Z_to_bv 64 (V 66%nat) -> getr R (reg 21) = Z_to_bv 64 (V 67%nat) -> getr R (reg 25) = Z_to_bv 64 (V 79%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> 0 <= (V 76%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 248) <= bv_unsigned a < ((V 2%nat) - 248) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 248) <= i < ((V 2%nat) - 248) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x2220c M) (st fx' R' 0x22674 M')
        /\ (forall x, In x KS_d5l2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139816
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 77%nat) + (V 79%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 248)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (V 76%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV66l HV66r] [HV67l HV67r] [HV76l HV76r] [HV77l HV77r] [HV79l HV79r] G2 G10 G18 G19 G20 G21 G25 [K0l K0r] K1 K2 [K3l K3r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 76%nat => (V 76%nat) | 77%nat => (V 77%nat) | 79%nat => (V 79%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E Pd5l2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5l2.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5l2.kn0).
  { unfold know_ok, Pd5l2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  destruct (Pd5l2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5l2.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 248) <= bv_unsigned a < ((V 2%nat) - 248) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5l2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5l2.ps0) with 0x22674 in Hms. change (SR.ps_regs Pd5l2.ps0) with (map (fun i => (i, nth i Pd5l2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5l2.ps0) with Pd5l2.cells0 in Hcells. unfold Pd5l2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5l2.regs0 Pd5l2.regs_out0 80 KS_d5l2 KS_d5l2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5l2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5l2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5l2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5l2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pd5l2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pd5l2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pd5l2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV76l HV76r K3l K3r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5l3c := LibSegZ_d5l3c.
Definition KS_d5l3c : list nat := Eval vm_compute in (BG.kept_list 80 Pd5l3c.regs0 Pd5l3c.regs_out0).
Lemma KS_d5l3c_ok : BG.kept_ok 80 Pd5l3c.regs0 Pd5l3c.regs_out0 KS_d5l3c = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5l3c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 79%nat) -> getr R (reg 22) = Z_to_bv 64 (V 78%nat) -> getr R (reg 24) = Z_to_bv 64 (V 72%nat) -> getr R (reg 26) = Z_to_bv 64 (V 75%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 248) (V 76%nat) ->
  4096 <= (V 79%nat) <= 140737488355328 -> aligned (V 79%nat) 8 -> L5.writable RSEGS M (V 79%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 79%nat) \/ (V 79%nat) + 8 <= ((V 2%nat) - 304)) ->
  (V 78%nat) < (V 75%nat) -> 0 <= (V 78%nat) <= 300 -> 0 <= (V 75%nat) <= 300 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 79%nat) + 0) <= bv_unsigned a < ((V 79%nat) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 79%nat) + 0) <= i < ((V 79%nat) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22228 M) (st fx' R' 0x221f0 M')
        /\ (forall x, In x KS_d5l3c -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 79%nat) - 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 76%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 72%nat)
        /\ L5.u64_at RSEGS M' (V 79%nat) (V 76%nat)).
Proof.
  intros [HV2l HV2r] [HV72l HV72r] [HV75l HV75r] [HV76l HV76r] [HV78l HV78r] [HV79l HV79r] G2 G8 G22 G24 G26 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 K8 [K9l K9r] [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 72%nat => (V 72%nat) | 75%nat => (V 75%nat) | 76%nat => (V 76%nat) | 78%nat => (V 78%nat) | 79%nat => (V 79%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E Pd5l3c.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5l3c.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5l3c.kn0).
  { unfold know_ok, Pd5l3c.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV76l HV76r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K4l K4r K7) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV79l HV79r K4l K4r K7) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV79l HV79r K4l K4r K7) | evalEk ZA ltac:(clear) | clear - HV79l HV79r K4l K4r K7; lia | clear - HV79l HV79r K4l K4r K7; lia | clear - HV79l HV79r K4l K4r K7; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV79l HV79r K4l K4r K7) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K8; clear; intro; destruct (Z.ltb_spec0 (V 78%nat) (V 75%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K8 K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K8 K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (Pd5l3c.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5l3c.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 79%nat) + 0) <= bv_unsigned a < ((V 79%nat) + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5l3c.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV79l HV79r K4l K4r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV79l HV79r K4l K4r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5l3c.ps0) with 0x221f0 in Hms. change (SR.ps_regs Pd5l3c.ps0) with (map (fun i => (i, nth i Pd5l3c.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5l3c.ps0) with Pd5l3c.cells0 in Hcells. unfold Pd5l3c.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5l3c.regs0 Pd5l3c.regs_out0 80 KS_d5l3c KS_d5l3c_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5l3c.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5l3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l3c.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5l3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l3c.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pd5l3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV79l HV79r K4l K4r K7) | evalEk' ZA Hag ltac:(clear - HV76l HV76r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5l3x := LibSegZ_d5l3x.
Definition KS_d5l3x : list nat := Eval vm_compute in (BG.kept_list 80 Pd5l3x.regs0 Pd5l3x.regs_out0).
Lemma KS_d5l3x_ok : BG.kept_ok 80 Pd5l3x.regs0 Pd5l3x.regs_out0 KS_d5l3x = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5l3x_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 8) = Z_to_bv 64 (V 79%nat) -> getr R (reg 22) = Z_to_bv 64 (V 78%nat) -> getr R (reg 24) = Z_to_bv 64 (V 72%nat) -> getr R (reg 26) = Z_to_bv 64 (V 75%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 248) (V 76%nat) ->
  4096 <= (V 79%nat) <= 140737488355328 -> aligned (V 79%nat) 8 -> L5.writable RSEGS M (V 79%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 79%nat) \/ (V 79%nat) + 8 <= ((V 2%nat) - 304)) ->
  (V 75%nat) <= (V 78%nat) -> 0 <= (V 78%nat) <= 300 -> 0 <= (V 75%nat) <= 300 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 79%nat) + 0) <= bv_unsigned a < ((V 79%nat) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 79%nat) + 0) <= i < ((V 79%nat) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22228 M) (st fx' R' 0x2223c M')
        /\ (forall x, In x KS_d5l3x -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 79%nat) - 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 76%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 72%nat)
        /\ L5.u64_at RSEGS M' (V 79%nat) (V 76%nat)).
Proof.
  intros [HV2l HV2r] [HV72l HV72r] [HV75l HV75r] [HV76l HV76r] [HV78l HV78r] [HV79l HV79r] G2 G8 G22 G24 G26 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 K8 [K9l K9r] [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 72%nat => (V 72%nat) | 75%nat => (V 75%nat) | 76%nat => (V 76%nat) | 78%nat => (V 78%nat) | 79%nat => (V 79%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E Pd5l3x.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5l3x.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5l3x.kn0).
  { unfold know_ok, Pd5l3x.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV76l HV76r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K4l K4r K7) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV79l HV79r K4l K4r K7) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV79l HV79r K4l K4r K7) | evalEk ZA ltac:(clear) | clear - HV79l HV79r K4l K4r K7; lia | clear - HV79l HV79r K4l K4r K7; lia | clear - HV79l HV79r K4l K4r K7; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV79l HV79r K4l K4r K7) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K8; clear; intro; destruct (Z.ltb_spec0 (V 78%nat) (V 75%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K8 K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K8 K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (Pd5l3x.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5l3x.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 79%nat) + 0) <= bv_unsigned a < ((V 79%nat) + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5l3x.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV79l HV79r K4l K4r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV79l HV79r K4l K4r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5l3x.ps0) with 0x2223c in Hms. change (SR.ps_regs Pd5l3x.ps0) with (map (fun i => (i, nth i Pd5l3x.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5l3x.ps0) with Pd5l3x.cells0 in Hcells. unfold Pd5l3x.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5l3x.regs0 Pd5l3x.regs_out0 80 KS_d5l3x KS_d5l3x_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5l3x.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5l3x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l3x.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5l3x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5l3x.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pd5l3x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV79l HV79r K4l K4r K7) | evalEk' ZA Hag ltac:(clear - HV76l HV76r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5x1 := LibSegZ_d5x1.
Definition KS_d5x1 : list nat := Eval vm_compute in (BG.kept_list 80 Pd5x1.regs0 Pd5x1.regs_out0).
Lemma KS_d5x1_ok : BG.kept_ok 80 Pd5x1.regs0 Pd5x1.regs_out0 KS_d5x1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5x1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x2223c M) (st fx' R' 0x215d0 M')
        /\ (forall x, In x KS_d5x1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139844
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] G2 G9 [K0l K0r] K1.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E Pd5x1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5x1.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5x1.kn0).
  { unfold know_ok, Pd5x1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_nil. }
  destruct (Pd5x1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5x1.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5x1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5x1.ps0) with 0x215d0 in Hms. change (SR.ps_regs Pd5x1.ps0) with (map (fun i => (i, nth i Pd5x1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5x1.ps0) with Pd5x1.cells0 in Hcells. unfold Pd5x1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5x1.regs0 Pd5x1.regs_out0 80 KS_d5x1 KS_d5x1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5x1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5x1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5x1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5x1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5x2n := LibSegZ_d5x2n.
Definition KS_d5x2n : list nat := Eval vm_compute in (BG.kept_list 80 Pd5x2n.regs0 Pd5x2n.regs_out0).
Lemma KS_d5x2n_ok : BG.kept_ok 80 Pd5x2n.regs0 Pd5x2n.regs_out0 KS_d5x2n = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5x2n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 272) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 280) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 288) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 256) 0 -> 1048576 <= (V 35%nat) <= 140737488355296 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 304) + 304 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 304)) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 ->
  L5.writable RSEGS M (V 35%nat) 32 -> 0 <= (V 61%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 35%nat) + 0) <= i < ((V 35%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22244 M) (st fx' R' 0x22290 M')
        /\ (forall x, In x KS_d5x2n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (2 * (V 61%nat))
        /\ getr R' (reg 19) = Z_to_bv 64 (V 62%nat)
        /\ L5.u8_at RSEGS M' (V 35%nat) (Z.lor (Z.land (V 69%nat) 253) ((2 * (V 61%nat)) mod 2 ^ 64))).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV36l HV36r] [HV61l HV61r] [HV62l HV62r] [HV69l HV69r] G2 G9 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r] K8 K9 K10 [K11l K11r] K12 [K13l K13r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 69%nat => (V 69%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E Pd5x2n.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5x2n.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5x2n.kn0).
  { unfold know_ok, Pd5x2n.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV61l HV61r K13l K13r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk ZA ltac:(clear - HV69l HV69r K11l K11r) | clear - HV35l HV35r K7l K7r K9; lia | clear - HV35l HV35r K7l K7r K9; lia | byte_tac ltac:(clear - HV69l HV69r K11l K11r; lia) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K7l K7r K9; lia | clear - HV35l HV35r K7l K7r K9; lia | clear - HV35l HV35r K7l K7r K9; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_nil. }
  destruct (Pd5x2n.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5x2n.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pd5x2n.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K7l K7r K9) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K7l K7r K9 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5x2n.ps0) with 0x22290 in Hms. change (SR.ps_regs Pd5x2n.ps0) with (map (fun i => (i, nth i Pd5x2n.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5x2n.ps0) with Pd5x2n.cells0 in Hcells. unfold Pd5x2n.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5x2n.regs0 Pd5x2n.regs_out0 80 KS_d5x2n KS_d5x2n_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5x2n.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5x2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5x2n.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5x2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5x2n.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5x2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5x2n.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5x2n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K7l K7r K9) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV61l HV61r K13l K13r HV69l HV69r K11l K11r; lia) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5t0i := LibSegZ_d5t0i.
Definition KS_d5t0i : list nat := Eval vm_compute in (BG.kept_list 80 Pd5t0i.regs0 Pd5t0i.regs_out0).
Lemma KS_d5t0i_ok : BG.kept_ok 80 Pd5t0i.regs0 Pd5t0i.regs_out0 KS_d5t0i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5t0i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 232) (V 41%nat) ->
  0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22290 M) (st fx' R' 0x222b0 M')
        /\ (forall x, In x KS_d5t0i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] G2 [K0l K0r] K1 K2 K3 [K4l K4r] K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E Pd5t0i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5t0i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5t0i.kn0).
  { unfold know_ok, Pd5t0i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K4l K4r K5; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false (V 41%nat) ltac:(clear - HV41l HV41r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_nil. }
  destruct (Pd5t0i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5t0i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5t0i.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5t0i.ps0) with 0x222b0 in Hms. change (SR.ps_regs Pd5t0i.ps0) with (map (fun i => (i, nth i Pd5t0i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5t0i.ps0) with Pd5t0i.cells0 in Hcells. unfold Pd5t0i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5t0i.regs0 Pd5t0i.regs_out0 80 KS_d5t0i KS_d5t0i_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg Pd5t0i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5t0i.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5t0d := LibSegZ_d5t0d.
Definition KS_d5t0d : list nat := Eval vm_compute in (BG.kept_list 80 Pd5t0d.regs0 Pd5t0d.regs_out0).
Lemma KS_d5t0d_ok : BG.kept_ok 80 Pd5t0d.regs0 Pd5t0d.regs_out0 KS_d5t0d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5t0d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 232) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (V 43%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = true ->
  1 <= (V 42%nat) <= 4096 -> 4096 <= (V 43%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22290 M) (st fx' R' 0x3ec28 M')
        /\ (forall x, In x KS_d5t0d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139952
        /\ getr R' (reg 10) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 42%nat))).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] G2 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] [K9l K9r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E Pd5t0d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5t0d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5t0d.kn0).
  { unfold know_ok, Pd5t0d.kn0.
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
  destruct (Pd5t0d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5t0d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5t0d.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5t0d.ps0) with 0x3ec28 in Hms. change (SR.ps_regs Pd5t0d.ps0) with (map (fun i => (i, nth i Pd5t0d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5t0d.ps0) with Pd5t0d.cells0 in Hcells. unfold Pd5t0d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5t0d.regs0 Pd5t0d.regs_out0 80 KS_d5t0d KS_d5t0d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5t0d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5t0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5t0d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5t0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5t0d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5t0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5t1i := LibSegZ_d5t1i.
Definition KS_d5t1i : list nat := Eval vm_compute in (BG.kept_list 80 Pd5t1i.regs0 Pd5t1i.regs_out0).
Lemma KS_d5t1i_ok : BG.kept_ok 80 Pd5t1i.regs0 Pd5t1i.regs_out0 KS_d5t1i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5t1i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 200) (V 41%nat) ->
  0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x222b0 M) (st fx' R' 0x222d0 M')
        /\ (forall x, In x KS_d5t1i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] G2 [K0l K0r] K1 K2 K3 [K4l K4r] K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E Pd5t1i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5t1i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5t1i.kn0).
  { unfold know_ok, Pd5t1i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K4l K4r K5; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false (V 41%nat) ltac:(clear - HV41l HV41r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_nil. }
  destruct (Pd5t1i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5t1i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5t1i.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5t1i.ps0) with 0x222d0 in Hms. change (SR.ps_regs Pd5t1i.ps0) with (map (fun i => (i, nth i Pd5t1i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5t1i.ps0) with Pd5t1i.cells0 in Hcells. unfold Pd5t1i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5t1i.regs0 Pd5t1i.regs_out0 80 KS_d5t1i KS_d5t1i_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg Pd5t1i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5t1i.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5t1d := LibSegZ_d5t1d.
Definition KS_d5t1d : list nat := Eval vm_compute in (BG.kept_list 80 Pd5t1d.regs0 Pd5t1d.regs_out0).
Lemma KS_d5t1d_ok : BG.kept_ok 80 Pd5t1d.regs0 Pd5t1d.regs_out0 KS_d5t1d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5t1d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 200) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 43%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = true ->
  1 <= (V 42%nat) <= 4096 -> 4096 <= (V 43%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x222b0 M) (st fx' R' 0x3ec28 M')
        /\ (forall x, In x KS_d5t1d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 139984
        /\ getr R' (reg 10) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 42%nat))).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] G2 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] [K9l K9r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E Pd5t1d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5t1d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5t1d.kn0).
  { unfold know_ok, Pd5t1d.kn0.
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
  destruct (Pd5t1d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5t1d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5t1d.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5t1d.ps0) with 0x3ec28 in Hms. change (SR.ps_regs Pd5t1d.ps0) with (map (fun i => (i, nth i Pd5t1d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5t1d.ps0) with Pd5t1d.cells0 in Hcells. unfold Pd5t1d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5t1d.regs0 Pd5t1d.regs_out0 80 KS_d5t1d KS_d5t1d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5t1d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5t1d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5t1d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5t1d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5t1d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5t1d.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5t2i := LibSegZ_d5t2i.
Definition KS_d5t2i : list nat := Eval vm_compute in (BG.kept_list 80 Pd5t2i.regs0 Pd5t2i.regs_out0).
Lemma KS_d5t2i_ok : BG.kept_ok 80 Pd5t2i.regs0 Pd5t2i.regs_out0 KS_d5t2i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5t2i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 168) (V 41%nat) ->
  0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x222d0 M) (st fx' R' 0x222f0 M')
        /\ (forall x, In x KS_d5t2i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] G2 [K0l K0r] K1 K2 K3 [K4l K4r] K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E Pd5t2i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5t2i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5t2i.kn0).
  { unfold know_ok, Pd5t2i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K4l K4r K5; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false (V 41%nat) ltac:(clear - HV41l HV41r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_nil. }
  destruct (Pd5t2i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5t2i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5t2i.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5t2i.ps0) with 0x222f0 in Hms. change (SR.ps_regs Pd5t2i.ps0) with (map (fun i => (i, nth i Pd5t2i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5t2i.ps0) with Pd5t2i.cells0 in Hcells. unfold Pd5t2i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5t2i.regs0 Pd5t2i.regs_out0 80 KS_d5t2i KS_d5t2i_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg Pd5t2i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5t2i.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5t2d := LibSegZ_d5t2d.
Definition KS_d5t2d : list nat := Eval vm_compute in (BG.kept_list 80 Pd5t2d.regs0 Pd5t2d.regs_out0).
Lemma KS_d5t2d_ok : BG.kept_ok 80 Pd5t2d.regs0 Pd5t2d.regs_out0 KS_d5t2d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5t2d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 168) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 43%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = true ->
  1 <= (V 42%nat) <= 4096 -> 4096 <= (V 43%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x222d0 M) (st fx' R' 0x3ec28 M')
        /\ (forall x, In x KS_d5t2d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 140016
        /\ getr R' (reg 10) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 42%nat))).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] G2 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] [K9l K9r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E Pd5t2d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5t2d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5t2d.kn0).
  { unfold know_ok, Pd5t2d.kn0.
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
  destruct (Pd5t2d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5t2d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5t2d.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5t2d.ps0) with 0x3ec28 in Hms. change (SR.ps_regs Pd5t2d.ps0) with (map (fun i => (i, nth i Pd5t2d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5t2d.ps0) with Pd5t2d.cells0 in Hcells. unfold Pd5t2d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5t2d.regs0 Pd5t2d.regs_out0 80 KS_d5t2d KS_d5t2d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5t2d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5t2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5t2d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5t2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5t2d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5t2d.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5t3i := LibSegZ_d5t3i.
Definition KS_d5t3i : list nat := Eval vm_compute in (BG.kept_list 80 Pd5t3i.regs0 Pd5t3i.regs_out0).
Lemma KS_d5t3i_ok : BG.kept_ok 80 Pd5t3i.regs0 Pd5t3i.regs_out0 KS_d5t3i = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5t3i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x222f0 M) (st fx' R' 0x22310 M')
        /\ (forall x, In x KS_d5t3i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] G2 [K0l K0r] K1 K2 K3 [K4l K4r] K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E Pd5t3i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5t3i.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5t3i.kn0).
  { unfold know_ok, Pd5t3i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV41l HV41r K4l K4r K5; lia) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false (V 41%nat) ltac:(clear - HV41l HV41r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_nil. }
  destruct (Pd5t3i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5t3i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5t3i.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5t3i.ps0) with 0x22310 in Hms. change (SR.ps_regs Pd5t3i.ps0) with (map (fun i => (i, nth i Pd5t3i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5t3i.ps0) with Pd5t3i.cells0 in Hcells. unfold Pd5t3i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5t3i.regs0 Pd5t3i.regs_out0 80 KS_d5t3i KS_d5t3i_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg Pd5t3i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5t3i.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5t3d := LibSegZ_d5t3d.
Definition KS_d5t3d : list nat := Eval vm_compute in (BG.kept_list 80 Pd5t3d.regs0 Pd5t3d.regs_out0).
Lemma KS_d5t3d_ok : BG.kept_ok 80 Pd5t3d.regs0 Pd5t3d.regs_out0 KS_d5t3d = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5t3d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 43%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = true ->
  1 <= (V 42%nat) <= 4096 -> 4096 <= (V 43%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x222f0 M) (st fx' R' 0x3ec28 M')
        /\ (forall x, In x KS_d5t3d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 140048
        /\ getr R' (reg 10) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 42%nat))).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] G2 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] [K9l K9r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E Pd5t3d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5t3d.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5t3d.kn0).
  { unfold know_ok, Pd5t3d.kn0.
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
  destruct (Pd5t3d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5t3d.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5t3d.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5t3d.ps0) with 0x3ec28 in Hms. change (SR.ps_regs Pd5t3d.ps0) with (map (fun i => (i, nth i Pd5t3d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5t3d.ps0) with Pd5t3d.cells0 in Hcells. unfold Pd5t3d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5t3d.regs0 Pd5t3d.regs_out0 80 KS_d5t3d KS_d5t3d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5t3d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5t3d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5t3d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pd5t3d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5t3d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pd5t3d.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pd5epi := LibSegZ_d5epi.
Definition KS_d5epi : list nat := Eval vm_compute in (BG.kept_list 80 Pd5epi.regs0 Pd5epi.regs_out0).
Lemma KS_d5epi_ok : BG.kept_ok 80 Pd5epi.regs0 Pd5epi.regs_out0 KS_d5epi = true. Proof. vm_compute. reflexivity. Qed.
Lemma d5epi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x22310 M) (st fx' R' 0x22348 M')
        /\ (forall x, In x KS_d5epi -> getr R' (reg x) = getr R (reg x))
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
  assert (HR: regs_ok E Pd5epi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pd5epi.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pd5epi.kn0).
  { unfold know_ok, Pd5epi.kn0.
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
  destruct (Pd5epi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pd5epi.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pd5epi.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pd5epi.ps0) with 0x22348 in Hms. change (SR.ps_regs Pd5epi.ps0) with (map (fun i => (i, nth i Pd5epi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pd5epi.ps0) with Pd5epi.cells0 in Hcells. unfold Pd5epi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pd5epi.regs0 Pd5epi.regs_out0 80 KS_d5epi KS_d5epi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pd5epi.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pd5epi.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End L5DIVNP.
