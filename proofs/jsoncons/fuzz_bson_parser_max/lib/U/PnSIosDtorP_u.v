(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import BigLinkGlue_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import L5Kn_u L5KnA_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_idA_u LibSegBs_idB_u LibSegBs_idC_u LibSegBs_idD_u LibSegBs_idE_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMSIDP.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5KA.zpolyA_sound E Vz e z A Pz)).
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
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof. intros K Ha Hn ->. eapply L5K.defined_of_KUnk; eauto. Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof. intros K Ha Hv -> ->. eapply L5KA.u8_of_KWord1_mod; eauto. Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof. intros K Ha Hn ->. eapply L5KA.zeros_of_KZero; eauto. Qed.
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
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof. intros Ha Hm. rewrite Z.land_comm. exact (proj2 (L5K.land_le_r m a Hm Ha)). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
  intros Ha. assert (E : forallb (fun i => let x := Z.of_nat i in (0 <=? (Z.land x 18446744073709551613 + 2) mod 2 ^ 64) && ((Z.land x 18446744073709551613 + 2) mod 2 ^ 64 <? 256)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in E. specialize (E (Z.to_nat a) ltac:(apply in_seq; lia)). cbn zeta in E. rewrite Z2Nat.id in E by lia. apply andb_prop in E as [E1 E2]. lia.
Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; byte_go.
Tactic Notation "byte_tac" tactic(k) := byte_tac0 k.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
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
          | |- L5KA.zeros_at _ ?a _ => lazymatch type of H with L5KA.zeros_at _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
(* [comment removed for export] *)
Local Ltac den_tac := first [reflexivity | lia | idtac].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.
(* [comment removed for export] *)
Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
  repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module PidA := LibSegBs_idA_u.
Definition KS_idA : list nat := Eval vm_compute in (BG.kept_list 48 PidA.regs0 PidA.regs_out0).
Lemma KS_idA_ok : BG.kept_ok 48 PidA.regs0 PidA.regs_out0 KS_idA = true. Proof. vm_compute. reflexivity. Qed.
Lemma idA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 4096 <= (bv_unsigned (getr R (reg 10))) <= 140737488355328 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  L5KA.zeros_at M ((bv_unsigned (getr R (reg 10))) + 56) 80 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 152 <= ((V 2%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 40) <= bv_unsigned a < ((V 2%nat) - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 40) <= i < ((V 2%nat) - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x5d4d0 M) (st fx' R' 0x81cb4 M')
        /\ (forall x, In x KS_idA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 380840
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 740328
        /\ L5.u64_at RSEGS M' (bv_unsigned (getr R (reg 10))) 740328
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 G2 pvzI3 K1 K2 pvzI4 K4 K5 K6 pvzI5 K8 K9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K7l; move K7l before pvzI5; pose proof (proj2 pvzI5) as K7r; move K7r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 34%nat. }
  assert (HR: regs_ok E PidA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PidA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PidA.kn0).
  { unfold know_ok, PidA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K9) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K9) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K9) | evalEk ZA ltac:(clear) | clear - K3l K3r K9; lia | clear - K3l K3r K9; lia | clear - K3l K3r K9; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K9) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r) | clear - K3l K3r K9; lia | clear - K3l K3r K9; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K3l K3r K9) | evalEk ZA ltac:(clear) | clear - K3l K3r K9; lia | clear - K3l K3r K9; lia | clear - K3l K3r K9; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PidA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PidA.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 40) <= bv_unsigned a < (vz_2 - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PidA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K9 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K9) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K9 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PidA.ps0) with 0x81cb4 in Hms. change (SR.ps_regs PidA.ps0) with (map (fun i => (i, nth i PidA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PidA.ps0) with PidA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PidA.regs0 PidA.regs_out0 48 KS_idA KS_idA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PidA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PidA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PidA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PidA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PidA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PidA.regs_out0]. rewrite (BG.edenot_kept 48 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PidA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PidA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PidA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PidA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PidA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PidA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PidB := LibSegBs_idB_u.
Definition KS_idB : list nat := Eval vm_compute in (BG.kept_list 48 PidB.regs0 PidB.regs_out0).
Lemma KS_idB_ok : BG.kept_ok 48 PidB.regs0 PidB.regs_out0 KS_idB = true. Proof. vm_compute. reflexivity. Qed.
Lemma idB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 4096 <= (V 40%nat) <= 140737488355328 ->
  aligned (V 40%nat) 8 -> L5KA.zeros_at M ((V 40%nat) + 56) 80 -> (((V 2%nat) - 48) + 48 <= (V 40%nat) \/ (V 40%nat) + 152 <= ((V 2%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x5cfa8 M) (st fx' R' 0x9cc94 M')
        /\ (forall x, In x KS_idB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 380848
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 G2 G8 pvzI3 K1 K2 pvzI4 K4 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PidB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PidB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PidB.kn0).
  { unfold know_ok, PidB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K6; lia | clear - HV40l HV40r K3l K3r K6; lia | clear - HV40l HV40r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PidB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PidB.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PidB.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PidB.ps0) with 0x9cc94 in Hms. change (SR.ps_regs PidB.ps0) with (map (fun i => (i, nth i PidB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PidB.ps0) with PidB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PidB.regs0 PidB.regs_out0 48 KS_idB KS_idB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PidB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PidB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PidB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PidB.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PidC := LibSegBs_idC_u.
Definition KS_idC : list nat := Eval vm_compute in (BG.kept_list 48 PidC.regs0 PidC.regs_out0).
Lemma KS_idC_ok : BG.kept_ok 48 PidC.regs0 PidC.regs_out0 KS_idC = true. Proof. vm_compute. reflexivity. Qed.
Lemma idC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 4096 <= (V 40%nat) <= 140737488355328 ->
  aligned (V 40%nat) 8 -> L5KA.zeros_at M ((V 40%nat) + 56) 80 -> (((V 2%nat) - 48) + 48 <= (V 40%nat) \/ (V 40%nat) + 152 <= ((V 2%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x5cfb0 M) (st fx' R' 0x9cc94 M')
        /\ (forall x, In x KS_idC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 380856
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 G2 G8 pvzI3 K1 K2 pvzI4 K4 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PidC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PidC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PidC.kn0).
  { unfold know_ok, PidC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K6; lia | clear - HV40l HV40r K3l K3r K6; lia | clear - HV40l HV40r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PidC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PidC.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PidC.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PidC.ps0) with 0x9cc94 in Hms. change (SR.ps_regs PidC.ps0) with (map (fun i => (i, nth i PidC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PidC.ps0) with PidC.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PidC.regs0 PidC.regs_out0 48 KS_idC KS_idC_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PidC.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PidC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PidC.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PidC.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PidD := LibSegBs_idD_u.
Definition KS_idD : list nat := Eval vm_compute in (BG.kept_list 48 PidD.regs0 PidD.regs_out0).
Lemma KS_idD_ok : BG.kept_ok 48 PidD.regs0 PidD.regs_out0 KS_idD = true. Proof. vm_compute. reflexivity. Qed.
Lemma idD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 4096 <= (V 40%nat) <= 140737488355328 ->
  aligned (V 40%nat) 8 -> L5KA.zeros_at M ((V 40%nat) + 56) 80 -> (((V 2%nat) - 48) + 48 <= (V 40%nat) \/ (V 40%nat) + 152 <= ((V 2%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x5cfb8 M) (st fx' R' 0x9cc94 M')
        /\ (forall x, In x KS_idD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 380864
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 G2 G8 pvzI3 K1 K2 pvzI4 K4 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PidD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PidD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PidD.kn0).
  { unfold know_ok, PidD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K6; lia | clear - HV40l HV40r K3l K3r K6; lia | clear - HV40l HV40r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PidD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PidD.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PidD.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PidD.ps0) with 0x9cc94 in Hms. change (SR.ps_regs PidD.ps0) with (map (fun i => (i, nth i PidD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PidD.ps0) with PidD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PidD.regs0 PidD.regs_out0 48 KS_idD KS_idD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PidD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PidD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PidD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PidD.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PidE := LibSegBs_idE_u.
Definition KS_idE : list nat := Eval vm_compute in (BG.kept_list 48 PidE.regs0 PidE.regs_out0).
Lemma KS_idE_ok : BG.kept_ok 48 PidE.regs0 PidE.regs_out0 KS_idE = true. Proof. vm_compute. reflexivity. Qed.
Lemma idE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 4096 <= (V 40%nat) <= 140737488355328 ->
  aligned (V 40%nat) 8 -> L5KA.zeros_at M ((V 40%nat) + 56) 80 -> (((V 2%nat) - 48) + 48 <= (V 40%nat) \/ (V 40%nat) + 152 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 41%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x5cfc0 M) (st fx' R' 0x9cc94 M')
        /\ (forall x, In x KS_idE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 41%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 K8 K9 K10 K11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PidE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PidE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PidE.kn0).
  { unfold know_ok, PidE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K6; lia | clear - HV40l HV40r K3l K3r K6; lia | clear - HV40l HV40r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K11]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PidE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PidE.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PidE.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PidE.ps0) with 0x9cc94 in Hms. change (SR.ps_regs PidE.ps0) with (map (fun i => (i, nth i PidE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PidE.ps0) with PidE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PidE.regs0 PidE.regs_out0 48 KS_idE KS_idE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PidE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PidE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PidE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PidE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PidE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PidE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PidE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PidE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PidE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PidE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PidE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PidE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PidE.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PidE.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End PMSIDP.
