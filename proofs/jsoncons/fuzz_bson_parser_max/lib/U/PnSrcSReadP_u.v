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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_srAlt_u LibSegBs_srAge_u LibSegBs_srBeq_u LibSegBs_srBne_u LibSegBs_srA0f_u LibSegBs_srA0e_u LibSegBs_srA0d_u LibSegBs_srC0_u LibSegBs_srClt_u LibSegBs_srCge_u LibSegBs_srD_u LibSegBs_srE1_u LibSegBs_srE2_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMSRDP.
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
Module PsrAlt := LibSegBs_srAlt_u.
Definition KS_srAlt : list nat := Eval vm_compute in (BG.kept_list 48 PsrAlt.regs0 PsrAlt.regs_out0).
Lemma KS_srAlt_ok : BG.kept_ok 48 PsrAlt.regs0 PsrAlt.regs_out0 KS_srAlt = true. Proof. vm_compute. reflexivity. Qed.
Lemma srAlt_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 38%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483120 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) -> L5.defined M ((V 36%nat) + 256) 8 -> L5.writable RSEGS M ((V 36%nat) + 256) 40 ->
  2 <= (V 33%nat) <= 16384 -> 1 <= (V 38%nat) <= 16383 -> 1 <= ((V 33%nat) - (V 38%nat)) <= 16383 -> 4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x370d0 M) (st fx' R' 0xab480 M')
        /\ (forall x, In x KS_srAlt -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 225560
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G10 G11 G12 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 K8 K9 K10 K11 pvzI10 pvzI11 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K12l; move K12l before pvzI10; pose proof (proj2 pvzI10) as K12r; move K12r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K15l; move K15l before pvzI13; pose proof (proj2 pvzI13) as K15r; move K15r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PsrAlt.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrAlt.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrAlt.kn0).
  { unfold know_ok, PsrAlt.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV35l HV35r K15l K15r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14l K14r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14l K14r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K13l K13r K14l K14r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14l K14r HV38l HV38r K13l K13r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrAlt.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrAlt.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PsrAlt.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrAlt.ps0) with 0xab480 in Hms. change (SR.ps_regs PsrAlt.ps0) with (map (fun i => (i, nth i PsrAlt.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrAlt.ps0) with PsrAlt.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrAlt.regs0 PsrAlt.regs_out0 48 KS_srAlt KS_srAlt_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrAlt.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrAlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAlt.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrAlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAlt.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrAlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAlt.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrAlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAlt.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrAlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAlt.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrAlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAlt.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrAlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAlt.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrAlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrAge := LibSegBs_srAge_u.
Definition KS_srAge : list nat := Eval vm_compute in (BG.kept_list 48 PsrAge.regs0 PsrAge.regs_out0).
Lemma KS_srAge_ok : BG.kept_ok 48 PsrAge.regs0 PsrAge.regs_out0 KS_srAge = true. Proof. vm_compute. reflexivity. Qed.
Lemma srAge_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 38%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483120 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) -> L5.defined M ((V 36%nat) + 256) 8 -> L5.writable RSEGS M ((V 36%nat) + 256) 40 ->
  1 <= (V 33%nat) <= 16384 -> 1 <= (V 38%nat) <= 16384 -> 0 <= (((-1) * (V 33%nat)) + (V 38%nat)) <= 16383 -> 4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x370d0 M) (st fx' R' 0xab480 M')
        /\ (forall x, In x KS_srAge -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 225560
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G10 G11 G12 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 K8 K9 K10 K11 pvzI10 pvzI11 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K12l; move K12l before pvzI10; pose proof (proj2 pvzI10) as K12r; move K12r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K15l; move K15l before pvzI13; pose proof (proj2 pvzI13) as K15r; move K15r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PsrAge.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrAge.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrAge.kn0).
  { unfold know_ok, PsrAge.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV35l HV35r K15l K15r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14l K14r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14l K14r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K13l K13r K14l K14r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14l K14r HV38l HV38r K13l K13r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrAge.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrAge.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PsrAge.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrAge.ps0) with 0xab480 in Hms. change (SR.ps_regs PsrAge.ps0) with (map (fun i => (i, nth i PsrAge.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrAge.ps0) with PsrAge.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrAge.regs0 PsrAge.regs_out0 48 KS_srAge KS_srAge_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrAge.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrAge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAge.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrAge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAge.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrAge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAge.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrAge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAge.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrAge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAge.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrAge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAge.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrAge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAge.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrAge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrAge.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrAge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrBeq := LibSegBs_srBeq_u.
Definition KS_srBeq : list nat := Eval vm_compute in (BG.kept_list 48 PsrBeq.regs0 PsrBeq.regs_out0).
Lemma KS_srBeq_ok : BG.kept_ok 48 PsrBeq.regs0 PsrBeq.regs_out0 KS_srBeq = true. Proof. vm_compute. reflexivity. Qed.
Lemma srBeq_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 39%nat) -> getr R (reg 18) = Z_to_bv 64 (V 39%nat) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483120 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) -> L5.defined M ((V 36%nat) + 256) 8 -> L5.writable RSEGS M ((V 36%nat) + 256) 40 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> 1 <= (V 33%nat) <= 16384 -> 1 <= (V 39%nat) <= 16384 -> 0 <= ((V 33%nat) - (V 39%nat)) <= 16383 ->
  4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x37118 M) (st fx' R' 0x372c8 M')
        /\ (forall x, In x KS_srBeq -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) - (V 39%nat))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) ((V 33%nat) - (V 39%nat))
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) ((V 35%nat) + (V 39%nat))
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G18 G19 pvzI13 K1 K2 pvzI14 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI15 pvzI16 pvzI17 pvzI18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV41l; move HV41l before pvzI9; pose proof (proj2 pvzI9) as HV41r; move HV41r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV42l; move HV42l before pvzI10; pose proof (proj2 pvzI10) as HV42r; move HV42r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV43l; move HV43l before pvzI11; pose proof (proj2 pvzI11) as HV43r; move HV43r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV44l; move HV44l before pvzI12; pose proof (proj2 pvzI12) as HV44r; move HV44r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K0l; move K0l before pvzI13; pose proof (proj2 pvzI13) as K0r; move K0r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K17l; move K17l before pvzI15; pose proof (proj2 pvzI15) as K17r; move K17r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K18l; move K18l before pvzI16; pose proof (proj2 pvzI16) as K18r; move K18r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K19l; move K19l before pvzI17; pose proof (proj2 pvzI17) as K19r; move K19r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K20l; move K20l before pvzI18; pose proof (proj2 pvzI18) as K20r; move K20r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E PsrBeq.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrBeq.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrBeq.kn0).
  { unfold know_ok, PsrBeq.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV35l HV35r K20l K20r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K19l K19r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K19l K19r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K18l K18r K19l K19r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K19l K19r HV39l HV39r K18l K18r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrBeq.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrBeq.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PsrBeq.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrBeq.ps0) with 0x372c8 in Hms. change (SR.ps_regs PsrBeq.ps0) with (map (fun i => (i, nth i PsrBeq.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrBeq.ps0) with PsrBeq.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrBeq.regs0 PsrBeq.regs_out0 48 KS_srBeq KS_srBeq_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrBeq.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrBeq.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrBeq.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrBeq.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrBeq.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrBeq.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrBeq.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrBeq.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrBeq.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrBeq.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrBeq.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrBeq.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrBeq.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrBeq.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrBeq.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrBeq.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K17l K17r K19l K19r HV39l HV39r K18l K18r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K20l K20r HV39l HV39r K18l K18r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrBne := LibSegBs_srBne_u.
Definition KS_srBne : list nat := Eval vm_compute in (BG.kept_list 48 PsrBne.regs0 PsrBne.regs_out0).
Lemma KS_srBne_ok : BG.kept_ok 48 PsrBne.regs0 PsrBne.regs_out0 KS_srBne = true. Proof. vm_compute. reflexivity. Qed.
Lemma srBne_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 39%nat) -> getr R (reg 18) = Z_to_bv 64 (V 38%nat) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483120 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 39%nat) -> L5.defined M ((V 36%nat) + 256) 8 -> L5.writable RSEGS M ((V 36%nat) + 256) 40 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> 1 <= (V 39%nat) <= 16383 -> 2 <= (V 38%nat) <= 16384 -> 1 <= ((V 38%nat) - (V 39%nat)) <= 16383 ->
  4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x37118 M) (st fx' R' 0x382d4 M')
        /\ (forall x, In x KS_srBne -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 225660
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 16384
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 38%nat) - (V 39%nat))
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G18 G19 pvzI13 K1 K2 pvzI14 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI15 pvzI16 pvzI17 pvzI18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV41l; move HV41l before pvzI9; pose proof (proj2 pvzI9) as HV41r; move HV41r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV42l; move HV42l before pvzI10; pose proof (proj2 pvzI10) as HV42r; move HV42r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV43l; move HV43l before pvzI11; pose proof (proj2 pvzI11) as HV43r; move HV43r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV44l; move HV44l before pvzI12; pose proof (proj2 pvzI12) as HV44r; move HV44r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K0l; move K0l before pvzI13; pose proof (proj2 pvzI13) as K0r; move K0r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K17l; move K17l before pvzI15; pose proof (proj2 pvzI15) as K17r; move K17r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K18l; move K18l before pvzI16; pose proof (proj2 pvzI16) as K18r; move K18r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K19l; move K19l before pvzI17; pose proof (proj2 pvzI17) as K19r; move K19r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K20l; move K20l before pvzI18; pose proof (proj2 pvzI18) as K20r; move K20r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E PsrBne.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrBne.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrBne.kn0).
  { unfold know_ok, PsrBne.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV35l HV35r K20l K20r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K19l K19r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K19l K19r HV39l HV39r K17l K17r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrBne.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrBne.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PsrBne.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrBne.ps0) with 0x382d4 in Hms. change (SR.ps_regs PsrBne.ps0) with (map (fun i => (i, nth i PsrBne.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrBne.ps0) with PsrBne.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrBne.regs0 PsrBne.regs_out0 48 KS_srBne KS_srBne_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrBne.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrBne.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrBne.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrBne.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrBne.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrBne.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrBne.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrBne.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrBne.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrBne.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrA0f := LibSegBs_srA0f_u.
Definition KS_srA0f : list nat := Eval vm_compute in (BG.kept_list 48 PsrA0f.regs0 PsrA0f.regs_out0).
Lemma KS_srA0f_ok : BG.kept_ok 48 PsrA0f.regs0 PsrA0f.regs_out0 KS_srA0f = true. Proof. vm_compute. reflexivity. Qed.
Lemma srA0f_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 38%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483120 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> L5.defined M ((V 36%nat) + 256) 8 -> L5.writable RSEGS M ((V 36%nat) + 256) 40 ->
  1 <= (V 38%nat) <= 16383 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x370d0 M) (st fx' R' 0x382d4 M')
        /\ (forall x, In x KS_srA0f -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 225660
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 16384
        /\ getr R' (reg 18) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.defined M' ((V 36%nat) + 256) 8).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 K8 K9 K10 K11 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PsrA0f.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrA0f.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrA0f.kn0).
  { unfold know_ok, PsrA0f.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrA0f.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrA0f.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PsrA0f.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrA0f.ps0) with 0x382d4 in Hms. change (SR.ps_regs PsrA0f.ps0) with (map (fun i => (i, nth i PsrA0f.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrA0f.ps0) with PsrA0f.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrA0f.regs0 PsrA0f.regs_out0 48 KS_srA0f KS_srA0f_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrA0f.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrA0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0f.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrA0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0f.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrA0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0f.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrA0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0f.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrA0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0f.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrA0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0f.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrA0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0f.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrA0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrA0e := LibSegBs_srA0e_u.
Definition KS_srA0e : list nat := Eval vm_compute in (BG.kept_list 48 PsrA0e.regs0 PsrA0e.regs_out0).
Lemma KS_srA0e_ok : BG.kept_ok 48 PsrA0e.regs0 PsrA0e.regs_out0 KS_srA0e = true. Proof. vm_compute. reflexivity. Qed.
Lemma srA0e_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 16384 ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483120 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> L5.defined M ((V 36%nat) + 256) 8 -> L5.writable RSEGS M ((V 36%nat) + 256) 40 ->
  140735332483120 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((V 2%nat) - 48)) -> L5.img_clear M 65536 754672 ->
  ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 45%nat) + 16) -> L5.u64_at RSEGS M (V 45%nat) 740792 ->
  L5.u64_at RSEGS M ((V 45%nat) + 16) 740552 -> L5.u32_at RSEGS M ((V 45%nat) + 152) 2 -> L5.u32_at RSEGS M ((V 45%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 160) ((V 45%nat) + 16) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x370d0 M) (st fx' R' 0x372c8 M')
        /\ (forall x, In x KS_srA0e -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.defined M' ((V 36%nat) + 256) 8).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 K8 K9 K10 K11 pvzI9 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_45 := V 45%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 45%nat => Z_to_bv 64 vz_45 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 45%nat => vz_45 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 46%nat. }
  assert (HR: regs_ok E PsrA0e.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrA0e.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrA0e.kn0).
  { unfold know_ok, PsrA0e.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K23]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrA0e.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrA0e.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PsrA0e.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrA0e.ps0) with 0x372c8 in Hms. change (SR.ps_regs PsrA0e.ps0) with (map (fun i => (i, nth i PsrA0e.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrA0e.ps0) with PsrA0e.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrA0e.regs0 PsrA0e.regs_out0 48 KS_srA0e KS_srA0e_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrA0e.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrA0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0e.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrA0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrA0d := LibSegBs_srA0d_u.
Definition KS_srA0d : list nat := Eval vm_compute in (BG.kept_list 48 PsrA0d.regs0 PsrA0d.regs_out0).
Lemma KS_srA0d_ok : BG.kept_ok 48 PsrA0d.regs0 PsrA0d.regs_out0 KS_srA0d = true. Proof. vm_compute. reflexivity. Qed.
Lemma srA0d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 16384 ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483120 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> L5.defined M ((V 36%nat) + 256) 8 -> L5.writable RSEGS M ((V 36%nat) + 256) 40 ->
  140735332483120 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((V 2%nat) - 48)) -> L5.img_clear M 65536 754672 ->
  ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 45%nat) + 16) -> L5.u64_at RSEGS M (V 45%nat) 740792 ->
  L5.u64_at RSEGS M ((V 45%nat) + 16) 740552 -> L5.u32_at RSEGS M ((V 45%nat) + 152) 0 -> L5.u32_at RSEGS M ((V 45%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 160) ((V 45%nat) + 16) ->
  1 <= (V 37%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x370d0 M) (st fx' R' 0x5d574 M')
        /\ (forall x, In x KS_srA0d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 225876
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 45%nat) + 16)
        /\ getr R' (reg 13) = Z_to_bv 64 382324
        /\ getr R' (reg 18) = Z_to_bv 64 16384
        /\ getr R' (reg 19) = Z_to_bv 64 (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 K8 K9 K10 K11 pvzI9 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K24l; move K24l before pvzI10; pose proof (proj2 pvzI10) as K24r; move K24r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_45 := V 45%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 45%nat => Z_to_bv 64 vz_45 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 45%nat => vz_45 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 46%nat. }
  assert (HR: regs_ok E PsrA0d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrA0d.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrA0d.kn0).
  { unfold know_ok, PsrA0d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrA0d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrA0d.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PsrA0d.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrA0d.ps0) with 0x5d574 in Hms. change (SR.ps_regs PsrA0d.ps0) with (map (fun i => (i, nth i PsrA0d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrA0d.ps0) with PsrA0d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrA0d.regs0 PsrA0d.regs_out0 48 KS_srA0d KS_srA0d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrA0d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrA0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0d.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrA0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0d.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrA0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0d.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrA0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrA0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0d.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PsrA0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0d.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrA0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrA0d.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrA0d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrC0 := LibSegBs_srC0_u.
Definition KS_srC0 : list nat := Eval vm_compute in (BG.kept_list 48 PsrC0.regs0 PsrC0.regs_out0).
Lemma KS_srC0_ok : BG.kept_ok 48 PsrC0.regs0 PsrC0.regs_out0 KS_srC0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma srC0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 39%nat) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 38%nat) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483120 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> L5.defined M ((V 36%nat) + 256) 8 -> L5.writable RSEGS M ((V 36%nat) + 256) 40 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3717c M) (st fx' R' 0x372c8 M')
        /\ (forall x, In x KS_srC0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G10 G18 G19 pvzI12 K1 K2 pvzI13 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV41l; move HV41l before pvzI8; pose proof (proj2 pvzI8) as HV41r; move HV41r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV42l; move HV42l before pvzI9; pose proof (proj2 pvzI9) as HV42r; move HV42r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV43l; move HV43l before pvzI10; pose proof (proj2 pvzI10) as HV43r; move HV43r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV44l; move HV44l before pvzI11; pose proof (proj2 pvzI11) as HV44r; move HV44r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K3l; move K3l before pvzI13; pose proof (proj2 pvzI13) as K3r; move K3r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E PsrC0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrC0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrC0.kn0).
  { unfold know_ok, PsrC0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K16]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrC0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrC0.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PsrC0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrC0.ps0) with 0x372c8 in Hms. change (SR.ps_regs PsrC0.ps0) with (map (fun i => (i, nth i PsrC0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrC0.ps0) with PsrC0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrC0.regs0 PsrC0.regs_out0 48 KS_srC0 KS_srC0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrC0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrC0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrC0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrC0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrC0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrC0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrC0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrC0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrC0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrC0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrC0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrC0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrC0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrC0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrClt := LibSegBs_srClt_u.
Definition KS_srClt : list nat := Eval vm_compute in (BG.kept_list 48 PsrClt.regs0 PsrClt.regs_out0).
Lemma KS_srClt_ok : BG.kept_ok 48 PsrClt.regs0 PsrClt.regs_out0 KS_srClt = true. Proof. vm_compute. reflexivity. Qed.
Lemma srClt_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 39%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 38%nat) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483120 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> L5.defined M ((V 36%nat) + 256) 8 -> L5.writable RSEGS M ((V 36%nat) + 256) 40 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> 2 <= (V 33%nat) <= 16384 -> 1 <= (V 38%nat) <= 16383 -> 1 <= ((V 33%nat) - (V 38%nat)) <= 16383 ->
  0 <= (V 39%nat) <= 16383 -> 1 <= (V 37%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3717c M) (st fx' R' 0xab480 M')
        /\ (forall x, In x KS_srClt -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 225712
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) + (V 39%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G18 G19 pvzI13 K1 K2 pvzI14 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV41l; move HV41l before pvzI9; pose proof (proj2 pvzI9) as HV41r; move HV41r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV42l; move HV42l before pvzI10; pose proof (proj2 pvzI10) as HV42r; move HV42r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV43l; move HV43l before pvzI11; pose proof (proj2 pvzI11) as HV43r; move HV43r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV44l; move HV44l before pvzI12; pose proof (proj2 pvzI12) as HV44r; move HV44r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K0l; move K0l before pvzI13; pose proof (proj2 pvzI13) as K0r; move K0r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K17l; move K17l before pvzI15; pose proof (proj2 pvzI15) as K17r; move K17r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K18l; move K18l before pvzI16; pose proof (proj2 pvzI16) as K18r; move K18r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K19l; move K19l before pvzI17; pose proof (proj2 pvzI17) as K19r; move K19r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K20l; move K20l before pvzI18; pose proof (proj2 pvzI18) as K20r; move K20r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K21l; move K21l before pvzI19; pose proof (proj2 pvzI19) as K21r; move K21r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E PsrClt.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrClt.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrClt.kn0).
  { unfold know_ok, PsrClt.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K19l K19r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K19l K19r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K19l K19r HV38l HV38r K18l K18r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrClt.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrClt.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PsrClt.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrClt.ps0) with 0xab480 in Hms. change (SR.ps_regs PsrClt.ps0) with (map (fun i => (i, nth i PsrClt.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrClt.ps0) with PsrClt.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrClt.regs0 PsrClt.regs_out0 48 KS_srClt KS_srClt_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrClt.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrClt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrClt.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrClt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrClt.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrClt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrClt.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrClt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K17l K17r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrCge := LibSegBs_srCge_u.
Definition KS_srCge : list nat := Eval vm_compute in (BG.kept_list 48 PsrCge.regs0 PsrCge.regs_out0).
Lemma KS_srCge_ok : BG.kept_ok 48 PsrCge.regs0 PsrCge.regs_out0 KS_srCge = true. Proof. vm_compute. reflexivity. Qed.
Lemma srCge_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 39%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 38%nat) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483120 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> L5.defined M ((V 36%nat) + 256) 8 -> L5.writable RSEGS M ((V 36%nat) + 256) 40 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> 1 <= (V 33%nat) <= 16383 -> 1 <= (V 38%nat) <= 16383 -> 0 <= (((-1) * (V 33%nat)) + (V 38%nat)) <= 16383 ->
  0 <= (V 39%nat) <= 16383 -> 1 <= (V 37%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3717c M) (st fx' R' 0xab480 M')
        /\ (forall x, In x KS_srCge -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 225712
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) + (V 39%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G18 G19 pvzI13 K1 K2 pvzI14 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV41l; move HV41l before pvzI9; pose proof (proj2 pvzI9) as HV41r; move HV41r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV42l; move HV42l before pvzI10; pose proof (proj2 pvzI10) as HV42r; move HV42r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV43l; move HV43l before pvzI11; pose proof (proj2 pvzI11) as HV43r; move HV43r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV44l; move HV44l before pvzI12; pose proof (proj2 pvzI12) as HV44r; move HV44r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K0l; move K0l before pvzI13; pose proof (proj2 pvzI13) as K0r; move K0r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K17l; move K17l before pvzI15; pose proof (proj2 pvzI15) as K17r; move K17r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K18l; move K18l before pvzI16; pose proof (proj2 pvzI16) as K18r; move K18r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K19l; move K19l before pvzI17; pose proof (proj2 pvzI17) as K19r; move K19r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K20l; move K20l before pvzI18; pose proof (proj2 pvzI18) as K20r; move K20r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K21l; move K21l before pvzI19; pose proof (proj2 pvzI19) as K21r; move K21r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E PsrCge.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrCge.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrCge.kn0).
  { unfold know_ok, PsrCge.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K19l K19r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K19l K19r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K19l K19r HV38l HV38r K18l K18r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrCge.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrCge.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PsrCge.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrCge.ps0) with 0xab480 in Hms. change (SR.ps_regs PsrCge.ps0) with (map (fun i => (i, nth i PsrCge.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrCge.ps0) with PsrCge.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrCge.regs0 PsrCge.regs_out0 48 KS_srCge KS_srCge_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrCge.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrCge.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrCge.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrCge.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrCge.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K17l K17r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrD := LibSegBs_srD_u.
Definition KS_srD : list nat := Eval vm_compute in (BG.kept_list 48 PsrD.regs0 PsrD.regs_out0).
Lemma KS_srD_ok : BG.kept_ok 48 PsrD.regs0 PsrD.regs_out0 KS_srD = true. Proof. vm_compute. reflexivity. Qed.
Lemma srD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 39%nat) -> getr R (reg 18) = Z_to_bv 64 (V 38%nat) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483120 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) -> L5.defined M ((V 36%nat) + 256) 8 -> L5.writable RSEGS M ((V 36%nat) + 256) 40 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> 1 <= (V 33%nat) <= 16384 -> 1 <= (V 38%nat) <= 16383 -> 0 <= ((V 33%nat) - (V 38%nat)) <= 16383 ->
  0 <= (V 39%nat) <= 16383 -> 4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x371b0 M) (st fx' R' 0x372c8 M')
        /\ (forall x, In x KS_srD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 38%nat) + (V 39%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) - (V 38%nat))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) ((V 33%nat) - (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) ((V 35%nat) + (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G18 G19 pvzI14 K1 K2 pvzI15 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV39l; move HV39l before pvzI8; pose proof (proj2 pvzI8) as HV39r; move HV39r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV40l; move HV40l before pvzI9; pose proof (proj2 pvzI9) as HV40r; move HV40r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV41l; move HV41l before pvzI10; pose proof (proj2 pvzI10) as HV41r; move HV41r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV42l; move HV42l before pvzI11; pose proof (proj2 pvzI11) as HV42r; move HV42r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV43l; move HV43l before pvzI12; pose proof (proj2 pvzI12) as HV43r; move HV43r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV44l; move HV44l before pvzI13; pose proof (proj2 pvzI13) as HV44r; move HV44r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K3l; move K3l before pvzI15; pose proof (proj2 pvzI15) as K3r; move K3r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K17l; move K17l before pvzI16; pose proof (proj2 pvzI16) as K17r; move K17r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K18l; move K18l before pvzI17; pose proof (proj2 pvzI17) as K18r; move K18r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K19l; move K19l before pvzI18; pose proof (proj2 pvzI18) as K19r; move K19r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K20l; move K20l before pvzI19; pose proof (proj2 pvzI19) as K20r; move K20r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K21l; move K21l before pvzI20; pose proof (proj2 pvzI20) as K21r; move K21r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E PsrD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrD.kn0).
  { unfold know_ok, PsrD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV35l HV35r K21l K21r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K19l K19r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K19l K19r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K19l K19r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K19l K19r HV38l HV38r K18l K18r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrD.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PsrD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrD.ps0) with 0x372c8 in Hms. change (SR.ps_regs PsrD.ps0) with (map (fun i => (i, nth i PsrD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrD.ps0) with PsrD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrD.regs0 PsrD.regs_out0 48 KS_srD KS_srD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrD.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrD.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrD.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrD.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrD.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K17l K17r K19l K19r HV38l HV38r K18l K18r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K21l K21r HV38l HV38r K18l K18r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrE1 := LibSegBs_srE1_u.
Definition KS_srE1 : list nat := Eval vm_compute in (BG.kept_list 48 PsrE1.regs0 PsrE1.regs_out0).
Lemma KS_srE1_ok : BG.kept_ok 48 PsrE1.regs0 PsrE1.regs_out0 KS_srE1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma srE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 0 -> getr R (reg 10) = Z_to_bv 64 16384 -> getr R (reg 18) = Z_to_bv 64 16384 -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483120 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> L5.defined M ((V 36%nat) + 256) 8 -> L5.writable RSEGS M ((V 36%nat) + 256) 40 ->
  140735332483120 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((V 2%nat) - 48)) -> L5.img_clear M 65536 754672 ->
  ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 45%nat) + 16) -> L5.u64_at RSEGS M (V 45%nat) 740792 ->
  L5.u64_at RSEGS M ((V 45%nat) + 16) 740552 -> L5.u32_at RSEGS M ((V 45%nat) + 152) 0 -> L5.u32_at RSEGS M ((V 45%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 160) ((V 45%nat) + 16) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x37254 M) (st fx' R' 0x372c8 M')
        /\ (forall x, In x KS_srE1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G10 G18 G19 pvzI12 K1 K2 pvzI13 K4 K5 K6 K7 K8 K9 K10 K11 pvzI14 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV42l; move HV42l before pvzI8; pose proof (proj2 pvzI8) as HV42r; move HV42r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV43l; move HV43l before pvzI9; pose proof (proj2 pvzI9) as HV43r; move HV43r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV44l; move HV44l before pvzI10; pose proof (proj2 pvzI10) as HV44r; move HV44r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV45l; move HV45l before pvzI11; pose proof (proj2 pvzI11) as HV45r; move HV45r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K3l; move K3l before pvzI13; pose proof (proj2 pvzI13) as K3r; move K3r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K12l; move K12l before pvzI14; pose proof (proj2 pvzI14) as K12r; move K12r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 46%nat. }
  assert (HR: regs_ok E PsrE1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrE1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrE1.kn0).
  { unfold know_ok, PsrE1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K28]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrE1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrE1.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PsrE1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrE1.ps0) with 0x372c8 in Hms. change (SR.ps_regs PsrE1.ps0) with (map (fun i => (i, nth i PsrE1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrE1.ps0) with PsrE1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrE1.regs0 PsrE1.regs_out0 48 KS_srE1 KS_srE1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrE1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrE1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrE1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrE1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrE1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrE1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrE2 := LibSegBs_srE2_u.
Definition KS_srE2 : list nat := Eval vm_compute in (BG.kept_list 48 PsrE2.regs0 PsrE2.regs_out0).
Lemma KS_srE2_ok : BG.kept_ok 48 PsrE2.regs0 PsrE2.regs_out0 KS_srE2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma srE2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 0 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 16384 -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483120 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> L5.defined M ((V 36%nat) + 256) 8 -> L5.writable RSEGS M ((V 36%nat) + 256) 40 ->
  140735332483120 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 48) + 48 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((V 2%nat) - 48)) -> L5.img_clear M 65536 754672 ->
  ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 45%nat) + 16) -> L5.u64_at RSEGS M (V 45%nat) 740792 ->
  L5.u64_at RSEGS M ((V 45%nat) + 16) 740552 -> L5.u32_at RSEGS M ((V 45%nat) + 152) 0 -> L5.u32_at RSEGS M ((V 45%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 160) ((V 45%nat) + 16) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> 0 <= (V 33%nat) <= 16383 -> L5.writable RSEGS M ((V 45%nat) + 152) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> ~ (((V 45%nat) + 152) <= bv_unsigned a < ((V 45%nat) + 152) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> ~ (((V 45%nat) + 152) <= i < ((V 45%nat) + 152) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x37254 M) (st fx' R' 0x372c8 M')
        /\ (forall x, In x KS_srE2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ L5.u32_at RSEGS M' ((V 45%nat) + 152) 2
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G18 G19 pvzI13 K1 K2 pvzI14 K4 K5 K6 K7 K8 K9 K10 K11 pvzI15 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI16 K30.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV41l; move HV41l before pvzI8; pose proof (proj2 pvzI8) as HV41r; move HV41r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV42l; move HV42l before pvzI9; pose proof (proj2 pvzI9) as HV42r; move HV42r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV43l; move HV43l before pvzI10; pose proof (proj2 pvzI10) as HV43r; move HV43r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV44l; move HV44l before pvzI11; pose proof (proj2 pvzI11) as HV44r; move HV44r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV45l; move HV45l before pvzI12; pose proof (proj2 pvzI12) as HV45r; move HV45r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K0l; move K0l before pvzI13; pose proof (proj2 pvzI13) as K0r; move K0r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K29l; move K29l before pvzI16; pose proof (proj2 pvzI16) as K29r; move K29r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 46%nat. }
  assert (HR: regs_ok E PsrE2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrE2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrE2.kn0).
  { unfold know_ok, PsrE2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear - HV36l HV36r K3l K3r K5 K16; lia | clear - HV36l HV36r K3l K3r K5 K16; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | clear - HV45l HV45r K12l K12r K14 K16; lia | exactA K30]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrE2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrE2.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> ~ ((vz_45 + 152) <= bv_unsigned a < (vz_45 + 152) + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PsrE2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K16 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K12l K12r K14 K16 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrE2.ps0) with 0x372c8 in Hms. change (SR.ps_regs PsrE2.ps0) with (map (fun i => (i, nth i PsrE2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrE2.ps0) with PsrE2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrE2.regs0 PsrE2.regs_out0 48 KS_srE2 KS_srE2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrE2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrE2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrE2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrE2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrE2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrE2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrE2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PsrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrE2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrE2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV45l HV45r K12l K12r K14 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PMSRDP.
