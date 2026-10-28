(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_pbS_u LibSegBs_pbLI_u LibSegBs_pbLG_u LibSegBs_pbGS_u LibSegBs_pbN_u LibSegBs_pbTS_u LibSegBs_pbD_u LibSegBs_pbT_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSPBP.
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
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
  intros K Ha Hv -> -> ->. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd).
  rewrite L5K.adenot_e, Ha in Rd. rewrite (BG.word_of_unsigned _ _ Hv) in Rd.
  pose proof (bv_unsigned_in_range 64 (edenot E e)) as Rg. rewrite Hv in Rg. change (bv_modulus 64) with (2 ^ 64) in Rg.
  unfold word_to_le_bytes in Rd. rewrite Z_to_bv_unsigned in Rd. unfold bv_wrap in Rd. change (bv_modulus 64) with (2 ^ 64) in Rd.
  rewrite (Z.mod_small v (2 ^ 64)) in Rd by (clear - Rg; lia). cbn [Z_to_le_bytes rdn] in Rd. unfold L5.u8_at.
  assert (E1 : (Z_to_bv 64 (a + off) + 1 = Z_to_bv 64 (a + off + 1))%bv).
  { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    change (bv_unsigned (1 : bv 64)) with 1. apply Z.add_mod_idemp_l. clear; lia. }
  rewrite E1 in Rd.
  destruct (match M (Z_to_bv 64 (a + off)) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 (a + off)) end) as [x|] eqn:X; [|discriminate].
  destruct (match M (Z_to_bv 64 (a + off + 1)) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 (a + off + 1)) end) as [y|] eqn:Y; [|discriminate].
  injection Rd as Ex Ey. split.
  - cbn [rdn]. rewrite X. subst x. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_mod by (clear; lia). reflexivity.
  - cbn [rdn]. rewrite Y. subst y. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 8) with 256. rewrite Z.mod_mod by (clear; lia). reflexivity.
Qed.
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
Module PpbS := LibSegBs_pbS_u.
Definition KS_pbS : list nat := Eval vm_compute in (BG.kept_list 60 PpbS.regs0 PpbS.regs_out0).
Lemma KS_pbS_ok : BG.kept_ok 60 PpbS.regs0 PpbS.regs_out0 KS_pbS = true. Proof. vm_compute. reflexivity. Qed.
Lemma pbS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 43 -> Z.testbit (V 33%nat) 0 = false -> 0 <= (bv_unsigned (getr R (reg 11))) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58938 M) (st fx' R' 0x58a68 M')
        /\ (forall x, In x KS_pbS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((bv_unsigned (getr R (reg 10))) + ((V 33%nat) / 2)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + ((V 33%nat) / 2)) + 2) 0
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + ((V 33%nat) / 2)) + 1) (bv_unsigned (getr R (reg 11)))
        /\ L5.u8_at RSEGS M' (bv_unsigned (getr R (reg 10))) ((V 33%nat) + 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 G2 pvzI3 K1 K2 pvzI4 K4 K5 K6 K7 pvzI5 K9 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K8l; move K8l before pvzI5; pose proof (proj2 pvzI5) as K8r; move K8r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K10l; move K10l before pvzI6; pose proof (proj2 pvzI6) as K10r; move K10r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 34%nat. }
  assert (HR: regs_ok E PpbS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PpbS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PpbS.kn0).
  { unfold know_ok, PpbS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | byte_tac ltac:(clear - HV33l HV33r K8l K8r K9) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear; lia | rewrite (L5K.land1_bit0_false vz_33 ltac:(clear - HV33l HV33r K8l K8r K9; lia) K9); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PpbS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PpbS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 64) <= bv_unsigned a < (vz_2 - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PpbS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PpbS.ps0) with 0x58a68 in Hms. change (SR.ps_regs PpbS.ps0) with (map (fun i => (i, nth i PpbS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PpbS.ps0) with PpbS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PpbS.regs0 PpbS.regs_out0 60 KS_pbS KS_pbS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PpbS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PpbS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PpbS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 HV33l HV33r K8l K8r K9) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 HV33l HV33r K8l K8r K9) | evalEk' ZA Hag ltac:(clear - K10l K10r) | byte_tac ltac:(clear - K10l K10r) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K9) | byte_tac ltac:(clear - HV33l HV33r K8l K8r K9) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PpbLI := LibSegBs_pbLI_u.
Definition KS_pbLI : list nat := Eval vm_compute in (BG.kept_list 60 PpbLI.regs0 PpbLI.regs_out0).
Lemma KS_pbLI_ok : BG.kept_ok 60 PpbLI.regs0 PpbLI.regs_out0 KS_pbLI = true. Proof. vm_compute. reflexivity. Qed.
Lemma pbLI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 36%nat) -> Z.testbit (V 36%nat) 0 = true ->
  27 <= (V 36%nat) <= 134217729 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 67108864 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) (V 35%nat) ->
  4096 <= (V 35%nat) <= 140737488355328 -> 0 <= (bv_unsigned (getr R (reg 11))) <= 255 -> 1 <= (((V 34%nat) - ((((2 * ((V 36%nat) / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) -> L5.writable RSEGS M ((V 35%nat) + (V 34%nat)) 2 ->
  (((V 35%nat) + (V 34%nat)) + 2 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 35%nat) + (V 34%nat))) -> (((V 35%nat) + (V 34%nat)) + 2 <= ((V 2%nat) - 64) \/ ((V 2%nat) - 64) + 64 <= ((V 35%nat) + (V 34%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> ~ ((((V 35%nat) + (V 34%nat)) + 0) <= bv_unsigned a < (((V 35%nat) + (V 34%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> ~ ((((V 35%nat) + (V 34%nat)) + 0) <= i < (((V 35%nat) + (V 34%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58938 M) (st fx' R' 0x58a68 M')
        /\ (forall x, In x KS_pbLI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 35%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ L5.u8_at RSEGS M' (((V 34%nat) + (V 35%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 34%nat) + (V 35%nat)) (bv_unsigned (getr R (reg 11)))
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 8) ((V 34%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u8_at RSEGS M' (bv_unsigned (getr R (reg 10))) (V 33%nat)
        /\ L5.u64_at RSEGS M' (bv_unsigned (getr R (reg 10))) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 16) (V 35%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 pvzI8 K9 K10 K11 pvzI9 K13 pvzI10 K15 pvzI11 pvzI12 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K17l; move K17l before pvzI12; pose proof (proj2 pvzI12) as K17r; move K17r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PpbLI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PpbLI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PpbLI.kn0).
  { unfold know_ok, PpbLI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K20) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K20) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K20) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K20; lia | clear - K3l K3r K6 K20; lia | clear - K3l K3r K6 K20; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K20) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K3l K3r K6 K20) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear - K3l K3r K6 K20; lia | clear - K3l K3r K6 K20; lia | byte_tac ltac:(clear - HV33l HV33r K8l K8r K9) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear; lia | rewrite (L5K.land1_bit0_true vz_33 ltac:(clear - HV33l HV33r K8l K8r K9; lia) K9); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K20) | evalEk ZA ltac:(clear - HV36l HV36r K11 K12l K12r K18) | clear - K3l K3r K6 K20; lia | clear - K3l K3r K6 K20; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K11 K12l K12r K18) | clear; lia | rewrite (L5K.land1_bit0_true vz_36 ltac:(clear - HV36l HV36r K11 K12l K12r K18; lia) K11); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K11 K12l K12r K18) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K20) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K18 K20 K21) | clear - K3l K3r K6 K20; lia | clear - K3l K3r K6 K20; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K18 K20 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K20) | evalEk ZA ltac:(clear - HV35l HV35r K16l K16r K20 K21) | clear - K3l K3r K6 K20; lia | clear - K3l K3r K6 K20; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K16l K16r K20 K21) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | generalize K18; clear; intro; destruct (Z.ltb_spec0 ((vz_34 - ((((2 * (vz_36 / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) 1); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K18 K20 K21 HV35l HV35r K16l K16r) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K14l K14r K18 K20 K21 HV35l HV35r K16l K16r; lia | clear - HV34l HV34r K14l K14r K18 K20 K21 HV35l HV35r K16l K16r; lia | clear - HV34l HV34r K14l K14r K18 K20 K21 HV35l HV35r K16l K16r; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K18 K20 K21 HV35l HV35r K16l K16r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K18 K20 K21 HV35l HV35r K16l K16r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PpbLI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PpbLI.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 64) <= bv_unsigned a < (vz_2 - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> ~ (((vz_35 + vz_34) + 0) <= bv_unsigned a < ((vz_35 + vz_34) + 0) + 2) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PpbLI.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K21 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K20) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K20 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K14l K14r K18 K20 K21 HV35l HV35r K16l K16r) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K14l K14r K18 K20 K21 HV35l HV35r K16l K16r Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PpbLI.ps0) with 0x58a68 in Hms. change (SR.ps_regs PpbLI.ps0) with (map (fun i => (i, nth i PpbLI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PpbLI.ps0) with PpbLI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PpbLI.regs0 PpbLI.regs_out0 60 KS_pbLI KS_pbLI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PpbLI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PpbLI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbLI.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PpbLI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbLI.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PpbLI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K14l K14r K18 K20 K21 HV35l HV35r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K14l K14r K18 K20 K21 HV35l HV35r K16l K16r) | evalEk' ZA Hag ltac:(clear - K17l K17r) | byte_tac ltac:(clear - K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K20) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K14l K14r K18 K20 K21) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K20) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K9) | byte_tac ltac:(clear - HV33l HV33r K8l K8r K9) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11 K12l K12r K18) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K20) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K16l K16r K20 K21) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PpbLG := LibSegBs_pbLG_u.
Definition KS_pbLG : list nat := Eval vm_compute in (BG.kept_list 60 PpbLG.regs0 PpbLG.regs_out0).
Lemma KS_pbLG_ok : BG.kept_ok 60 PpbLG.regs0 PpbLG.regs_out0 KS_pbLG = true. Proof. vm_compute. reflexivity. Qed.
Lemma pbLG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 36%nat) -> Z.testbit (V 36%nat) 0 = true ->
  27 <= (V 36%nat) <= 134217729 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 67108864 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) (V 35%nat) ->
  4096 <= (V 35%nat) <= 140737488355328 -> 0 <= (bv_unsigned (getr R (reg 11))) <= 255 -> (((V 34%nat) - ((((2 * ((V 36%nat) / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) < 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58938 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_pbLG -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 363004
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 11)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 ((8 * (((4 * ((V 36%nat) / 2)) - 2) / 8)) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 12
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((8 * (((4 * ((V 36%nat) / 2)) - 2) / 8)) + 8)
        /\ getr R' (reg 20) = Z_to_bv 64 ((2 * ((V 36%nat) / 2)) - 1)
        /\ getr R' (reg 21) = Z_to_bv 64 (2 * ((V 36%nat) / 2))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 pvzI8 K9 K10 K11 pvzI9 K13 pvzI10 K15 pvzI11 pvzI12 K18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K17l; move K17l before pvzI12; pose proof (proj2 pvzI12) as K17r; move K17r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PpbLG.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PpbLG.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PpbLG.kn0).
  { unfold know_ok, PpbLG.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | byte_tac ltac:(clear - HV33l HV33r K8l K8r K9) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear; lia | rewrite (L5K.land1_bit0_true vz_33 ltac:(clear - HV33l HV33r K8l K8r K9; lia) K9); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV36l HV36r K11 K12l K12r K18) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K11 K12l K12r K18) | clear; lia | rewrite (L5K.land1_bit0_true vz_36 ltac:(clear - HV36l HV36r K11 K12l K12r K18; lia) K11); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K11 K12l K12r K18) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K18) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K18) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV35l HV35r K16l K16r) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | generalize K18; clear; intro; destruct (Z.ltb_spec0 ((vz_34 - ((((2 * (vz_36 / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) 1); lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PpbLG.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PpbLG.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 64) <= bv_unsigned a < (vz_2 - 64) + 64) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PpbLG.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PpbLG.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PpbLG.ps0) with (map (fun i => (i, nth i PpbLG.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PpbLG.ps0) with PpbLG.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PpbLG.regs0 PpbLG.regs_out0 60 KS_pbLG KS_pbLG_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PpbLG.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PpbLG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbLG.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PpbLG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbLG.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PpbLG.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PpbLG.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PpbLG.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PpbLG.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PpbLG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbLG.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PpbLG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbLG.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PpbLG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbLG.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PpbLG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbLG.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PpbLG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbLG.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PpbLG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbLG.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PpbLG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PpbGS := LibSegBs_pbGS_u.
Definition KS_pbGS : list nat := Eval vm_compute in (BG.kept_list 60 PpbGS.regs0 PpbGS.regs_out0).
Lemma KS_pbGS_ok : BG.kept_ok 60 PpbGS.regs0 PpbGS.regs_out0 KS_pbGS = true. Proof. vm_compute. reflexivity. Qed.
Lemma pbGS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) 44 ->
  0 <= (bv_unsigned (getr R (reg 11))) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58938 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_pbGS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 363004
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 11)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 48
        /\ getr R' (reg 12) = Z_to_bv 64 44
        /\ getr R' (reg 18) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 1)
        /\ getr R' (reg 19) = Z_to_bv 64 48
        /\ getr R' (reg 20) = Z_to_bv 64 22
        /\ getr R' (reg 21) = Z_to_bv 64 23
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 G2 pvzI2 K1 K2 pvzI3 K4 K5 K6 K7 pvzI4.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K3l; move K3l before pvzI3; pose proof (proj2 pvzI3) as K3r; move K3r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K8l; move K8l before pvzI4; pose proof (proj2 pvzI4) as K8r; move K8r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PpbGS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PpbGS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PpbGS.kn0).
  { unfold know_ok, PpbGS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | byte_tac ltac:(clear) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PpbGS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PpbGS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 64) <= bv_unsigned a < (vz_2 - 64) + 64) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PpbGS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PpbGS.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PpbGS.ps0) with (map (fun i => (i, nth i PpbGS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PpbGS.ps0) with PpbGS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PpbGS.regs0 PpbGS.regs_out0 60 KS_pbGS KS_pbGS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PpbGS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PpbGS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbGS.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PpbGS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbGS.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PpbGS.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PpbGS.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PpbGS.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PpbGS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PpbGS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbGS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PpbGS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbGS.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PpbGS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbGS.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PpbGS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbGS.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PpbGS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbGS.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PpbGS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PpbN := LibSegBs_pbN_u.
Definition KS_pbN : list nat := Eval vm_compute in (BG.kept_list 60 PpbN.regs0 PpbN.regs_out0).
Lemma KS_pbN_ok : BG.kept_ok 60 PpbN.regs0 PpbN.regs_out0 KS_pbN = true. Proof. vm_compute. reflexivity. Qed.
Lemma pbN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 56%nat) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 41%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 39%nat) -> getr R (reg 21) = Z_to_bv 64 (V 40%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x589fc M) (st fx' R' 0xab884 M')
        /\ (forall x, In x KS_pbN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 363020
        /\ getr R' (reg 11) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G9 G10 G18 G19 G20 G21 pvzI17 K1 K2 pvzI18 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV44l; move HV44l before pvzI8; pose proof (proj2 pvzI8) as HV44r; move HV44r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV45l; move HV45l before pvzI9; pose proof (proj2 pvzI9) as HV45r; move HV45r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV46l; move HV46l before pvzI10; pose proof (proj2 pvzI10) as HV46r; move HV46r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV47l; move HV47l before pvzI11; pose proof (proj2 pvzI11) as HV47r; move HV47r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV48l; move HV48l before pvzI12; pose proof (proj2 pvzI12) as HV48r; move HV48r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV49l; move HV49l before pvzI13; pose proof (proj2 pvzI13) as HV49r; move HV49r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV50l; move HV50l before pvzI14; pose proof (proj2 pvzI14) as HV50r; move HV50r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV51l; move HV51l before pvzI15; pose proof (proj2 pvzI15) as HV51r; move HV51r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV56l; move HV56l before pvzI16; pose proof (proj2 pvzI16) as HV56r; move HV56r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K0l; move K0l before pvzI17; pose proof (proj2 pvzI17) as K0r; move K0r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K3l; move K3l before pvzI18; pose proof (proj2 pvzI18) as K3r; move K3r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PpbN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PpbN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PpbN.kn0).
  { unfold know_ok, PpbN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K14]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PpbN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PpbN.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PpbN.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PpbN.ps0) with 0xab884 in Hms. change (SR.ps_regs PpbN.ps0) with (map (fun i => (i, nth i PpbN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PpbN.ps0) with PpbN.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PpbN.regs0 PpbN.regs_out0 60 KS_pbN KS_pbN_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PpbN.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PpbN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbN.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PpbN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbN.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PpbN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PpbN.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PpbN.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PpbTS := LibSegBs_pbTS_u.
Definition KS_pbTS : list nat := Eval vm_compute in (BG.kept_list 60 PpbTS.regs0 PpbTS.regs_out0).
Lemma KS_pbTS_ok : BG.kept_ok 60 PpbTS.regs0 PpbTS.regs_out0 KS_pbTS = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma pbTS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 56%nat) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 (V 41%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 39%nat) -> getr R (reg 21) = Z_to_bv 64 23 -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 0 <= (V 56%nat) <= 255 ->
  4096 <= (V 37%nat) <= 140737488355328 -> 0 <= (V 39%nat) <= 67108864 -> 26 <= (V 38%nat) <= 134217729 -> L5.writable RSEGS M ((V 37%nat) + (V 39%nat)) 2 ->
  (((V 37%nat) + (V 39%nat)) + 2 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 37%nat) + (V 39%nat))) -> (((V 37%nat) + (V 39%nat)) + 2 <= ((V 2%nat) - 64) \/ ((V 2%nat) - 64) + 64 <= ((V 37%nat) + (V 39%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> ~ ((((V 37%nat) + (V 39%nat)) + 0) <= bv_unsigned a < (((V 37%nat) + (V 39%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> ~ ((((V 37%nat) + (V 39%nat)) + 0) <= i < (((V 37%nat) + (V 39%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58a0c M) (st fx' R' 0x58a68 M')
        /\ (forall x, In x KS_pbTS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) + (V 39%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 39%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ L5.u8_at RSEGS M' (((V 37%nat) + (V 39%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 37%nat) + (V 39%nat)) (V 56%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) ((V 39%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' (V 10%nat) ((2 * ((V 38%nat) / 2)) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI17 K1 K2 pvzI18 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 pvzI19 pvzI20 pvzI21 pvzI22 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV50l; move HV50l before pvzI13; pose proof (proj2 pvzI13) as HV50r; move HV50r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV51l; move HV51l before pvzI14; pose proof (proj2 pvzI14) as HV51r; move HV51r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV54l; move HV54l before pvzI15; pose proof (proj2 pvzI15) as HV54r; move HV54r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV56l; move HV56l before pvzI16; pose proof (proj2 pvzI16) as HV56r; move HV56r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K0l; move K0l before pvzI17; pose proof (proj2 pvzI17) as K0r; move K0r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K3l; move K3l before pvzI18; pose proof (proj2 pvzI18) as K3r; move K3r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K15l; move K15l before pvzI19; pose proof (proj2 pvzI19) as K15r; move K15r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K16l; move K16l before pvzI20; pose proof (proj2 pvzI20) as K16r; move K16r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K17l; move K17l before pvzI21; pose proof (proj2 pvzI21) as K17r; move K17r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 54%nat => Z_to_bv 64 vz_54 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 54%nat => vz_54 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PpbTS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PpbTS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PpbTS.kn0).
  { unfold know_ok, PpbTS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K20) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K20) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K20; lia | clear - HV10l HV10r K3l K3r K6 K20; lia | clear - HV10l HV10r K3l K3r K6 K20; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K16l K16r K20 K21) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K20 K21) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r; lia | clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r; lia | clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PpbTS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PpbTS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 0) <= bv_unsigned a < (vz_10 + 0) + 24) -> ~ (((vz_37 + vz_39) + 0) <= bv_unsigned a < ((vz_37 + vz_39) + 0) + 2) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PpbTS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K20 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PpbTS.ps0) with 0x58a68 in Hms. change (SR.ps_regs PpbTS.ps0) with (map (fun i => (i, nth i PpbTS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PpbTS.ps0) with PpbTS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PpbTS.regs0 PpbTS.regs_out0 60 KS_pbTS KS_pbTS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PpbTS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PpbTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbTS.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PpbTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbTS.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PpbTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbTS.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PpbTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbTS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PpbTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbTS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PpbTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbTS.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PpbTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbTS.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PpbTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbTS.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PpbTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbTS.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PpbTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbTS.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PpbTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r) | evalEk' ZA Hag ltac:(clear - HV56l HV56r K15l K15r) | byte_tac ltac:(clear - HV56l HV56r K15l K15r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K17l K17r K20 K21) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K16l K16r K20 K21) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K18l K18r) | clear; lia]. 
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PpbD := LibSegBs_pbD_u.
Definition KS_pbD : list nat := Eval vm_compute in (BG.kept_list 60 PpbD.regs0 PpbD.regs_out0).
Lemma KS_pbD_ok : BG.kept_ok 60 PpbD.regs0 PpbD.regs_out0 KS_pbD = true. Proof. vm_compute. reflexivity. Qed.
Lemma pbD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 56%nat) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 (V 41%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 39%nat) -> getr R (reg 21) = Z_to_bv 64 (V 40%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 26 <= (V 40%nat) <= 134217729 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58a0c M) (st fx' R' 0x56720 M')
        /\ (forall x, In x KS_pbD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 363040
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI18 K1 K2 pvzI19 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 pvzI20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV44l; move HV44l before pvzI8; pose proof (proj2 pvzI8) as HV44r; move HV44r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV45l; move HV45l before pvzI9; pose proof (proj2 pvzI9) as HV45r; move HV45r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV46l; move HV46l before pvzI10; pose proof (proj2 pvzI10) as HV46r; move HV46r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV47l; move HV47l before pvzI11; pose proof (proj2 pvzI11) as HV47r; move HV47r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV48l; move HV48l before pvzI12; pose proof (proj2 pvzI12) as HV48r; move HV48r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV49l; move HV49l before pvzI13; pose proof (proj2 pvzI13) as HV49r; move HV49r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV50l; move HV50l before pvzI14; pose proof (proj2 pvzI14) as HV50r; move HV50r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV51l; move HV51l before pvzI15; pose proof (proj2 pvzI15) as HV51r; move HV51r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV54l; move HV54l before pvzI16; pose proof (proj2 pvzI16) as HV54r; move HV54r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV56l; move HV56l before pvzI17; pose proof (proj2 pvzI17) as HV56r; move HV56r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K15l; move K15l before pvzI20; pose proof (proj2 pvzI20) as K15r; move K15r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 54%nat => Z_to_bv 64 vz_54 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 54%nat => vz_54 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PpbD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PpbD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PpbD.kn0).
  { unfold know_ok, PpbD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PpbD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PpbD.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PpbD.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PpbD.ps0) with 0x56720 in Hms. change (SR.ps_regs PpbD.ps0) with (map (fun i => (i, nth i PpbD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PpbD.ps0) with PpbD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PpbD.regs0 PpbD.regs_out0 60 KS_pbD KS_pbD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PpbD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PpbD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PpbD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PpbD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PpbD.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PpbT := LibSegBs_pbT_u.
Definition KS_pbT : list nat := Eval vm_compute in (BG.kept_list 60 PpbT.regs0 PpbT.regs_out0).
Lemma KS_pbT_ok : BG.kept_ok 60 PpbT.regs0 PpbT.regs_out0 KS_pbT = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma pbT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 56%nat) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 (V 41%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 39%nat) -> getr R (reg 21) = Z_to_bv 64 (V 40%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 0 <= (V 56%nat) <= 255 ->
  4096 <= (V 37%nat) <= 140737488355328 -> 0 <= (V 39%nat) <= 67108864 -> 26 <= (V 38%nat) <= 134217729 -> L5.writable RSEGS M ((V 37%nat) + (V 39%nat)) 2 ->
  (((V 37%nat) + (V 39%nat)) + 2 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 37%nat) + (V 39%nat))) -> (((V 37%nat) + (V 39%nat)) + 2 <= ((V 2%nat) - 64) \/ ((V 2%nat) - 64) + 64 <= ((V 37%nat) + (V 39%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> ~ ((((V 37%nat) + (V 39%nat)) + 0) <= bv_unsigned a < (((V 37%nat) + (V 39%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> ~ ((((V 37%nat) + (V 39%nat)) + 0) <= i < (((V 37%nat) + (V 39%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58a20 M) (st fx' R' 0x58a68 M')
        /\ (forall x, In x KS_pbT -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) + (V 39%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 39%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ L5.u8_at RSEGS M' (((V 37%nat) + (V 39%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 37%nat) + (V 39%nat)) (V 56%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) ((V 39%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' (V 10%nat) ((2 * ((V 38%nat) / 2)) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI18 K1 K2 pvzI19 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 pvzI20 pvzI21 pvzI22 pvzI23 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV44l; move HV44l before pvzI8; pose proof (proj2 pvzI8) as HV44r; move HV44r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV45l; move HV45l before pvzI9; pose proof (proj2 pvzI9) as HV45r; move HV45r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV46l; move HV46l before pvzI10; pose proof (proj2 pvzI10) as HV46r; move HV46r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV47l; move HV47l before pvzI11; pose proof (proj2 pvzI11) as HV47r; move HV47r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV48l; move HV48l before pvzI12; pose proof (proj2 pvzI12) as HV48r; move HV48r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV49l; move HV49l before pvzI13; pose proof (proj2 pvzI13) as HV49r; move HV49r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV50l; move HV50l before pvzI14; pose proof (proj2 pvzI14) as HV50r; move HV50r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV51l; move HV51l before pvzI15; pose proof (proj2 pvzI15) as HV51r; move HV51r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV55l; move HV55l before pvzI16; pose proof (proj2 pvzI16) as HV55r; move HV55r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV56l; move HV56l before pvzI17; pose proof (proj2 pvzI17) as HV56r; move HV56r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K15l; move K15l before pvzI20; pose proof (proj2 pvzI20) as K15r; move K15r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K17l; move K17l before pvzI22; pose proof (proj2 pvzI22) as K17r; move K17r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K18l; move K18l before pvzI23; pose proof (proj2 pvzI23) as K18r; move K18r before pvzI23; clear pvzI23.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 55%nat => vz_55 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PpbT.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PpbT.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PpbT.kn0).
  { unfold know_ok, PpbT.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K20) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K20) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K20; lia | clear - HV10l HV10r K3l K3r K6 K20; lia | clear - HV10l HV10r K3l K3r K6 K20; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K6 K21; lia | clear - HV2l HV2r K0l K0r K6 K21; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K16l K16r K20 K21) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K20 K21) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r; lia | clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r; lia | clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PpbT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PpbT.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 0) <= bv_unsigned a < (vz_10 + 0) + 24) -> ~ (((vz_37 + vz_39) + 0) <= bv_unsigned a < ((vz_37 + vz_39) + 0) + 2) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PpbT.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K20 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PpbT.ps0) with 0x58a68 in Hms. change (SR.ps_regs PpbT.ps0) with (map (fun i => (i, nth i PpbT.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PpbT.ps0) with PpbT.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PpbT.regs0 PpbT.regs_out0 60 KS_pbT KS_pbT_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PpbT.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PpbT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbT.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PpbT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbT.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PpbT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbT.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PpbT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbT.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PpbT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbT.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PpbT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbT.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PpbT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbT.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PpbT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbT.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PpbT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbT.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PpbT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpbT.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PpbT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K16l K16r K20 K21 HV39l HV39r K17l K17r) | evalEk' ZA Hag ltac:(clear - HV56l HV56r K15l K15r) | byte_tac ltac:(clear - HV56l HV56r K15l K15r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K17l K17r K20 K21) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K16l K16r K20 K21) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K20) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K18l K18r) | clear; lia]. 
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

End PNSPBP.
