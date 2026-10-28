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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_icA_u LibSegBs_icB_u LibSegBs_icCs1_u LibSegBs_icCs2_u LibSegBs_icCl1a_u LibSegBs_icCl1b_u LibSegBs_icCl2_u LibSegBs_icCl3_u LibSegBs_icCl4_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMISP.
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
Module PicA := LibSegBs_icA_u.
Definition KS_icA : list nat := Eval vm_compute in (BG.kept_list 52 PicA.regs0 PicA.regs_out0).
Lemma KS_icA_ok : BG.kept_ok 52 PicA.regs0 PicA.regs_out0 KS_icA = true. Proof. vm_compute. reflexivity. Qed.
Lemma icA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 33%nat) + (V 39%nat)) -> getr R (reg 12) = Z_to_bv 64 8 ->
  140735332483280 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 208) 208 -> 140735332483280 <= (V 33%nat) <= 140737488355056 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 208) + 208 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 208)) -> L5.writable RSEGS M (V 33%nat) 272 -> 272 <= (V 39%nat) <= 8388608 ->
  aligned (V 39%nat) 8 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 16) -> ~ (((V 33%nat) + 120) <= bv_unsigned a < ((V 33%nat) + 120) + 136) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 16) -> ~ (((V 33%nat) + 120) <= i < ((V 33%nat) + 120) + 136) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x349d4 M) (st fx' R' 0x81bdc M')
        /\ (forall x, In x KS_icA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 215644
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 39%nat))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 168)
        /\ getr R' (reg 18) = Z_to_bv 64 8
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 33%nat) + 120)
        /\ getr R' (reg 21) = Z_to_bv 64 740848
        /\ getr R' (reg 22) = Z_to_bv 64 740832
        /\ getr R' (reg 23) = Z_to_bv 64 740768
        /\ L5KA.zeros_at M' ((V 33%nat) + 176) 80
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 152) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 144) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 136) 6
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 128) 4098
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 160) ((V 33%nat) + 16)
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 156) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 120) 740944
        /\ L5.u64_at RSEGS M' (V 33%nat) 740904
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 168) 0
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
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 G12 pvzI4 K1 K2 pvzI5 K4 K5 K6 pvzI6 K8 K9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV39l; move HV39l before pvzI3; pose proof (proj2 pvzI3) as HV39r; move HV39r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K7l; move K7l before pvzI6; pose proof (proj2 pvzI6) as K7r; move K7r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PicA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PicA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PicA.kn0).
  { unfold know_ok, PicA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PicA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PicA.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 208) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 16) -> ~ ((vz_33 + 120) <= bv_unsigned a < (vz_33 + 120) + 136) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PicA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PicA.ps0) with 0x81bdc in Hms. change (SR.ps_regs PicA.ps0) with (map (fun i => (i, nth i PicA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PicA.ps0) with PicA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PicA.regs0 PicA.regs_out0 52 KS_icA KS_icA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PicA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PicA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PicA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PicA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PicA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PicA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PicA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PicA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PicA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PicA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicA.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PicA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicA.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PicA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PicB := LibSegBs_icB_u.
Definition KS_icB : list nat := Eval vm_compute in (BG.kept_list 52 PicB.regs0 PicB.regs_out0).
Lemma KS_icB_ok : BG.kept_ok 52 PicB.regs0 PicB.regs_out0 KS_icB = true. Proof. vm_compute. reflexivity. Qed.
Lemma icB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 39%nat)) -> getr R (reg 18) = Z_to_bv 64 8 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 120) -> getr R (reg 21) = Z_to_bv 64 740848 -> getr R (reg 22) = Z_to_bv 64 740832 -> getr R (reg 23) = Z_to_bv 64 740768 ->
  140735332483280 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 208) 208 -> 140735332483280 <= (V 33%nat) <= 140737488355056 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 208) + 208 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 208)) -> L5.writable RSEGS M (V 33%nat) 272 -> 272 <= (V 39%nat) <= 8388608 ->
  aligned (V 39%nat) 8 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 64) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 8) -> ~ (((V 33%nat) + 16) <= bv_unsigned a < ((V 33%nat) + 16) + 8) -> ~ (((V 33%nat) + 120) <= bv_unsigned a < ((V 33%nat) + 120) + 8) -> ~ (((V 33%nat) + 256) <= bv_unsigned a < ((V 33%nat) + 256) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 64) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 8) -> ~ (((V 33%nat) + 16) <= i < ((V 33%nat) + 16) + 8) -> ~ (((V 33%nat) + 120) <= i < ((V 33%nat) + 120) + 8) -> ~ (((V 33%nat) + 256) <= i < ((V 33%nat) + 256) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x34a5c M) (st fx' R' 0x81bdc M')
        /\ (forall x, In x KS_icB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 221700
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + (V 39%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 8
        /\ getr R' (reg 19) = Z_to_bv 64 8
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 33%nat) + (V 39%nat))
        /\ getr R' (reg 21) = Z_to_bv 64 740424
        /\ getr R' (reg 23) = Z_to_bv 64 740792
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) 740424
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 740848
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) ((V 33%nat) + (V 39%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) 215696
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 120) 740832
        /\ L5.u64_at RSEGS M' (V 33%nat) 740792
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 266) 255
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 265) 255
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 264) 255
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 256) 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 267) 255).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 G18 G19 G20 G21 G22 G23 pvzI4 K1 K2 pvzI5 K4 K5 K6 pvzI6 K8 K9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV39l; move HV39l before pvzI3; pose proof (proj2 pvzI3) as HV39r; move HV39r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K7l; move K7l before pvzI6; pose proof (proj2 pvzI6) as K7r; move K7r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PicB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PicB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PicB.kn0).
  { unfold know_ok, PicB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PicB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PicB.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 144) <= bv_unsigned a < (vz_2 - 144) + 64) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 8) -> ~ ((vz_33 + 16) <= bv_unsigned a < (vz_33 + 16) + 8) -> ~ ((vz_33 + 120) <= bv_unsigned a < (vz_33 + 120) + 8) -> ~ ((vz_33 + 256) <= bv_unsigned a < (vz_33 + 256) + 12) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PicB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PicB.ps0) with 0x81bdc in Hms. change (SR.ps_regs PicB.ps0) with (map (fun i => (i, nth i PicB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PicB.ps0) with PicB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PicB.regs0 PicB.regs_out0 52 KS_icB KS_icB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PicB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PicB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicB.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PicB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicB.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PicB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicB.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PicB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PicB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PicB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PicB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicB.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PicB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicB.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PicB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PicB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PicB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PicCs1 := LibSegBs_icCs1_u.
Definition KS_icCs1 : list nat := Eval vm_compute in (BG.kept_list 52 PicCs1.regs0 PicCs1.regs_out0).
Lemma KS_icCs1_ok : BG.kept_ok 52 PicCs1.regs0 PicCs1.regs_out0 KS_icCs1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma icCs1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 19) = Z_to_bv 64 8 -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + (V 39%nat)) -> getr R (reg 21) = Z_to_bv 64 740424 ->
  140735332483280 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 208) 208 -> 140735332483280 <= (V 33%nat) <= 140737488355056 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 208) + 208 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 208)) -> L5.writable RSEGS M (V 33%nat) 272 -> 272 <= (V 39%nat) <= 8388608 ->
  aligned (V 39%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u8_at RSEGS M ((V 33%nat) + (V 39%nat)) (V 38%nat) -> 0 <= (V 38%nat) <= 255 ->
  Z.testbit (V 38%nat) 0 = false -> L5.u64_at RSEGS M ((V 33%nat) + (V 39%nat)) (V 35%nat) -> L5.u64_at RSEGS M (((V 33%nat) + (V 39%nat)) + 8) (V 36%nat) -> L5.u64_at RSEGS M (((V 33%nat) + (V 39%nat)) + 16) (V 37%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 16) <= bv_unsigned a < ((V 33%nat) + 16) + 8) -> ~ (((V 33%nat) + 32) <= bv_unsigned a < ((V 33%nat) + 32) + 84) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 16) <= i < ((V 33%nat) + 16) + 8) -> ~ (((V 33%nat) + 32) <= i < ((V 33%nat) + 32) + 84) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36204 M) (st fx' R' 0x36248 M')
        /\ (forall x, In x KS_icCs1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 221768
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 80) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 96) (V 37%nat)
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 112) 8
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 104) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) 740552
        /\ L5KA.zeros_at M' ((V 33%nat) + 32) 48).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G19 G20 G21 pvzI8 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 pvzI11 K12 K13 K14 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PicCs1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PicCs1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PicCs1.kn0).
  { unfold know_ok, PicCs1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K12) | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | byte_tac ltac:(clear - HV38l HV38r K11l K11r K12) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K12) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K12) | clear; lia | rewrite (L5K.land1_bit0_false vz_38 ltac:(clear - HV38l HV38r K11l K11r K12; lia) K12); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | exactA K15]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PicCs1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PicCs1.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 16) <= bv_unsigned a < (vz_33 + 16) + 8) -> ~ ((vz_33 + 32) <= bv_unsigned a < (vz_33 + 32) + 84) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PicCs1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PicCs1.ps0) with 0x36248 in Hms. change (SR.ps_regs PicCs1.ps0) with (map (fun i => (i, nth i PicCs1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PicCs1.ps0) with PicCs1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PicCs1.regs0 PicCs1.regs_out0 52 KS_icCs1 KS_icCs1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PicCs1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PicCs1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PicCs1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PicCs1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PicCs1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PicCs1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PicCs1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PicCs1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PicCs2 := LibSegBs_icCs2_u.
Definition KS_icCs2 : list nat := Eval vm_compute in (BG.kept_list 52 PicCs2.regs0 PicCs2.regs_out0).
Lemma KS_icCs2_ok : BG.kept_ok 52 PicCs2.regs0 PicCs2.regs_out0 KS_icCs2 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma icCs2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 16) ->
  140735332483280 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 208) 208 -> 140735332483280 <= (V 33%nat) <= 140737488355056 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 208) + 208 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 208)) -> L5.writable RSEGS M (V 33%nat) 272 -> 272 <= (V 39%nat) <= 8388608 ->
  aligned (V 39%nat) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 88) 215696 -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 33%nat) + (V 39%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 112) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 120) -> L5.u64_at RSEGS M ((V 2%nat) - 136) 740848 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 51%nat) -> L5.u8_at RSEGS M ((V 33%nat) + 80) (V 38%nat) -> 0 <= (V 38%nat) <= 44 -> Z.testbit (V 38%nat) 0 = false ->
  L5.u32_at RSEGS M ((V 33%nat) + 112) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 48) -> ~ (((V 33%nat) + 32) <= bv_unsigned a < ((V 33%nat) + 32) + 24) -> ~ (((V 33%nat) + 104) <= bv_unsigned a < ((V 33%nat) + 104) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 48) -> ~ (((V 33%nat) + 32) <= i < ((V 33%nat) + 32) + 24) -> ~ (((V 33%nat) + 104) <= i < ((V 33%nat) + 104) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36248 M) (st fx' R' 0x34ab8 M')
        /\ (forall x, In x KS_icCs2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 33%nat) + ((V 38%nat) / 2)) + 81)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 104) (((V 33%nat) + ((V 38%nat) / 2)) + 81)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 48) (((V 33%nat) + ((V 38%nat) / 2)) + 81)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 40) ((V 33%nat) + 81)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 32) ((V 33%nat) + 81)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 pvzI14 K1 K2 pvzI15 K4 K5 K6 pvzI16 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 pvzI17 K27 K28.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV39l; move HV39l before pvzI4; pose proof (proj2 pvzI4) as HV39r; move HV39r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV49l; move HV49l before pvzI11; pose proof (proj2 pvzI11) as HV49r; move HV49r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV50l; move HV50l before pvzI12; pose proof (proj2 pvzI12) as HV50r; move HV50r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV51l; move HV51l before pvzI13; pose proof (proj2 pvzI13) as HV51r; move HV51r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K3l; move K3l before pvzI15; pose proof (proj2 pvzI15) as K3r; move K3r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K7l; move K7l before pvzI16; pose proof (proj2 pvzI16) as K7r; move K7r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K26l; move K26l before pvzI17; pose proof (proj2 pvzI17) as K26r; move K26r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 39%nat => vz_39 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PicCs2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PicCs2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PicCs2.kn0).
  { unfold know_ok, PicCs2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV38l HV38r K26l K26r K27) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | byte_tac ltac:(clear - HV38l HV38r K26l K26r K27) | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K26l K26r K27) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K26l K26r K27) | clear; lia | rewrite (L5K.land1_bit0_false vz_38 ltac:(clear - HV38l HV38r K26l K26r K27; lia) K27); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K28]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PicCs2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PicCs2.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 48) -> ~ ((vz_33 + 32) <= bv_unsigned a < (vz_33 + 32) + 24) -> ~ ((vz_33 + 104) <= bv_unsigned a < (vz_33 + 104) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PicCs2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PicCs2.ps0) with 0x34ab8 in Hms. change (SR.ps_regs PicCs2.ps0) with (map (fun i => (i, nth i PicCs2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PicCs2.ps0) with PicCs2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PicCs2.regs0 PicCs2.regs_out0 52 KS_icCs2 KS_icCs2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCs2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 HV38l HV38r K26l K26r K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 HV38l HV38r K26l K26r K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. 
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PicCl1a := LibSegBs_icCl1a_u.
Definition KS_icCl1a : list nat := Eval vm_compute in (BG.kept_list 52 PicCl1a.regs0 PicCl1a.regs_out0).
Lemma KS_icCl1a_ok : BG.kept_ok 52 PicCl1a.regs0 PicCl1a.regs_out0 KS_icCl1a = true. Proof. vm_compute. reflexivity. Qed.
Lemma icCl1a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 19) = Z_to_bv 64 8 -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + (V 39%nat)) -> getr R (reg 21) = Z_to_bv 64 740424 ->
  140735332483280 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 208) 208 -> 140735332483280 <= (V 33%nat) <= 140737488355056 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 208) + 208 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 208)) -> L5.writable RSEGS M (V 33%nat) 272 -> 272 <= (V 39%nat) <= 8388608 ->
  aligned (V 39%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u8_at RSEGS M ((V 33%nat) + (V 39%nat)) (V 38%nat) -> 0 <= (V 38%nat) <= 255 ->
  Z.testbit (V 38%nat) 0 = true -> L5.u64_at RSEGS M (((V 33%nat) + (V 39%nat)) + 8) (V 40%nat) -> L5.u64_at RSEGS M (((V 33%nat) + (V 39%nat)) + 16) (V 36%nat) -> 23 <= (V 40%nat) <= 44 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 48) -> ~ (((V 33%nat) + 16) <= bv_unsigned a < ((V 33%nat) + 16) + 8) -> ~ (((V 33%nat) + 32) <= bv_unsigned a < ((V 33%nat) + 32) + 84) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 48) -> ~ (((V 33%nat) + 16) <= i < ((V 33%nat) + 16) + 8) -> ~ (((V 33%nat) + 32) <= i < ((V 33%nat) + 32) + 84) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36204 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_icCl1a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 364116
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 10) = Z_to_bv 64 48
        /\ getr R' (reg 11) = Z_to_bv 64 44
        /\ getr R' (reg 12) = Z_to_bv 64 30
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 47
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 33%nat) + (V 39%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 33%nat) + 80)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 221768
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 112) 8
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 104) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 96) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 88) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 80) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) 740552
        /\ L5KA.zeros_at M' ((V 33%nat) + 32) 48).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G19 G20 G21 pvzI7 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8 K9 K10 pvzI10 K12 K13 K14 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K11l; move K11l before pvzI10; pose proof (proj2 pvzI10) as K11r; move K11r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K15l; move K15l before pvzI11; pose proof (proj2 pvzI11) as K15r; move K15r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PicCl1a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PicCl1a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PicCl1a.kn0).
  { unfold know_ok, PicCl1a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K12) | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | byte_tac ltac:(clear - HV38l HV38r K11l K11r K12) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K12) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K12) | clear; lia | rewrite (L5K.land1_bit0_true vz_38 ltac:(clear - HV38l HV38r K11l K11r K12; lia) K12); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | evalEk ZA ltac:(clear - HV40l HV40r K15l K15r) | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PicCl1a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PicCl1a.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 48) -> ~ ((vz_33 + 16) <= bv_unsigned a < (vz_33 + 16) + 8) -> ~ ((vz_33 + 32) <= bv_unsigned a < (vz_33 + 32) + 84) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PicCl1a.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PicCl1a.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PicCl1a.ps0) with (map (fun i => (i, nth i PicCl1a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PicCl1a.ps0) with PicCl1a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PicCl1a.regs0 PicCl1a.regs_out0 52 KS_icCl1a KS_icCl1a_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PicCl1a.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1a.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1a.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1a.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1a.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1a.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1a.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1a.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1a.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1a.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1a.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PicCl1b := LibSegBs_icCl1b_u.
Definition KS_icCl1b : list nat := Eval vm_compute in (BG.kept_list 52 PicCl1b.regs0 PicCl1b.regs_out0).
Lemma KS_icCl1b_ok : BG.kept_ok 52 PicCl1b.regs0 PicCl1b.regs_out0 KS_icCl1b = true. Proof. vm_compute. reflexivity. Qed.
Lemma icCl1b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 19) = Z_to_bv 64 8 -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + (V 39%nat)) -> getr R (reg 21) = Z_to_bv 64 740424 ->
  140735332483280 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 208) 208 -> 140735332483280 <= (V 33%nat) <= 140737488355056 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 208) + 208 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 208)) -> L5.writable RSEGS M (V 33%nat) 272 -> 272 <= (V 39%nat) <= 8388608 ->
  aligned (V 39%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u8_at RSEGS M ((V 33%nat) + (V 39%nat)) (V 38%nat) -> 0 <= (V 38%nat) <= 255 ->
  Z.testbit (V 38%nat) 0 = true -> L5.u64_at RSEGS M (((V 33%nat) + (V 39%nat)) + 8) (V 40%nat) -> L5.u64_at RSEGS M (((V 33%nat) + (V 39%nat)) + 16) (V 36%nat) -> 45 <= (V 40%nat) <= 67108863 ->
  47 <= (Z.lor (V 40%nat) 7) <= 67108871 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 48) -> ~ (((V 33%nat) + 16) <= bv_unsigned a < ((V 33%nat) + 16) + 8) -> ~ (((V 33%nat) + 32) <= bv_unsigned a < ((V 33%nat) + 32) + 84) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 48) -> ~ (((V 33%nat) + 16) <= i < ((V 33%nat) + 16) + 8) -> ~ (((V 33%nat) + 32) <= i < ((V 33%nat) + 32) + 84) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36204 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_icCl1b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 364116
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 10) = Z_to_bv 64 ((8 * ((V 40%nat) / 8)) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 44
        /\ getr R' (reg 12) = Z_to_bv 64 30
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((8 * ((V 40%nat) / 8)) + 7)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 33%nat) + (V 39%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 33%nat) + 80)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 221768
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 112) 8
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 104) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 96) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 88) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 80) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) 740552
        /\ L5KA.zeros_at M' ((V 33%nat) + 32) 48).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G19 G20 G21 pvzI7 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8 K9 K10 pvzI10 K12 K13 K14 pvzI11 K16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K11l; move K11l before pvzI10; pose proof (proj2 pvzI10) as K11r; move K11r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K15l; move K15l before pvzI11; pose proof (proj2 pvzI11) as K15r; move K15r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PicCl1b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PicCl1b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PicCl1b.kn0).
  { unfold know_ok, PicCl1b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K12) | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | byte_tac ltac:(clear - HV38l HV38r K11l K11r K12) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K12) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K12) | clear; lia | rewrite (L5K.land1_bit0_true vz_38 ltac:(clear - HV38l HV38r K11l K11r K12; lia) K12); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | evalEk ZA ltac:(clear - HV40l HV40r K15l K15r) | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K16]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PicCl1b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PicCl1b.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 48) -> ~ ((vz_33 + 16) <= bv_unsigned a < (vz_33 + 16) + 8) -> ~ ((vz_33 + 32) <= bv_unsigned a < (vz_33 + 32) + 84) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PicCl1b.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PicCl1b.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PicCl1b.ps0) with (map (fun i => (i, nth i PicCl1b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PicCl1b.ps0) with PicCl1b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PicCl1b.regs0 PicCl1b.regs_out0 52 KS_icCl1b KS_icCl1b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PicCl1b.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1b.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1b.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1b.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1b.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1b.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1b.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1b.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1b.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl1b.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PicCl2 := LibSegBs_icCl2_u.
Definition KS_icCl2 : list nat := Eval vm_compute in (BG.kept_list 52 PicCl2.regs0 PicCl2.regs_out0).
Lemma KS_icCl2_ok : BG.kept_ok 52 PicCl2.regs0 PicCl2.regs_out0 KS_icCl2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma icCl2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58e54 M) (st fx' R' 0xab480 M')
        /\ (forall x, In x KS_icCl2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 364132
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 41%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G10 G19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PicCl2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PicCl2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PicCl2.kn0).
  { unfold know_ok, PicCl2.kn0.
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PicCl2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PicCl2.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PicCl2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PicCl2.ps0) with 0xab480 in Hms. change (SR.ps_regs PicCl2.ps0) with (map (fun i => (i, nth i PicCl2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PicCl2.ps0) with PicCl2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PicCl2.regs0 PicCl2.regs_out0 52 KS_icCl2 KS_icCl2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PicCl2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PicCl2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PicCl2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PicCl2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PicCl2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PicCl2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PicCl3 := LibSegBs_icCl3_u.
Definition KS_icCl3 : list nat := Eval vm_compute in (BG.kept_list 52 PicCl3.regs0 PicCl3.regs_out0).
Lemma KS_icCl3_ok : BG.kept_ok 52 PicCl3.regs0 PicCl3.regs_out0 KS_icCl3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma icCl3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 80) -> getr R (reg 18) = Z_to_bv 64 (V 41%nat) -> getr R (reg 20) = Z_to_bv 64 (V 42%nat) ->
  140735332483280 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 208) 208 -> 140735332483280 <= (V 33%nat) <= 140737488355056 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 208) + 208 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 208)) -> L5.writable RSEGS M (V 33%nat) 272 -> 272 <= (V 39%nat) <= 8388608 ->
  aligned (V 39%nat) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 152) 221768 -> L5.u64_at RSEGS M ((V 2%nat) - 160) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 33%nat) + 24) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 80) -> L5.u64_at RSEGS M ((V 2%nat) - 184) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 192) ((V 33%nat) + (V 39%nat)) -> 4096 <= (V 41%nat) <= 140737488355328 ->
  23 <= (V 40%nat) <= 67108863 -> 47 <= (V 42%nat) <= 67108871 -> L5.writable RSEGS M ((V 41%nat) + (V 40%nat)) 1 -> (((V 2%nat) - 208) + 208 <= ((V 41%nat) + (V 40%nat)) \/ ((V 41%nat) + (V 40%nat)) + 1 <= ((V 2%nat) - 208)) ->
  ((V 33%nat) + 272 <= ((V 41%nat) + (V 40%nat)) \/ ((V 41%nat) + (V 40%nat)) + 1 <= (V 33%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 80) <= bv_unsigned a < ((V 33%nat) + 80) + 24) -> ~ ((((V 41%nat) + (V 40%nat)) + 0) <= bv_unsigned a < (((V 41%nat) + (V 40%nat)) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 80) <= i < ((V 33%nat) + 80) + 24) -> ~ ((((V 41%nat) + (V 40%nat)) + 0) <= i < (((V 41%nat) + (V 40%nat)) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58e64 M) (st fx' R' 0x36248 M')
        /\ (forall x, In x KS_icCl3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 221768
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 19) = Z_to_bv 64 8
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 33%nat) + (V 39%nat))
        /\ L5.u8_at RSEGS M' ((V 40%nat) + (V 41%nat)) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 96) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 80) ((V 42%nat) + 2)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G20 pvzI7 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8 K9 K10 K11 K12 K13 K14 pvzI10 pvzI11 pvzI12 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV39l; move HV39l before pvzI3; pose proof (proj2 pvzI3) as HV39r; move HV39r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K15l; move K15l before pvzI10; pose proof (proj2 pvzI10) as K15r; move K15r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K17l; move K17l before pvzI12; pose proof (proj2 pvzI12) as K17r; move K17r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PicCl3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PicCl3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PicCl3.kn0).
  { unfold know_ok, PicCl3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K19) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K19) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K19) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K19; lia | clear - HV2l HV2r K0l K0r K5 K19; lia | clear - HV2l HV2r K0l K0r K5 K19; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K20) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K20) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K20) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K20) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K20; lia | clear - HV33l HV33r K3l K3r K5 K20; lia | clear - HV33l HV33r K3l K3r K5 K20; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K19) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K19; lia | clear - HV2l HV2r K0l K0r K5 K19; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K19) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K20) | clear - HV2l HV2r K0l K0r K5 K19; lia | clear - HV2l HV2r K0l K0r K5 K19; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K19) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K20) | clear - HV2l HV2r K0l K0r K5 K19; lia | clear - HV2l HV2r K0l K0r K5 K19; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K19) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K20) | clear - HV2l HV2r K0l K0r K5 K19; lia | clear - HV2l HV2r K0l K0r K5 K19; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K19) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K19; lia | clear - HV2l HV2r K0l K0r K5 K19; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K19) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K20 HV39l HV39r K7l K7r) | clear - HV2l HV2r K0l K0r K5 K19; lia | clear - HV2l HV2r K0l K0r K5 K19; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K15l K15r K19 K20) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r K19 K20) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r K19 K20 HV41l HV41r K15l K15r) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K16l K16r K19 K20 HV41l HV41r K15l K15r; lia | clear - HV40l HV40r K16l K16r K19 K20 HV41l HV41r K15l K15r; lia | clear - HV40l HV40r K16l K16r K19 K20 HV41l HV41r K15l K15r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K16l K16r K19 K20 HV41l HV41r K15l K15r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K16l K16r K19 K20 HV41l HV41r K15l K15r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PicCl3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PicCl3.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 80) <= bv_unsigned a < (vz_33 + 80) + 24) -> ~ (((vz_41 + vz_40) + 0) <= bv_unsigned a < ((vz_41 + vz_40) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PicCl3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K20 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K16l K16r K19 K20 HV41l HV41r K15l K15r) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K16l K16r K19 K20 HV41l HV41r K15l K15r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PicCl3.ps0) with 0x36248 in Hms. change (SR.ps_regs PicCl3.ps0) with (map (fun i => (i, nth i PicCl3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PicCl3.ps0) with PicCl3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PicCl3.regs0 PicCl3.regs_out0 52 KS_icCl3 KS_icCl3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PicCl3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl3.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl3.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl3.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K16l K16r K19 K20 HV41l HV41r K15l K15r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K20) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K15l K15r K19 K20) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K20) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K16l K16r K19 K20) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K20) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K17l K17r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PicCl4 := LibSegBs_icCl4_u.
Definition KS_icCl4 : list nat := Eval vm_compute in (BG.kept_list 52 PicCl4.regs0 PicCl4.regs_out0).
Lemma KS_icCl4_ok : BG.kept_ok 52 PicCl4.regs0 PicCl4.regs_out0 KS_icCl4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma icCl4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 16) ->
  140735332483280 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 208) 208 -> 140735332483280 <= (V 33%nat) <= 140737488355056 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 208) + 208 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 208)) -> L5.writable RSEGS M (V 33%nat) 272 -> 272 <= (V 39%nat) <= 8388608 ->
  aligned (V 39%nat) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 88) 215696 -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 33%nat) + (V 39%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 112) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 120) -> L5.u64_at RSEGS M ((V 2%nat) - 136) 740848 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 51%nat) -> L5.u8_at RSEGS M ((V 33%nat) + 80) (V 38%nat) -> 0 <= (V 38%nat) <= 255 -> Z.testbit (V 38%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 33%nat) + 88) (V 40%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 96) (V 41%nat) -> L5.u32_at RSEGS M ((V 33%nat) + 112) 8 -> 4096 <= (V 41%nat) <= 140737488355328 ->
  23 <= (V 40%nat) <= 67108863 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 48) -> ~ (((V 33%nat) + 32) <= bv_unsigned a < ((V 33%nat) + 32) + 24) -> ~ (((V 33%nat) + 104) <= bv_unsigned a < ((V 33%nat) + 104) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 48) -> ~ (((V 33%nat) + 32) <= i < ((V 33%nat) + 32) + 24) -> ~ (((V 33%nat) + 104) <= i < ((V 33%nat) + 104) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36248 M) (st fx' R' 0x34ab8 M')
        /\ (forall x, In x KS_icCl4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + (V 41%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 104) ((V 40%nat) + (V 41%nat))
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 48) ((V 40%nat) + (V 41%nat))
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 40) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 32) (V 41%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 pvzI16 K1 K2 pvzI17 K4 K5 K6 pvzI18 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 pvzI19 K27 K28 K29 K30 pvzI20 pvzI21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV39l; move HV39l before pvzI4; pose proof (proj2 pvzI4) as HV39r; move HV39r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV44l; move HV44l before pvzI8; pose proof (proj2 pvzI8) as HV44r; move HV44r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV45l; move HV45l before pvzI9; pose proof (proj2 pvzI9) as HV45r; move HV45r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV46l; move HV46l before pvzI10; pose proof (proj2 pvzI10) as HV46r; move HV46r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV47l; move HV47l before pvzI11; pose proof (proj2 pvzI11) as HV47r; move HV47r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV48l; move HV48l before pvzI12; pose proof (proj2 pvzI12) as HV48r; move HV48r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV49l; move HV49l before pvzI13; pose proof (proj2 pvzI13) as HV49r; move HV49r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV50l; move HV50l before pvzI14; pose proof (proj2 pvzI14) as HV50r; move HV50r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV51l; move HV51l before pvzI15; pose proof (proj2 pvzI15) as HV51r; move HV51r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K3l; move K3l before pvzI17; pose proof (proj2 pvzI17) as K3r; move K3r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K7l; move K7l before pvzI18; pose proof (proj2 pvzI18) as K7r; move K7r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K31l; move K31l before pvzI20; pose proof (proj2 pvzI20) as K31r; move K31r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K32l; move K32l before pvzI21; pose proof (proj2 pvzI21) as K32r; move K32r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PicCl4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PicCl4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PicCl4.kn0).
  { unfold know_ok, PicCl4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 HV39l HV39r K7l K7r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV38l HV38r K26l K26r K27) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | byte_tac ltac:(clear - HV38l HV38r K26l K26r K27) | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K26l K26r K27) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K26l K26r K27) | clear; lia | rewrite (L5K.land1_bit0_true vz_38 ltac:(clear - HV38l HV38r K26l K26r K27; lia) K27); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV40l HV40r K32l K32r) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV41l HV41r K31l K31r) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K31l K31r) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PicCl4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PicCl4.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 48) -> ~ ((vz_33 + 32) <= bv_unsigned a < (vz_33 + 32) + 24) -> ~ ((vz_33 + 104) <= bv_unsigned a < (vz_33 + 104) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PicCl4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PicCl4.ps0) with 0x34ab8 in Hms. change (SR.ps_regs PicCl4.ps0) with (map (fun i => (i, nth i PicCl4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PicCl4.ps0) with PicCl4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PicCl4.regs0 PicCl4.regs_out0 52 KS_icCl4 KS_icCl4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PicCl4.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K32l K32r HV41l HV41r K31l K31r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K32l K32r HV41l HV41r K31l K31r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K31l K31r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K31l K31r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PMISP.
