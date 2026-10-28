(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_abrsA_b LibSegBa_abrsSS_b LibSegBa_abrsSL_b LibSegBa_abrsLS_b LibSegBa_abrsLL_b LibSegBa_abrsT_b LibSegBa_abrsM_b LibSegBa_abrsZ_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARBP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).

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
Module PabrsA := LibSegBa_abrsA_b.
Definition KS_abrsA : list nat := Eval vm_compute in (BG.kept_list 60 PabrsA.regs0 PabrsA.regs_out0).
Lemma KS_abrsA_ok : BG.kept_ok 60 PabrsA.regs0 PabrsA.regs_out0 KS_abrsA = true. Proof. vm_compute. reflexivity. Qed.
Lemma abrsA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 6905856 <= (V 40%nat) <= 140737488354912 -> aligned (V 40%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450881) 1 -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450920) 12 -> L5KA.zeros_at M ((((V 40%nat) + 9) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 40%nat) + 345) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 40%nat) + 369) / 8) + 2147450880) 1 -> (((V 2%nat) - 64) + 64 <= (V 40%nat) \/ (V 40%nat) + 416 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 40%nat) + 320) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 40%nat) + 328) (V 36%nat) -> L5.writable RSEGS M ((V 40%nat) + 8) 2 -> L5.writable RSEGS M ((V 40%nat) + 328) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((V 40%nat) + 8) <= bv_unsigned a < ((V 40%nat) + 8) + 2) -> ~ (((V 40%nat) + 328) <= bv_unsigned a < ((V 40%nat) + 328) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((V 40%nat) + 8) <= i < ((V 40%nat) + 8) + 2) -> ~ (((V 40%nat) + 328) <= i < ((V 40%nat) + 328) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xadb68 M) (st fx' R' 0xabb00 M')
        /\ (forall x, In x KS_abrsA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711632
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 320)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 9) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 8) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 328) (V 36%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 K0 K1 K2 pvzI5 K4 K5 pvzI6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 36%nat => vz_36 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PabrsA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabrsA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabrsA.kn0).
  { unfold know_ok, PabrsA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K14; lia | clear - HV2l HV2r K3l K3r K14; lia | clear - HV2l HV2r K3l K3r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K12]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K18]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabrsA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabrsA.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ ((vz_40 + 8) <= bv_unsigned a < (vz_40 + 8) + 2) -> ~ ((vz_40 + 328) <= bv_unsigned a < (vz_40 + 328) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PabrsA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabrsA.ps0) with 0xabb00 in Hms. change (SR.ps_regs PabrsA.ps0) with (map (fun i => (i, nth i PabrsA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabrsA.ps0) with PabrsA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabrsA.regs0 PabrsA.regs_out0 60 KS_abrsA KS_abrsA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabrsA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabrsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PabrsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PabrsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabrsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabrsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PabrsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabrsSS := LibSegBa_abrsSS_b.
Definition KS_abrsSS : list nat := Eval vm_compute in (BG.kept_list 60 PabrsSS.regs0 PabrsSS.regs_out0).
Lemma KS_abrsSS_ok : BG.kept_ok 60 PabrsSS.regs0 PabrsSS.regs_out0 KS_abrsSS = true. Proof. vm_compute. reflexivity. Qed.
Lemma abrsSS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 6905856 <= (V 40%nat) <= 140737488354912 -> aligned (V 40%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450881) 1 -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450920) 12 -> L5KA.zeros_at M ((((V 40%nat) + 9) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 40%nat) + 345) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 40%nat) + 369) / 8) + 2147450880) 1 -> (((V 2%nat) - 64) + 64 <= (V 40%nat) \/ (V 40%nat) + 416 <= ((V 2%nat) - 64)) -> L5.u8_at RSEGS M ((V 40%nat) + 344) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = false -> L5.writable RSEGS M ((V 40%nat) + 344) 2 -> L5.u8_at RSEGS M ((V 40%nat) + 368) (V 43%nat) ->
  0 <= (V 43%nat) <= 255 -> Z.testbit (V 43%nat) 0 = false -> L5.writable RSEGS M ((V 40%nat) + 368) 2 -> L5.u64_at RSEGS M ((V 40%nat) + 392) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 40%nat) + 400) (V 47%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 40%nat) + 344) <= bv_unsigned a < ((V 40%nat) + 344) + 2) -> ~ (((V 40%nat) + 368) <= bv_unsigned a < ((V 40%nat) + 368) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 40%nat) + 344) <= i < ((V 40%nat) + 344) + 2) -> ~ (((V 40%nat) + 368) <= i < ((V 40%nat) + 368) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xadbd0 M) (st fx' R' 0xab740 M')
        /\ (forall x, In x KS_abrsSS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711932
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 392)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((((V 40%nat) + 368) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 40%nat) + 392)
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 368) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 369) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 344) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 345) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G19 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI9 K17 K18 K19 pvzI10 K21 K22 K23 K24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV46l; move HV46l before pvzI5; pose proof (proj2 pvzI5) as HV46r; move HV46r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 40%nat => vz_40 | 43%nat => vz_43 | 46%nat => vz_46 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PabrsSS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabrsSS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabrsSS.kn0).
  { unfold know_ok, PabrsSS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K14; lia | clear - HV2l HV2r K3l K3r K14; lia | clear - HV2l HV2r K3l K3r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K12]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | byte_tac ltac:(clear - HV33l HV33r K16l K16r) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r) | clear; lia | erewrite L5K.land1_bit0_false by first [exact K17 | (clear - HV33l HV33r K16l K16r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear - HV43l HV43r K20l K20r) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | byte_tac ltac:(clear - HV43l HV43r K20l K20r) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV43l HV43r K20l K20r) | clear; lia | erewrite L5K.land1_bit0_false by first [exact K21 | (clear - HV43l HV43r K20l K20r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV40l HV40r K6l K6r K8 K14; lia | clear - HV40l HV40r K6l K6r K8 K14; lia | exactA K24]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabrsSS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabrsSS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_40 + 344) <= bv_unsigned a < (vz_40 + 344) + 2) -> ~ ((vz_40 + 368) <= bv_unsigned a < (vz_40 + 368) + 2) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PabrsSS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabrsSS.ps0) with 0xab740 in Hms. change (SR.ps_regs PabrsSS.ps0) with (map (fun i => (i, nth i PabrsSS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabrsSS.ps0) with PabrsSS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabrsSS.regs0 PabrsSS.regs_out0 60 KS_abrsSS KS_abrsSS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabrsSS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabrsSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsSS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabrsSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsSS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabrsSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsSS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabrsSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsSS.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PabrsSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsSS.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabrsSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabrsSL := LibSegBa_abrsSL_b.
Definition KS_abrsSL : list nat := Eval vm_compute in (BG.kept_list 60 PabrsSL.regs0 PabrsSL.regs_out0).
Lemma KS_abrsSL_ok : BG.kept_ok 60 PabrsSL.regs0 PabrsSL.regs_out0 KS_abrsSL = true. Proof. vm_compute. reflexivity. Qed.
Lemma abrsSL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 6905856 <= (V 40%nat) <= 140737488354912 -> aligned (V 40%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450881) 1 -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450920) 12 -> L5KA.zeros_at M ((((V 40%nat) + 9) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 40%nat) + 345) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 40%nat) + 369) / 8) + 2147450880) 1 -> (((V 2%nat) - 64) + 64 <= (V 40%nat) \/ (V 40%nat) + 416 <= ((V 2%nat) - 64)) -> L5.u8_at RSEGS M ((V 40%nat) + 344) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = false -> L5.writable RSEGS M ((V 40%nat) + 344) 2 -> L5.u8_at RSEGS M ((V 40%nat) + 368) (V 43%nat) ->
  0 <= (V 43%nat) <= 255 -> Z.testbit (V 43%nat) 0 = true -> L5.u64_at RSEGS M ((V 40%nat) + 384) (V 45%nat) -> 4096 <= (V 45%nat) <= 140737488355320 ->
  aligned (V 45%nat) 8 -> (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 45%nat) 1 ->
  (((V 2%nat) - 64) + 64 <= (V 45%nat) \/ (V 45%nat) + 1 <= ((V 2%nat) - 64)) -> ((V 45%nat) + 1 <= (V 40%nat) \/ (V 40%nat) + 416 <= (V 45%nat)) -> (65536 + 6840320 <= (V 45%nat) \/ (V 45%nat) + 1 <= 65536) -> L5.writable RSEGS M ((V 40%nat) + 376) 8 ->
  L5.u64_at RSEGS M ((V 40%nat) + 392) (V 46%nat) -> L5.u64_at RSEGS M ((V 40%nat) + 400) (V 47%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 40%nat) + 344) <= bv_unsigned a < ((V 40%nat) + 344) + 2) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 1) -> ~ (((V 40%nat) + 376) <= bv_unsigned a < ((V 40%nat) + 376) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 40%nat) + 344) <= i < ((V 40%nat) + 344) + 2) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 1) -> ~ (((V 40%nat) + 376) <= i < ((V 40%nat) + 376) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xadbd0 M) (st fx' R' 0xab740 M')
        /\ (forall x, In x KS_abrsSL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711932
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 392)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 376)
        /\ getr R' (reg 12) = Z_to_bv 64 ((((V 40%nat) + 368) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 40%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 376) 0
        /\ L5.u8_at RSEGS M' (V 45%nat) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 344) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 345) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G19 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI10 K17 K18 K19 pvzI11 K21 K22 pvzI12 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV47l; move HV47l before pvzI7; pose proof (proj2 pvzI7) as HV47r; move HV47r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K16l; move K16l before pvzI10; pose proof (proj2 pvzI10) as K16r; move K16r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 40%nat => vz_40 | 43%nat => vz_43 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PabrsSL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabrsSL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabrsSL.kn0).
  { unfold know_ok, PabrsSL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K28) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K28) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K28) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K14 K28; lia | clear - HV2l HV2r K3l K3r K14 K28; lia | clear - HV2l HV2r K3l K3r K14 K28; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | exactA K12]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r) | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | byte_tac ltac:(clear - HV33l HV33r K16l K16r) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r) | clear; lia | erewrite L5K.land1_bit0_false by first [exact K17 | (clear - HV33l HV33r K16l K16r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear - HV43l HV43r K20l K20r) | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | byte_tac ltac:(clear - HV43l HV43r K20l K20r) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV43l HV43r K20l K20r) | clear; lia | erewrite L5K.land1_bit0_true by first [exact K21 | (clear - HV43l HV43r K20l K20r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K25 K28 K29 K30) | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K25 K28 K29 K30) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K25 K28 K29 K30) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K25 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K25 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K23l K23r K25 K28 K29 K30; lia | clear - HV45l HV45r K23l K23r K25 K28 K29 K30; lia | clear - HV45l HV45r K23l K23r K25 K28 K29 K30; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K25 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K23l K23r K25 K28 K29 K30; lia | clear - HV45l HV45r K23l K23r K25 K28 K29 K30; lia | clear - HV45l HV45r K23l K23r K25 K28 K29 K30; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K25 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K25 K28 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K25 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | clear - HV40l HV40r K6l K6r K8 K14 K29; lia | exactA K33]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabrsSL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabrsSL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_40 + 344) <= bv_unsigned a < (vz_40 + 344) + 2) -> ~ ((vz_45 + 0) <= bv_unsigned a < (vz_45 + 0) + 1) -> ~ ((vz_40 + 376) <= bv_unsigned a < (vz_40 + 376) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PabrsSL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K29 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K23l K23r K25 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K23l K23r K25 K28 K29 K30 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K29 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabrsSL.ps0) with 0xab740 in Hms. change (SR.ps_regs PabrsSL.ps0) with (map (fun i => (i, nth i PabrsSL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabrsSL.ps0) with PabrsSL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabrsSL.regs0 PabrsSL.regs_out0 60 KS_abrsSL KS_abrsSL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabrsSL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabrsSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsSL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabrsSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsSL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabrsSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsSL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabrsSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsSL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PabrsSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsSL.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabrsSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV45l HV45r K23l K23r K25 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K29) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabrsLS := LibSegBa_abrsLS_b.
Definition KS_abrsLS : list nat := Eval vm_compute in (BG.kept_list 60 PabrsLS.regs0 PabrsLS.regs_out0).
Lemma KS_abrsLS_ok : BG.kept_ok 60 PabrsLS.regs0 PabrsLS.regs_out0 KS_abrsLS = true. Proof. vm_compute. reflexivity. Qed.
Lemma abrsLS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 6905856 <= (V 40%nat) <= 140737488354912 -> aligned (V 40%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450881) 1 -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450920) 12 -> L5KA.zeros_at M ((((V 40%nat) + 9) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 40%nat) + 345) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 40%nat) + 369) / 8) + 2147450880) 1 -> (((V 2%nat) - 64) + 64 <= (V 40%nat) \/ (V 40%nat) + 416 <= ((V 2%nat) - 64)) -> L5.u8_at RSEGS M ((V 40%nat) + 344) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((V 40%nat) + 360) (V 37%nat) -> 4096 <= (V 37%nat) <= 140737488355320 ->
  aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 37%nat) 1 ->
  (((V 2%nat) - 64) + 64 <= (V 37%nat) \/ (V 37%nat) + 1 <= ((V 2%nat) - 64)) -> ((V 37%nat) + 1 <= (V 40%nat) \/ (V 40%nat) + 416 <= (V 37%nat)) -> (65536 + 6840320 <= (V 37%nat) \/ (V 37%nat) + 1 <= 65536) -> L5.writable RSEGS M ((V 40%nat) + 352) 8 ->
  L5.u8_at RSEGS M ((V 40%nat) + 368) (V 43%nat) -> 0 <= (V 43%nat) <= 255 -> Z.testbit (V 43%nat) 0 = false -> L5.writable RSEGS M ((V 40%nat) + 368) 2 ->
  L5.u64_at RSEGS M ((V 40%nat) + 392) (V 46%nat) -> L5.u64_at RSEGS M ((V 40%nat) + 400) (V 47%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) + 0) <= bv_unsigned a < ((V 37%nat) + 0) + 1) -> ~ (((V 40%nat) + 352) <= bv_unsigned a < ((V 40%nat) + 352) + 8) -> ~ (((V 40%nat) + 368) <= bv_unsigned a < ((V 40%nat) + 368) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) + 0) <= i < ((V 37%nat) + 0) + 1) -> ~ (((V 40%nat) + 352) <= i < ((V 40%nat) + 352) + 8) -> ~ (((V 40%nat) + 368) <= i < ((V 40%nat) + 368) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xadbd0 M) (st fx' R' 0xab740 M')
        /\ (forall x, In x KS_abrsLS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711932
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 392)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((((V 40%nat) + 368) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 40%nat) + 392)
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 368) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 369) 0
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 352) 0
        /\ L5.u8_at RSEGS M' (V 37%nat) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G19 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI10 K17 K18 pvzI11 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI12 K30 K31 K32 K33.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV47l; move HV47l before pvzI7; pose proof (proj2 pvzI7) as HV47r; move HV47r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K16l; move K16l before pvzI10; pose proof (proj2 pvzI10) as K16r; move K16r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K19l; move K19l before pvzI11; pose proof (proj2 pvzI11) as K19r; move K19r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K29l; move K29l before pvzI12; pose proof (proj2 pvzI12) as K29r; move K29r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 37%nat => vz_37 | 40%nat => vz_40 | 43%nat => vz_43 | 46%nat => vz_46 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PabrsLS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabrsLS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabrsLS.kn0).
  { unfold know_ok, PabrsLS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K14 K24; lia | clear - HV2l HV2r K3l K3r K14 K24; lia | clear - HV2l HV2r K3l K3r K14 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | exactA K12]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r) | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | byte_tac ltac:(clear - HV33l HV33r K16l K16r) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r) | clear; lia | erewrite L5K.land1_bit0_true by first [exact K17 | (clear - HV33l HV33r K16l K16r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26) | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K19l K19r K21 K24 K25 K26; lia | clear - HV37l HV37r K19l K19r K21 K24 K25 K26; lia | clear - HV37l HV37r K19l K19r K21 K24 K25 K26; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K19l K19r K21 K24 K25 K26; lia | clear - HV37l HV37r K19l K19r K21 K24 K25 K26; lia | clear - HV37l HV37r K19l K19r K21 K24 K25 K26; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear - HV43l HV43r K29l K29r) | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | byte_tac ltac:(clear - HV43l HV43r K29l K29r) | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV43l HV43r K29l K29r) | clear; lia | erewrite L5K.land1_bit0_false by first [exact K30 | (clear - HV43l HV43r K29l K29r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | clear - HV40l HV40r K6l K6r K8 K14 K25; lia | exactA K33]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabrsLS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabrsLS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_37 + 0) <= bv_unsigned a < (vz_37 + 0) + 1) -> ~ ((vz_40 + 352) <= bv_unsigned a < (vz_40 + 352) + 8) -> ~ ((vz_40 + 368) <= bv_unsigned a < (vz_40 + 368) + 2) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PabrsLS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K19l K19r K21 K24 K25 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabrsLS.ps0) with 0xab740 in Hms. change (SR.ps_regs PabrsLS.ps0) with (map (fun i => (i, nth i PabrsLS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabrsLS.ps0) with PabrsLS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabrsLS.regs0 PabrsLS.regs_out0 60 KS_abrsLS KS_abrsLS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabrsLS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabrsLS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsLS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabrsLS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsLS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabrsLS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsLS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabrsLS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsLS.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PabrsLS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsLS.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabrsLS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabrsLL := LibSegBa_abrsLL_b.
Definition KS_abrsLL : list nat := Eval vm_compute in (BG.kept_list 60 PabrsLL.regs0 PabrsLL.regs_out0).
Lemma KS_abrsLL_ok : BG.kept_ok 60 PabrsLL.regs0 PabrsLL.regs_out0 KS_abrsLL = true. Proof. vm_compute. reflexivity. Qed.
Lemma abrsLL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 6905856 <= (V 40%nat) <= 140737488354912 -> aligned (V 40%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450881) 1 -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450920) 12 -> L5KA.zeros_at M ((((V 40%nat) + 9) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 40%nat) + 345) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 40%nat) + 369) / 8) + 2147450880) 1 -> (((V 2%nat) - 64) + 64 <= (V 40%nat) \/ (V 40%nat) + 416 <= ((V 2%nat) - 64)) -> L5.u8_at RSEGS M ((V 40%nat) + 344) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((V 40%nat) + 360) (V 37%nat) -> 4096 <= (V 37%nat) <= 140737488355320 ->
  aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 37%nat) 1 ->
  (((V 2%nat) - 64) + 64 <= (V 37%nat) \/ (V 37%nat) + 1 <= ((V 2%nat) - 64)) -> ((V 37%nat) + 1 <= (V 40%nat) \/ (V 40%nat) + 416 <= (V 37%nat)) -> (65536 + 6840320 <= (V 37%nat) \/ (V 37%nat) + 1 <= 65536) -> L5.writable RSEGS M ((V 40%nat) + 352) 8 ->
  L5.u8_at RSEGS M ((V 40%nat) + 368) (V 43%nat) -> 0 <= (V 43%nat) <= 255 -> Z.testbit (V 43%nat) 0 = true -> L5.u64_at RSEGS M ((V 40%nat) + 384) (V 45%nat) ->
  4096 <= (V 45%nat) <= 140737488355320 -> aligned (V 45%nat) 8 -> (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 45%nat) 1 -> (((V 2%nat) - 64) + 64 <= (V 45%nat) \/ (V 45%nat) + 1 <= ((V 2%nat) - 64)) -> ((V 45%nat) + 1 <= (V 40%nat) \/ (V 40%nat) + 416 <= (V 45%nat)) -> (65536 + 6840320 <= (V 45%nat) \/ (V 45%nat) + 1 <= 65536) ->
  L5.writable RSEGS M ((V 40%nat) + 376) 8 -> L5.u64_at RSEGS M ((V 40%nat) + 392) (V 46%nat) -> L5.u64_at RSEGS M ((V 40%nat) + 400) (V 47%nat) -> ((V 37%nat) + 1 <= (V 45%nat) \/ (V 45%nat) + 1 <= (V 37%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) + 0) <= bv_unsigned a < ((V 37%nat) + 0) + 1) -> ~ (((V 40%nat) + 352) <= bv_unsigned a < ((V 40%nat) + 352) + 8) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 1) -> ~ (((V 40%nat) + 376) <= bv_unsigned a < ((V 40%nat) + 376) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) + 0) <= i < ((V 37%nat) + 0) + 1) -> ~ (((V 40%nat) + 352) <= i < ((V 40%nat) + 352) + 8) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 1) -> ~ (((V 40%nat) + 376) <= i < ((V 40%nat) + 376) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xadbd0 M) (st fx' R' 0xab740 M')
        /\ (forall x, In x KS_abrsLL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711932
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 392)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 376)
        /\ getr R' (reg 12) = Z_to_bv 64 ((((V 40%nat) + 368) / 8) + 2147450880)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 40%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 376) 0
        /\ L5.u8_at RSEGS M' (V 45%nat) 0
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 352) 0
        /\ L5.u8_at RSEGS M' (V 37%nat) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G19 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI11 K17 K18 pvzI12 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI13 K30 K31 pvzI14 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K19l; move K19l before pvzI12; pose proof (proj2 pvzI12) as K19r; move K19r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K29l; move K29l before pvzI13; pose proof (proj2 pvzI13) as K29r; move K29r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K32l; move K32l before pvzI14; pose proof (proj2 pvzI14) as K32r; move K32r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 37%nat => vz_37 | 40%nat => vz_40 | 43%nat => vz_43 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PabrsLL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabrsLL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabrsLL.kn0).
  { unfold know_ok, PabrsLL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K24 K37) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K24 K37) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K24 K37) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K14 K24 K37; lia | clear - HV2l HV2r K3l K3r K14 K24 K37; lia | clear - HV2l HV2r K3l K3r K14 K24 K37; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K24 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | byte_tac ltac:(clear - HV33l HV33r K16l K16r) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r) | clear; lia | erewrite L5K.land1_bit0_true by first [exact K17 | (clear - HV33l HV33r K16l K16r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43; lia | clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43; lia | clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43; lia | clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43; lia | clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K24 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear - HV43l HV43r K29l K29r) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | byte_tac ltac:(clear - HV43l HV43r K29l K29r) | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV43l HV43r K29l K29r) | clear; lia | erewrite L5K.land1_bit0_true by first [exact K30 | (clear - HV43l HV43r K29l K29r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43; lia | clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43; lia | clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43; lia | clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43; lia | clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K24 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | clear - HV40l HV40r K6l K6r K8 K14 K25 K38; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabrsLL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabrsLL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_37 + 0) <= bv_unsigned a < (vz_37 + 0) + 1) -> ~ ((vz_40 + 352) <= bv_unsigned a < (vz_40 + 352) + 8) -> ~ ((vz_45 + 0) <= bv_unsigned a < (vz_45 + 0) + 1) -> ~ ((vz_40 + 376) <= bv_unsigned a < (vz_40 + 376) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PabrsLL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K8 K14 K25 K38 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabrsLL.ps0) with 0xab740 in Hms. change (SR.ps_regs PabrsLL.ps0) with (map (fun i => (i, nth i PabrsLL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabrsLL.ps0) with PabrsLL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabrsLL.regs0 PabrsLL.regs_out0 60 KS_abrsLL KS_abrsLL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabrsLL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabrsLL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsLL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabrsLL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsLL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabrsLL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsLL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabrsLL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsLL.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabrsLL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV45l HV45r K32l K32r K34 K37 K38 K39 K43) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K8 K14 K25 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K19l K19r K21 K24 K25 K26 K43) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabrsT := LibSegBa_abrsT_b.
Definition KS_abrsT : list nat := Eval vm_compute in (BG.kept_list 60 PabrsT.regs0 PabrsT.regs_out0).
Lemma KS_abrsT_ok : BG.kept_ok 60 PabrsT.regs0 PabrsT.regs_out0 KS_abrsT = true. Proof. vm_compute. reflexivity. Qed.
Lemma abrsT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 40%nat) + 392) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332487216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 6905856 <= (V 40%nat) <= 140737488354912 ->
  aligned (V 40%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 40%nat) \/ (V 40%nat) + 416 <= ((V 2%nat) - 64)) -> L5KA.zeros_at M ((((V 40%nat) + 400) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 40%nat) + 408) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 40%nat) + 392) (V 36%nat) -> L5.u64_at RSEGS M ((V 40%nat) + 400) (V 36%nat) -> L5.u64_at RSEGS M ((V 40%nat) + 408) (V 50%nat) -> 4096 <= (V 36%nat) <= 140737488355288 ->
  aligned (V 36%nat) 16 -> 4136 <= (V 50%nat) <= 140737488355327 -> 40 <= ((V 50%nat) - (V 36%nat)) <= 81920 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 60) <= bv_unsigned a < ((V 2%nat) - 60) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 60) <= i < ((V 2%nat) - 60) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xadcfc M) (st fx' R' 0xacf40 M')
        /\ (forall x, In x KS_abrsT -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 712016
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 40%nat) + 400)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 392)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 52)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 56)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 40%nat) + 400) / 8) + 2147450880)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 56) 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 52) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G18 G19 pvzI5 K1 K2 pvzI6 K4 K5 K6 K7 K8 K9 K10 pvzI7 K12 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K11l; move K11l before pvzI7; pose proof (proj2 pvzI7) as K11r; move K11r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K13l; move K13l before pvzI8; pose proof (proj2 pvzI8) as K13r; move K13r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 40%nat => vz_40 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PabrsT.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabrsT.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabrsT.kn0).
  { unfold know_ok, PabrsT.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K14l K14r) | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K14l K14r) | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K14l K14r) | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K14l K14r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K14l K14r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K14l K14r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K14l K14r HV50l HV50r K13l K13r) | exact (conj K14l K14r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabrsT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabrsT.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 60) <= bv_unsigned a < (vz_2 - 60) + 12) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PabrsT.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabrsT.ps0) with 0xacf40 in Hms. change (SR.ps_regs PabrsT.ps0) with (map (fun i => (i, nth i PabrsT.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabrsT.ps0) with PabrsT.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabrsT.regs0 PabrsT.regs_out0 60 KS_abrsT KS_abrsT_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabrsT.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabrsT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsT.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PabrsT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsT.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PabrsT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsT.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabrsT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsT.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabrsT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsT.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabrsT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsT.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PabrsT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsT.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PabrsT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabrsM := LibSegBa_abrsM_b.
Definition KS_abrsM : list nat := Eval vm_compute in (BG.kept_list 60 PabrsM.regs0 PabrsM.regs_out0).
Lemma KS_abrsM_ok : BG.kept_ok 60 PabrsM.regs0 PabrsM.regs_out0 KS_abrsM = true. Proof. vm_compute. reflexivity. Qed.
Lemma abrsM_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 40%nat) + 392) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332487216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 6905856 <= (V 40%nat) <= 140737488354912 ->
  aligned (V 40%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 40%nat) \/ (V 40%nat) + 416 <= ((V 2%nat) - 64)) -> L5KA.zeros_at M ((((V 40%nat) + 400) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 40%nat) + 408) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 40%nat) + 392) (V 36%nat) -> L5.u64_at RSEGS M ((V 40%nat) + 400) (V 36%nat) -> L5.u64_at RSEGS M ((V 40%nat) + 408) (V 36%nat) -> 4096 <= (V 36%nat) <= 140737488355288 ->
  aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 60) <= bv_unsigned a < ((V 2%nat) - 60) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 60) <= i < ((V 2%nat) - 60) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xadcfc M) (st fx' R' 0xad11c M')
        /\ (forall x, In x KS_abrsM -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 712056
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 40%nat) + 400)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 392)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 52)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 56)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 40%nat) + 400) / 8) + 2147450880)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 56) 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 52) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G18 G19 pvzI4 K1 K2 pvzI5 K4 K5 K6 K7 K8 K9 K10 pvzI6 K12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K11l; move K11l before pvzI6; pose proof (proj2 pvzI6) as K11r; move K11r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PabrsM.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabrsM.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabrsM.kn0).
  { unfold know_ok, PabrsM.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K5) | evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | clear - HV40l HV40r K3l K3r K5; lia | clear - HV40l HV40r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | clear; lia | exact K12]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabrsM.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabrsM.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 60) <= bv_unsigned a < (vz_2 - 60) + 12) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PabrsM.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabrsM.ps0) with 0xad11c in Hms. change (SR.ps_regs PabrsM.ps0) with (map (fun i => (i, nth i PabrsM.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabrsM.ps0) with PabrsM.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabrsM.regs0 PabrsM.regs_out0 60 KS_abrsM KS_abrsM_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabrsM.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabrsM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsM.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PabrsM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsM.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PabrsM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsM.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabrsM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsM.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabrsM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsM.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabrsM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsM.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PabrsM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsM.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PabrsM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabrsZ := LibSegBa_abrsZ_b.
Definition KS_abrsZ : list nat := Eval vm_compute in (BG.kept_list 60 PabrsZ.regs0 PabrsZ.regs_out0).
Lemma KS_abrsZ_ok : BG.kept_ok 60 PabrsZ.regs0 PabrsZ.regs_out0 KS_abrsZ = true. Proof. vm_compute. reflexivity. Qed.
Lemma abrsZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 40%nat) + 400) -> getr R (reg 18) = Z_to_bv 64 ((V 40%nat) + 392) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 ((((V 40%nat) + 400) / 8) + 2147450880) ->
  140735332487216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 44%nat) -> 6905856 <= (V 40%nat) <= 140737488354912 -> aligned (V 40%nat) 8 -> L5KA.zeros_at M ((((V 40%nat) + 400) / 8) + 2147450880) 1 ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> L5.writable RSEGS M ((V 40%nat) + 400) 8 -> (((V 2%nat) - 64) + 64 <= (V 40%nat) \/ (V 40%nat) + 416 <= ((V 2%nat) - 64)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 40%nat) + 400) <= bv_unsigned a < ((V 40%nat) + 400) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 40%nat) + 400) <= i < ((V 40%nat) + 400) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xadd50 M) (st fx' R' 0xaddb8 M')
        /\ (forall x, In x KS_abrsZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 40
        /\ getr R' (reg 18) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 400) ((V 36%nat) + 40)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G18 G19 G20 pvzI10 K1 K2 K3 K4 K5 K6 K7 K8 pvzI11 K10 K11 pvzI12 K13 K14 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV39l; move HV39l before pvzI4; pose proof (proj2 pvzI4) as HV39r; move HV39r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K9l; move K9l before pvzI11; pose proof (proj2 pvzI11) as K9r; move K9r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K12l; move K12l before pvzI12; pose proof (proj2 pvzI12) as K12r; move K12r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E PabrsZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabrsZ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabrsZ.kn0).
  { unfold know_ok, PabrsZ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K15; lia | clear - HV2l HV2r K0l K0r K15; lia | clear - HV2l HV2r K0l K0r K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K15; lia | clear - HV2l HV2r K0l K0r K15; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K15; lia | clear - HV2l HV2r K0l K0r K15; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K15; lia | clear - HV2l HV2r K0l K0r K15; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K15; lia | clear - HV2l HV2r K0l K0r K15; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K15; lia | clear - HV2l HV2r K0l K0r K15; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K15; lia | clear - HV2l HV2r K0l K0r K15; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K9l K9r K15) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K9l K9r K15) | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K9l K9r K15) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K9l K9r K15; lia | clear - HV40l HV40r K9l K9r K15; lia | clear - HV40l HV40r K9l K9r K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K9l K9r K15) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K9l K9r K15; lia | clear - HV40l HV40r K9l K9r K15; lia | clear - HV40l HV40r K9l K9r K15; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K9l K9r K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabrsZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabrsZ.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_40 + 400) <= bv_unsigned a < (vz_40 + 400) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PabrsZ.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K9l K9r K15) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K9l K9r K15 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabrsZ.ps0) with 0xaddb8 in Hms. change (SR.ps_regs PabrsZ.ps0) with (map (fun i => (i, nth i PabrsZ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabrsZ.ps0) with PabrsZ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabrsZ.regs0 PabrsZ.regs_out0 60 KS_abrsZ KS_abrsZ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabrsZ.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabrsZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsZ.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PabrsZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsZ.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PabrsZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsZ.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PabrsZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsZ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabrsZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsZ.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabrsZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsZ.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabrsZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsZ.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PabrsZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabrsZ.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PabrsZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K9l K9r K15) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r) | clear; lia].
Qed.
(* [comment removed for export] *)

End PNARBP.
