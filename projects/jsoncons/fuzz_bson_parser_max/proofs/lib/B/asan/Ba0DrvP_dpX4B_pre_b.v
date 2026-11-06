(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_dpX4B_pre_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module AS0DRVP_dpX4B_pre.
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
Module PdpX4B_pre := LibSegBa_dpX4B_pre_b.
Definition KS_dpX4B_pre : list nat := Eval vm_compute in (BG.kept_list 56 PdpX4B_pre.regs0 PdpX4B_pre.regs_out0).
Lemma KS_dpX4B_pre_ok : BG.kept_ok 56 PdpX4B_pre.regs0 PdpX4B_pre.regs_out0 KS_dpX4B_pre = true. Proof. vm_compute. reflexivity. Qed.
Lemma dpX4B_pre_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 1147060 -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 4) = Z_to_bv 64 6765824 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 320) 320 -> L5.defined M ((V 2%nat) - 320) 320 ->
  L5.img_clear M 65536 1282048 -> L5.writable RSEGS M 1295744 8 -> L5.writable RSEGS M 1295824 1 -> L5.writable RSEGS M 1299696 8 ->
  L5.writable RSEGS M 6896976 1 -> L5.writable RSEGS M 6896984 4 -> L5.writable RSEGS M 6896992 8 -> L5.writable RSEGS M 6897520 4 ->
  L5.writable RSEGS M 2147468856 1 -> L5.writable RSEGS M 2147468857 1 -> L5.writable RSEGS M 2147468858 1 -> L5.writable RSEGS M 2147468859 1 ->
  L5.writable RSEGS M 2147468868 1 -> L5.writable RSEGS M 2147468869 1 -> L5.writable RSEGS M 2147468870 1 -> L5.writable RSEGS M 2147468871 1 ->
  L5.writable RSEGS M 2147468872 1 -> L5.writable RSEGS M 2147468872 4 -> L5.writable RSEGS M 2147468873 1 -> L5.writable RSEGS M 2147468874 1 ->
  L5.writable RSEGS M 2147468875 1 -> L5.writable RSEGS M 2147468876 4 -> L5.writable RSEGS M 2147468880 1 -> L5.writable RSEGS M 2147468880 4 ->
  L5.writable RSEGS M 2147468881 1 -> L5.writable RSEGS M 2147468882 1 -> L5.writable RSEGS M 2147468883 1 -> L5.writable RSEGS M 2147468896 1 ->
  L5.writable RSEGS M 2147468897 1 -> L5.writable RSEGS M 2147468898 1 -> L5.writable RSEGS M 2147468899 1 -> L5.writable RSEGS M 2147468900 1 ->
  L5.writable RSEGS M 2147468901 1 -> L5.writable RSEGS M 2147468902 1 -> L5.writable RSEGS M 2147468903 1 -> L5.writable RSEGS M 2147468904 1 ->
  L5.writable RSEGS M 2147468905 1 -> L5.writable RSEGS M 2147468906 1 -> L5.writable RSEGS M 2147468907 1 -> L5.writable RSEGS M 2147468908 1 ->
  L5.writable RSEGS M 2147468909 1 -> L5.writable RSEGS M 2147468910 1 -> L5.writable RSEGS M 2147468911 1 -> L5.writable RSEGS M 2147468912 1 ->
  L5.writable RSEGS M 2147468912 4 -> L5.writable RSEGS M 2147468913 1 -> L5.writable RSEGS M 2147468914 1 -> L5.writable RSEGS M 2147468915 1 ->
  L5.writable RSEGS M 2147468916 4 -> L5.writable RSEGS M 2147468920 1 -> L5.writable RSEGS M 2147468920 4 -> L5.writable RSEGS M 2147468921 1 ->
  L5.writable RSEGS M 2147468922 1 -> L5.writable RSEGS M 2147468923 1 -> L5.writable RSEGS M 2147468924 1 -> L5.writable RSEGS M 2147468924 4 ->
  L5.writable RSEGS M 2147468925 1 -> L5.writable RSEGS M 2147468926 1 -> L5.writable RSEGS M 2147468927 1 -> L5.writable RSEGS M 2147468928 4 ->
  L5.writable RSEGS M 2147468932 1 -> L5.writable RSEGS M 2147468932 4 -> L5.writable RSEGS M 2147468933 1 -> L5.writable RSEGS M 2147468934 1 ->
  L5.writable RSEGS M 2147468935 1 -> L5.writable RSEGS M 2147468936 1 -> L5.writable RSEGS M 2147468936 4 -> L5.writable RSEGS M 2147468937 1 ->
  L5.writable RSEGS M 2147468938 1 -> L5.writable RSEGS M 2147468939 1 -> L5.writable RSEGS M 2147468940 4 -> L5.writable RSEGS M 2147468944 4 ->
  L5.writable RSEGS M 2147468948 1 -> L5.writable RSEGS M 2147468948 4 -> L5.writable RSEGS M 2147468949 1 -> L5.writable RSEGS M 2147468950 1 ->
  L5.writable RSEGS M 2147468951 1 -> L5.writable RSEGS M 2147468952 1 -> L5.writable RSEGS M 2147468952 4 -> L5.writable RSEGS M 2147468953 1 ->
  L5.writable RSEGS M 2147468954 1 -> L5.writable RSEGS M 2147468955 1 -> L5.writable RSEGS M 2147468956 4 -> L5.writable RSEGS M 2147468960 1 ->
  L5.writable RSEGS M 2147468960 4 -> L5.writable RSEGS M 2147468961 1 -> L5.writable RSEGS M 2147468962 1 -> L5.writable RSEGS M 2147468963 1 ->
  L5.writable RSEGS M 2147468964 1 -> L5.writable RSEGS M 2147468965 1 -> L5.writable RSEGS M 2147468966 1 -> L5.writable RSEGS M 2147468967 1 ->
  L5.writable RSEGS M 2147468968 1 -> L5.writable RSEGS M 2147468969 1 -> L5.writable RSEGS M 2147468970 1 -> L5.writable RSEGS M 2147468971 1 ->
  L5.writable RSEGS M 2147468972 1 -> L5.writable RSEGS M 2147468973 1 -> L5.writable RSEGS M 2147468974 1 -> L5.writable RSEGS M 2147468975 1 ->
  L5.writable RSEGS M 2147468976 1 -> L5.writable RSEGS M 2147468977 1 -> L5.writable RSEGS M 2147468978 1 -> L5.writable RSEGS M 2147468979 1 ->
  L5.writable RSEGS M 2147468980 1 -> L5.writable RSEGS M 2147468981 1 -> L5.writable RSEGS M 2147468982 1 -> L5.writable RSEGS M 2147468983 1 ->
  L5.writable RSEGS M 2147468984 1 -> L5.writable RSEGS M 2147468985 1 -> L5.writable RSEGS M 2147468986 1 -> L5.writable RSEGS M 2147468987 1 ->
  L5.writable RSEGS M 2147468988 1 -> L5.writable RSEGS M 2147468989 1 -> L5.writable RSEGS M 2147468990 1 -> L5.writable RSEGS M 2147468991 1 ->
  L5.writable RSEGS M 2147468992 1 -> L5.writable RSEGS M 2147468993 1 -> L5.writable RSEGS M 2147468994 1 -> L5.writable RSEGS M 2147468995 1 ->
  L5.writable RSEGS M 2147468996 1 -> L5.writable RSEGS M 2147468997 1 -> L5.writable RSEGS M 2147468998 1 -> L5.writable RSEGS M 2147468999 1 ->
  L5.writable RSEGS M 2147469000 1 -> L5.writable RSEGS M 2147469001 1 -> L5.writable RSEGS M 2147469002 1 -> L5.writable RSEGS M 2147469003 1 ->
  L5.writable RSEGS M 2147469004 1 -> L5.writable RSEGS M 2147469005 1 -> L5.writable RSEGS M 2147469006 1 -> L5.writable RSEGS M 2147469007 1 ->
  L5.writable RSEGS M 2147469008 1 -> L5.writable RSEGS M 2147469009 1 -> L5.writable RSEGS M 2147469010 1 -> L5.writable RSEGS M 2147469011 1 ->
  L5.writable RSEGS M 2147469012 1 -> L5.writable RSEGS M 2147469013 1 -> L5.writable RSEGS M 2147469014 1 -> L5.writable RSEGS M 2147469015 1 ->
  L5.writable RSEGS M 2147469016 1 -> L5.writable RSEGS M 2147469017 1 -> L5.writable RSEGS M 2147469018 1 -> L5.writable RSEGS M 2147469019 1 ->
  L5.writable RSEGS M 2147469020 1 -> L5.writable RSEGS M 2147469020 4 -> L5.writable RSEGS M 2147469021 1 -> L5.writable RSEGS M 2147469022 1 ->
  L5.writable RSEGS M 2147469023 1 -> L5.writable RSEGS M 2147469024 4 -> L5.writable RSEGS M 2147469028 1 -> L5.writable RSEGS M 2147469028 4 ->
  L5.writable RSEGS M 2147469029 1 -> L5.writable RSEGS M 2147469030 1 -> L5.writable RSEGS M 2147469031 1 -> L5.writable RSEGS M 2147469032 1 ->
  L5.writable RSEGS M 2147469033 1 -> L5.writable RSEGS M 2147469034 1 -> L5.writable RSEGS M 2147469035 1 -> L5.writable RSEGS M 2147469036 1 ->
  L5.writable RSEGS M 2147469037 1 -> L5.writable RSEGS M 2147469038 1 -> L5.writable RSEGS M 2147469039 1 -> L5.writable RSEGS M 2147469072 1 ->
  L5.writable RSEGS M 2147469072 4 -> L5.writable RSEGS M 2147469073 1 -> L5.writable RSEGS M 2147469074 1 -> L5.writable RSEGS M 2147469075 1 ->
  L5.writable RSEGS M 2147469076 4 -> L5.writable RSEGS M 2147469080 1 -> L5.writable RSEGS M 2147469080 4 -> L5.writable RSEGS M 2147469081 1 ->
  L5.writable RSEGS M 2147469082 1 -> L5.writable RSEGS M 2147469083 1 -> L5.writable RSEGS M 2147469084 1 -> L5.writable RSEGS M 2147469085 1 ->
  L5.writable RSEGS M 2147469086 1 -> L5.writable RSEGS M 2147469087 1 -> L5.writable RSEGS M 2147469088 1 -> L5.writable RSEGS M 2147469089 1 ->
  L5.writable RSEGS M 2147469090 1 -> L5.writable RSEGS M 2147469091 1 -> L5.writable RSEGS M 2147469092 1 -> L5.writable RSEGS M 2147469092 4 ->
  L5.writable RSEGS M 2147469093 1 -> L5.writable RSEGS M 2147469094 1 -> L5.writable RSEGS M 2147469095 1 -> L5.writable RSEGS M 2147469096 4 ->
  L5.writable RSEGS M 2147469100 1 -> L5.writable RSEGS M 2147469100 4 -> L5.writable RSEGS M 2147469101 1 -> L5.writable RSEGS M 2147469102 1 ->
  L5.writable RSEGS M 2147469103 1 ->
  L5.writable RSEGS M 2147612664 184 -> L5.writable RSEGS M 2147612664 1 -> L5.writable RSEGS M 2147612664 4 ->
  L5.writable RSEGS M 2147612665 1 -> L5.writable RSEGS M 2147612666 1 -> L5.writable RSEGS M 2147612667 1 -> L5.writable RSEGS M 2147612668 4 ->
  L5.writable RSEGS M 2147612672 4 -> L5.writable RSEGS M 2147612676 4 -> L5.writable RSEGS M 2147612680 4 -> L5.writable RSEGS M 2147612684 4 ->
  L5.writable RSEGS M 2147612688 4 -> L5.writable RSEGS M 2147612692 8 -> L5.writable RSEGS M 2147612700 8 -> L5.writable RSEGS M 2147612708 8 ->
  L5.writable RSEGS M 2147612716 8 -> L5.writable RSEGS M 2147612724 8 -> L5.writable RSEGS M 2147612732 8 -> L5.writable RSEGS M 2147612740 8 ->
  L5.writable RSEGS M 2147612748 8 -> L5.writable RSEGS M 2147612756 8 -> L5.writable RSEGS M 2147612764 8 -> L5.writable RSEGS M 2147612772 8 ->
  L5.writable RSEGS M 2147612780 8 -> L5.writable RSEGS M 2147612788 8 -> L5.writable RSEGS M 2147612796 8 -> L5.writable RSEGS M 2147612804 8 ->
  L5.writable RSEGS M 2147612812 8 -> L5.writable RSEGS M 2147612820 8 -> L5.writable RSEGS M 2147612828 4 -> L5.writable RSEGS M 2147612828 8 ->
  L5.writable RSEGS M 2147612832 4 -> L5.writable RSEGS M 2147612836 4 -> L5.writable RSEGS M 2147612836 8 -> L5.writable RSEGS M 2147612840 4 ->
  L5.writable RSEGS M 2147612844 4 -> L5.writable RSEGS M 2147612844 8 ->
  L5.u32_at RSEGS M 6765656 (V 44%nat) -> 1 <= (V 44%nat) <= 4194303 -> L5.u32_at RSEGS M 6897520 0 -> L5.u8_at RSEGS M 6897555 0 ->
  L5.u64_at RSEGS M 6896992 6897000 -> L5.u32_at RSEGS M 6896984 4 -> L5.u64_at RSEGS M 6897032 449180 -> L5.u64_at RSEGS M 6897288 0 ->
  L5.u32_at RSEGS M 6896980 0 -> L5.u8_at RSEGS M 1299540 0 -> L5.u64_at RSEGS M 6897024 872740 -> L5.u64_at RSEGS M 6897280 1293304 ->
  L5.u64_at RSEGS M 6897016 1148964 -> L5.u64_at RSEGS M 6897272 687916 -> L5.u8_at RSEGS M 6759060 0 -> L5.u64_at RSEGS M 6897008 1148964 ->
  L5.u64_at RSEGS M 6897264 619876 -> L5.u8_at RSEGS M 1907424 0 -> L5.u64_at RSEGS M 6897000 0 -> L5.u8_at RSEGS M 1295824 0 ->
  L5.u64_at RSEGS M 1282768 1282768 -> L5.u64_at RSEGS M 1295744 1 -> L5.u32_at RSEGS M 1299536 1 -> L5.u64_at RSEGS M 1299696 0 ->
  L5.u8_at RSEGS M 1313048 1 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u64_at RSEGS M 1294272 143808 -> L5.u8_at RSEGS M 1294288 32 ->
  L5.u8_at RSEGS M 1307804 1 -> L5.u64_at RSEGS M 1294288 32 -> L5.u64_at RSEGS M 1906656 18446744073709551615 -> L5.u64_at RSEGS M 1283280 1219844 ->
  L5.u64_at RSEGS M 1294328 18446744073709551615 -> L5.u64_at RSEGS M 1294336 143904 -> L5.u8_at RSEGS M 1294352 32 -> L5.u64_at RSEGS M 1294352 32 ->
  L5.u64_at RSEGS M 1294392 18446744073709551615 -> L5.u64_at RSEGS M 1294400 143936 -> L5.u8_at RSEGS M 1294416 96 -> L5.u64_at RSEGS M 1294416 96 ->
  L5.u64_at RSEGS M 1294456 18446744073709551615 -> L5.u64_at RSEGS M 1294464 144128 -> L5.u8_at RSEGS M 1294480 32 -> L5.u64_at RSEGS M 1294480 32 ->
  L5.u64_at RSEGS M 1294520 18446744073709551615 -> L5.u64_at RSEGS M 1294528 144160 -> L5.u8_at RSEGS M 1294544 64 -> L5.u64_at RSEGS M 1294544 64 ->
  L5.u64_at RSEGS M 1294584 18446744073709551615 -> L5.u64_at RSEGS M 1294592 144224 -> L5.u8_at RSEGS M 1294608 32 -> L5.u64_at RSEGS M 1294608 32 ->
  L5.u64_at RSEGS M 1294648 18446744073709551615 -> L5.u64_at RSEGS M 1294656 144256 -> L5.u8_at RSEGS M 1294672 96 -> L5.u64_at RSEGS M 1294672 96 ->
  L5.u64_at RSEGS M 1294712 18446744073709551615 -> L5.u64_at RSEGS M 1294720 144352 -> L5.u8_at RSEGS M 1294736 96 -> L5.u64_at RSEGS M 1294736 96 ->
  L5.u64_at RSEGS M 1294776 18446744073709551615 -> L5.u64_at RSEGS M 1294784 144448 -> L5.u8_at RSEGS M 1294800 128 -> L5.u64_at RSEGS M 1294800 128 ->
  L5.u64_at RSEGS M 1294840 18446744073709551615 -> L5.u64_at RSEGS M 1294848 144576 -> L5.u8_at RSEGS M 1294864 96 -> L5.u64_at RSEGS M 1294864 96 ->
  L5.u64_at RSEGS M 1294904 18446744073709551615 -> L5.u64_at RSEGS M 1294912 144672 -> L5.u8_at RSEGS M 1294928 64 -> L5.u64_at RSEGS M 1294928 64 ->
  L5.u64_at RSEGS M 1294968 18446744073709551615 -> L5.u64_at RSEGS M 1294976 144736 -> L5.u8_at RSEGS M 1294992 64 -> L5.u64_at RSEGS M 1294992 64 ->
  L5.u64_at RSEGS M 1295032 18446744073709551615 -> L5.u64_at RSEGS M 1295040 144800 -> L5.u8_at RSEGS M 1295056 64 -> L5.u64_at RSEGS M 1295056 64 ->
  L5.u64_at RSEGS M 1295096 18446744073709551615 -> L5.u64_at RSEGS M 1295104 144864 -> L5.u8_at RSEGS M 1295120 64 -> L5.u64_at RSEGS M 1295120 64 ->
  L5.u64_at RSEGS M 1295160 18446744073709551615 -> L5.u64_at RSEGS M 1295168 144928 -> L5.u8_at RSEGS M 1295184 64 -> L5.u64_at RSEGS M 1295184 64 ->
  L5.u64_at RSEGS M 1295224 18446744073709551615 -> L5.u64_at RSEGS M 1295232 144992 -> L5.u8_at RSEGS M 1295248 64 -> L5.u64_at RSEGS M 1295248 64 ->
  L5.u64_at RSEGS M 1295288 18446744073709551615 -> L5.u64_at RSEGS M 1295296 145056 -> L5.u8_at RSEGS M 1295312 64 -> L5.u64_at RSEGS M 1295312 64 ->
  L5.u64_at RSEGS M 1295352 18446744073709551615 -> L5.u64_at RSEGS M 1295360 145120 -> L5.u8_at RSEGS M 1295376 96 -> L5.u64_at RSEGS M 1295376 96 ->
  L5.u64_at RSEGS M 1295416 18446744073709551615 -> L5.u64_at RSEGS M 1295424 145216 -> L5.u8_at RSEGS M 1295440 64 -> L5.u64_at RSEGS M 1295440 64 ->
  L5.u64_at RSEGS M 1295480 18446744073709551615 -> L5.u64_at RSEGS M 1295488 145536 -> L5.u8_at RSEGS M 1295504 96 -> L5.u64_at RSEGS M 1295504 96 ->
  L5.u64_at RSEGS M 1295544 18446744073709551615 -> L5.u64_at RSEGS M 1295552 145632 -> L5.u8_at RSEGS M 1295568 32 -> L5.u64_at RSEGS M 1295568 32 ->
  L5.u64_at RSEGS M 1295608 18446744073709551615 -> L5.u64_at RSEGS M 1295616 145664 -> L5.u8_at RSEGS M 1295632 32 -> L5.u64_at RSEGS M 1295632 32 ->
  L5.u64_at RSEGS M 1295672 18446744073709551615 -> L5.u64_at RSEGS M 1295680 145696 -> L5.u8_at RSEGS M 1295696 96 -> L5.u64_at RSEGS M 1295696 96 ->
  L5.u64_at RSEGS M 1295736 18446744073709551615 ->
  L5.u64_at RSEGS M 6898952 0 -> L5.u64_at RSEGS M 1294224 1293992 -> L5.u32_at RSEGS M 1294132 4294967295 ->
  L5.u64_at RSEGS M 1294032 0 -> L5.u64_at RSEGS M 1294048 0 -> L5.u64_at RSEGS M 1294000 0 -> L5.u64_at RSEGS M 1294008 0 ->
  L5.u64_at RSEGS M 1293984 1293752 -> L5.u32_at RSEGS M 1293892 4294967295 -> L5.u64_at RSEGS M 1293792 6898982 -> L5.u64_at RSEGS M 1293808 6898976 ->
  L5.u64_at RSEGS M 1293824 1180112 -> L5.u64_at RSEGS M 6896960 (V 40%nat) -> L5.u32_at RSEGS M 1293872 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 320) <= bv_unsigned a < ((V 2%nat) - 320) + 320) -> ~ (1295744 <= bv_unsigned a < 1295744 + 8) -> ~ (1295824 <= bv_unsigned a < 1295824 + 1) -> ~ (1299696 <= bv_unsigned a < 1299696 + 8) -> ~ (6896976 <= bv_unsigned a < 6896976 + 1) -> ~ (6896984 <= bv_unsigned a < 6896984 + 4) -> ~ (6896992 <= bv_unsigned a < 6896992 + 8) -> ~ (6897520 <= bv_unsigned a < 6897520 + 4) -> ~ (2147468856 <= bv_unsigned a < 2147468856 + 1) -> ~ (2147468857 <= bv_unsigned a < 2147468857 + 1) -> ~ (2147468858 <= bv_unsigned a < 2147468858 + 1) -> ~ (2147468859 <= bv_unsigned a < 2147468859 + 1) -> ~ (2147468868 <= bv_unsigned a < 2147468868 + 1) -> ~ (2147468869 <= bv_unsigned a < 2147468869 + 1) -> ~ (2147468870 <= bv_unsigned a < 2147468870 + 1) -> ~ (2147468871 <= bv_unsigned a < 2147468871 + 1) -> ~ (2147468872 <= bv_unsigned a < 2147468872 + 1) -> ~ (2147468872 <= bv_unsigned a < 2147468872 + 4) -> ~ (2147468873 <= bv_unsigned a < 2147468873 + 1) -> ~ (2147468874 <= bv_unsigned a < 2147468874 + 1) -> ~ (2147468875 <= bv_unsigned a < 2147468875 + 1) -> ~ (2147468876 <= bv_unsigned a < 2147468876 + 4) -> ~ (2147468880 <= bv_unsigned a < 2147468880 + 1) -> ~ (2147468880 <= bv_unsigned a < 2147468880 + 4) -> ~ (2147468881 <= bv_unsigned a < 2147468881 + 1) -> ~ (2147468882 <= bv_unsigned a < 2147468882 + 1) -> ~ (2147468883 <= bv_unsigned a < 2147468883 + 1) -> ~ (2147468896 <= bv_unsigned a < 2147468896 + 1) -> ~ (2147468897 <= bv_unsigned a < 2147468897 + 1) -> ~ (2147468898 <= bv_unsigned a < 2147468898 + 1) -> ~ (2147468899 <= bv_unsigned a < 2147468899 + 1) -> ~ (2147468900 <= bv_unsigned a < 2147468900 + 1) -> ~ (2147468901 <= bv_unsigned a < 2147468901 + 1) -> ~ (2147468902 <= bv_unsigned a < 2147468902 + 1) -> ~ (2147468903 <= bv_unsigned a < 2147468903 + 1) -> ~ (2147468904 <= bv_unsigned a < 2147468904 + 1) -> ~ (2147468905 <= bv_unsigned a < 2147468905 + 1) -> ~ (2147468906 <= bv_unsigned a < 2147468906 + 1) -> ~ (2147468907 <= bv_unsigned a < 2147468907 + 1) -> ~ (2147468908 <= bv_unsigned a < 2147468908 + 1) -> ~ (2147468909 <= bv_unsigned a < 2147468909 + 1) -> ~ (2147468910 <= bv_unsigned a < 2147468910 + 1) -> ~ (2147468911 <= bv_unsigned a < 2147468911 + 1) -> ~ (2147468912 <= bv_unsigned a < 2147468912 + 1) -> ~ (2147468912 <= bv_unsigned a < 2147468912 + 4) -> ~ (2147468913 <= bv_unsigned a < 2147468913 + 1) -> ~ (2147468914 <= bv_unsigned a < 2147468914 + 1) -> ~ (2147468915 <= bv_unsigned a < 2147468915 + 1) -> ~ (2147468916 <= bv_unsigned a < 2147468916 + 4) -> ~ (2147468920 <= bv_unsigned a < 2147468920 + 1) -> ~ (2147468920 <= bv_unsigned a < 2147468920 + 4) -> ~ (2147468921 <= bv_unsigned a < 2147468921 + 1) -> ~ (2147468922 <= bv_unsigned a < 2147468922 + 1) -> ~ (2147468923 <= bv_unsigned a < 2147468923 + 1) -> ~ (2147468924 <= bv_unsigned a < 2147468924 + 1) -> ~ (2147468924 <= bv_unsigned a < 2147468924 + 4) -> ~ (2147468925 <= bv_unsigned a < 2147468925 + 1) -> ~ (2147468926 <= bv_unsigned a < 2147468926 + 1) -> ~ (2147468927 <= bv_unsigned a < 2147468927 + 1) -> ~ (2147468928 <= bv_unsigned a < 2147468928 + 4) -> ~ (2147468932 <= bv_unsigned a < 2147468932 + 1) -> ~ (2147468932 <= bv_unsigned a < 2147468932 + 4) -> ~ (2147468933 <= bv_unsigned a < 2147468933 + 1) -> ~ (2147468934 <= bv_unsigned a < 2147468934 + 1) -> ~ (2147468935 <= bv_unsigned a < 2147468935 + 1) -> ~ (2147468936 <= bv_unsigned a < 2147468936 + 1) -> ~ (2147468936 <= bv_unsigned a < 2147468936 + 4) -> ~ (2147468937 <= bv_unsigned a < 2147468937 + 1) -> ~ (2147468938 <= bv_unsigned a < 2147468938 + 1) -> ~ (2147468939 <= bv_unsigned a < 2147468939 + 1) -> ~ (2147468940 <= bv_unsigned a < 2147468940 + 4) -> ~ (2147468944 <= bv_unsigned a < 2147468944 + 4) -> ~ (2147468948 <= bv_unsigned a < 2147468948 + 1) -> ~ (2147468948 <= bv_unsigned a < 2147468948 + 4) -> ~ (2147468949 <= bv_unsigned a < 2147468949 + 1) -> ~ (2147468950 <= bv_unsigned a < 2147468950 + 1) -> ~ (2147468951 <= bv_unsigned a < 2147468951 + 1) -> ~ (2147468952 <= bv_unsigned a < 2147468952 + 1) -> ~ (2147468952 <= bv_unsigned a < 2147468952 + 4) -> ~ (2147468953 <= bv_unsigned a < 2147468953 + 1) -> ~ (2147468954 <= bv_unsigned a < 2147468954 + 1) -> ~ (2147468955 <= bv_unsigned a < 2147468955 + 1) -> ~ (2147468956 <= bv_unsigned a < 2147468956 + 4) -> ~ (2147468960 <= bv_unsigned a < 2147468960 + 1) -> ~ (2147468960 <= bv_unsigned a < 2147468960 + 4) -> ~ (2147468961 <= bv_unsigned a < 2147468961 + 1) -> ~ (2147468962 <= bv_unsigned a < 2147468962 + 1) -> ~ (2147468963 <= bv_unsigned a < 2147468963 + 1) -> ~ (2147468964 <= bv_unsigned a < 2147468964 + 1) -> ~ (2147468965 <= bv_unsigned a < 2147468965 + 1) -> ~ (2147468966 <= bv_unsigned a < 2147468966 + 1) -> ~ (2147468967 <= bv_unsigned a < 2147468967 + 1) -> ~ (2147468968 <= bv_unsigned a < 2147468968 + 1) -> ~ (2147468969 <= bv_unsigned a < 2147468969 + 1) -> ~ (2147468970 <= bv_unsigned a < 2147468970 + 1) -> ~ (2147468971 <= bv_unsigned a < 2147468971 + 1) -> ~ (2147468972 <= bv_unsigned a < 2147468972 + 1) -> ~ (2147468973 <= bv_unsigned a < 2147468973 + 1) -> ~ (2147468974 <= bv_unsigned a < 2147468974 + 1) -> ~ (2147468975 <= bv_unsigned a < 2147468975 + 1) -> ~ (2147468976 <= bv_unsigned a < 2147468976 + 1) -> ~ (2147468977 <= bv_unsigned a < 2147468977 + 1) -> ~ (2147468978 <= bv_unsigned a < 2147468978 + 1) -> ~ (2147468979 <= bv_unsigned a < 2147468979 + 1) -> ~ (2147468980 <= bv_unsigned a < 2147468980 + 1) -> ~ (2147468981 <= bv_unsigned a < 2147468981 + 1) -> ~ (2147468982 <= bv_unsigned a < 2147468982 + 1) -> ~ (2147468983 <= bv_unsigned a < 2147468983 + 1) -> ~ (2147468984 <= bv_unsigned a < 2147468984 + 1) -> ~ (2147468985 <= bv_unsigned a < 2147468985 + 1) -> ~ (2147468986 <= bv_unsigned a < 2147468986 + 1) -> ~ (2147468987 <= bv_unsigned a < 2147468987 + 1) -> ~ (2147468988 <= bv_unsigned a < 2147468988 + 1) -> ~ (2147468989 <= bv_unsigned a < 2147468989 + 1) -> ~ (2147468990 <= bv_unsigned a < 2147468990 + 1) -> ~ (2147468991 <= bv_unsigned a < 2147468991 + 1) -> ~ (2147468992 <= bv_unsigned a < 2147468992 + 1) -> ~ (2147468993 <= bv_unsigned a < 2147468993 + 1) -> ~ (2147468994 <= bv_unsigned a < 2147468994 + 1) -> ~ (2147468995 <= bv_unsigned a < 2147468995 + 1) -> ~ (2147468996 <= bv_unsigned a < 2147468996 + 1) -> ~ (2147468997 <= bv_unsigned a < 2147468997 + 1) -> ~ (2147468998 <= bv_unsigned a < 2147468998 + 1) -> ~ (2147468999 <= bv_unsigned a < 2147468999 + 1) -> ~ (2147469000 <= bv_unsigned a < 2147469000 + 1) -> ~ (2147469001 <= bv_unsigned a < 2147469001 + 1) -> ~ (2147469002 <= bv_unsigned a < 2147469002 + 1) -> ~ (2147469003 <= bv_unsigned a < 2147469003 + 1) -> ~ (2147469004 <= bv_unsigned a < 2147469004 + 1) -> ~ (2147469005 <= bv_unsigned a < 2147469005 + 1) -> ~ (2147469006 <= bv_unsigned a < 2147469006 + 1) -> ~ (2147469007 <= bv_unsigned a < 2147469007 + 1) -> ~ (2147469008 <= bv_unsigned a < 2147469008 + 1) -> ~ (2147469009 <= bv_unsigned a < 2147469009 + 1) -> ~ (2147469010 <= bv_unsigned a < 2147469010 + 1) -> ~ (2147469011 <= bv_unsigned a < 2147469011 + 1) -> ~ (2147469012 <= bv_unsigned a < 2147469012 + 1) -> ~ (2147469013 <= bv_unsigned a < 2147469013 + 1) -> ~ (2147469014 <= bv_unsigned a < 2147469014 + 1) -> ~ (2147469015 <= bv_unsigned a < 2147469015 + 1) -> ~ (2147469016 <= bv_unsigned a < 2147469016 + 1) -> ~ (2147469017 <= bv_unsigned a < 2147469017 + 1) -> ~ (2147469018 <= bv_unsigned a < 2147469018 + 1) -> ~ (2147469019 <= bv_unsigned a < 2147469019 + 1) -> ~ (2147469020 <= bv_unsigned a < 2147469020 + 1) -> ~ (2147469020 <= bv_unsigned a < 2147469020 + 4) -> ~ (2147469021 <= bv_unsigned a < 2147469021 + 1) -> ~ (2147469022 <= bv_unsigned a < 2147469022 + 1) -> ~ (2147469023 <= bv_unsigned a < 2147469023 + 1) -> ~ (2147469024 <= bv_unsigned a < 2147469024 + 4) -> ~ (2147469028 <= bv_unsigned a < 2147469028 + 1) -> ~ (2147469028 <= bv_unsigned a < 2147469028 + 4) -> ~ (2147469029 <= bv_unsigned a < 2147469029 + 1) -> ~ (2147469030 <= bv_unsigned a < 2147469030 + 1) -> ~ (2147469031 <= bv_unsigned a < 2147469031 + 1) -> ~ (2147469032 <= bv_unsigned a < 2147469032 + 1) -> ~ (2147469033 <= bv_unsigned a < 2147469033 + 1) -> ~ (2147469034 <= bv_unsigned a < 2147469034 + 1) -> ~ (2147469035 <= bv_unsigned a < 2147469035 + 1) -> ~ (2147469036 <= bv_unsigned a < 2147469036 + 1) -> ~ (2147469037 <= bv_unsigned a < 2147469037 + 1) -> ~ (2147469038 <= bv_unsigned a < 2147469038 + 1) -> ~ (2147469039 <= bv_unsigned a < 2147469039 + 1) -> ~ (2147469072 <= bv_unsigned a < 2147469072 + 1) -> ~ (2147469072 <= bv_unsigned a < 2147469072 + 4) -> ~ (2147469073 <= bv_unsigned a < 2147469073 + 1) -> ~ (2147469074 <= bv_unsigned a < 2147469074 + 1) -> ~ (2147469075 <= bv_unsigned a < 2147469075 + 1) -> ~ (2147469076 <= bv_unsigned a < 2147469076 + 4) -> ~ (2147469080 <= bv_unsigned a < 2147469080 + 1) -> ~ (2147469080 <= bv_unsigned a < 2147469080 + 4) -> ~ (2147469081 <= bv_unsigned a < 2147469081 + 1) -> ~ (2147469082 <= bv_unsigned a < 2147469082 + 1) -> ~ (2147469083 <= bv_unsigned a < 2147469083 + 1) -> ~ (2147469084 <= bv_unsigned a < 2147469084 + 1) -> ~ (2147469085 <= bv_unsigned a < 2147469085 + 1) -> ~ (2147469086 <= bv_unsigned a < 2147469086 + 1) -> ~ (2147469087 <= bv_unsigned a < 2147469087 + 1) -> ~ (2147469088 <= bv_unsigned a < 2147469088 + 1) -> ~ (2147469089 <= bv_unsigned a < 2147469089 + 1) -> ~ (2147469090 <= bv_unsigned a < 2147469090 + 1) -> ~ (2147469091 <= bv_unsigned a < 2147469091 + 1) -> ~ (2147469092 <= bv_unsigned a < 2147469092 + 1) -> ~ (2147469092 <= bv_unsigned a < 2147469092 + 4) -> ~ (2147469093 <= bv_unsigned a < 2147469093 + 1) -> ~ (2147469094 <= bv_unsigned a < 2147469094 + 1) -> ~ (2147469095 <= bv_unsigned a < 2147469095 + 1) -> ~ (2147469096 <= bv_unsigned a < 2147469096 + 4) -> ~ (2147469100 <= bv_unsigned a < 2147469100 + 1) -> ~ (2147469100 <= bv_unsigned a < 2147469100 + 4) -> ~ (2147469101 <= bv_unsigned a < 2147469101 + 1) -> ~ (2147469102 <= bv_unsigned a < 2147469102 + 1) -> ~ (2147469103 <= bv_unsigned a < 2147469103 + 1) -> ~ (2147612664 <= bv_unsigned a < 2147612664 + 184) -> ~ (2147612664 <= bv_unsigned a < 2147612664 + 1) -> ~ (2147612664 <= bv_unsigned a < 2147612664 + 4) -> ~ (2147612665 <= bv_unsigned a < 2147612665 + 1) -> ~ (2147612666 <= bv_unsigned a < 2147612666 + 1) -> ~ (2147612667 <= bv_unsigned a < 2147612667 + 1) -> ~ (2147612668 <= bv_unsigned a < 2147612668 + 4) -> ~ (2147612672 <= bv_unsigned a < 2147612672 + 4) -> ~ (2147612676 <= bv_unsigned a < 2147612676 + 4) -> ~ (2147612680 <= bv_unsigned a < 2147612680 + 4) -> ~ (2147612684 <= bv_unsigned a < 2147612684 + 4) -> ~ (2147612688 <= bv_unsigned a < 2147612688 + 4) -> ~ (2147612692 <= bv_unsigned a < 2147612692 + 8) -> ~ (2147612700 <= bv_unsigned a < 2147612700 + 8) -> ~ (2147612708 <= bv_unsigned a < 2147612708 + 8) -> ~ (2147612716 <= bv_unsigned a < 2147612716 + 8) -> ~ (2147612724 <= bv_unsigned a < 2147612724 + 8) -> ~ (2147612732 <= bv_unsigned a < 2147612732 + 8) -> ~ (2147612740 <= bv_unsigned a < 2147612740 + 8) -> ~ (2147612748 <= bv_unsigned a < 2147612748 + 8) -> ~ (2147612756 <= bv_unsigned a < 2147612756 + 8) -> ~ (2147612764 <= bv_unsigned a < 2147612764 + 8) -> ~ (2147612772 <= bv_unsigned a < 2147612772 + 8) -> ~ (2147612780 <= bv_unsigned a < 2147612780 + 8) -> ~ (2147612788 <= bv_unsigned a < 2147612788 + 8) -> ~ (2147612796 <= bv_unsigned a < 2147612796 + 8) -> ~ (2147612804 <= bv_unsigned a < 2147612804 + 8) -> ~ (2147612812 <= bv_unsigned a < 2147612812 + 8) -> ~ (2147612820 <= bv_unsigned a < 2147612820 + 8) -> ~ (2147612828 <= bv_unsigned a < 2147612828 + 4) -> ~ (2147612828 <= bv_unsigned a < 2147612828 + 8) -> ~ (2147612832 <= bv_unsigned a < 2147612832 + 4) -> ~ (2147612836 <= bv_unsigned a < 2147612836 + 4) -> ~ (2147612836 <= bv_unsigned a < 2147612836 + 8) -> ~ (2147612840 <= bv_unsigned a < 2147612840 + 4) -> ~ (2147612844 <= bv_unsigned a < 2147612844 + 4) -> ~ (2147612844 <= bv_unsigned a < 2147612844 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 320) <= i < ((V 2%nat) - 320) + 320) -> ~ (1295744 <= i < 1295744 + 8) -> ~ (1295824 <= i < 1295824 + 1) -> ~ (1299696 <= i < 1299696 + 8) -> ~ (6896976 <= i < 6896976 + 1) -> ~ (6896984 <= i < 6896984 + 4) -> ~ (6896992 <= i < 6896992 + 8) -> ~ (6897520 <= i < 6897520 + 4) -> ~ (2147468856 <= i < 2147468856 + 1) -> ~ (2147468857 <= i < 2147468857 + 1) -> ~ (2147468858 <= i < 2147468858 + 1) -> ~ (2147468859 <= i < 2147468859 + 1) -> ~ (2147468868 <= i < 2147468868 + 1) -> ~ (2147468869 <= i < 2147468869 + 1) -> ~ (2147468870 <= i < 2147468870 + 1) -> ~ (2147468871 <= i < 2147468871 + 1) -> ~ (2147468872 <= i < 2147468872 + 1) -> ~ (2147468872 <= i < 2147468872 + 4) -> ~ (2147468873 <= i < 2147468873 + 1) -> ~ (2147468874 <= i < 2147468874 + 1) -> ~ (2147468875 <= i < 2147468875 + 1) -> ~ (2147468876 <= i < 2147468876 + 4) -> ~ (2147468880 <= i < 2147468880 + 1) -> ~ (2147468880 <= i < 2147468880 + 4) -> ~ (2147468881 <= i < 2147468881 + 1) -> ~ (2147468882 <= i < 2147468882 + 1) -> ~ (2147468883 <= i < 2147468883 + 1) -> ~ (2147468896 <= i < 2147468896 + 1) -> ~ (2147468897 <= i < 2147468897 + 1) -> ~ (2147468898 <= i < 2147468898 + 1) -> ~ (2147468899 <= i < 2147468899 + 1) -> ~ (2147468900 <= i < 2147468900 + 1) -> ~ (2147468901 <= i < 2147468901 + 1) -> ~ (2147468902 <= i < 2147468902 + 1) -> ~ (2147468903 <= i < 2147468903 + 1) -> ~ (2147468904 <= i < 2147468904 + 1) -> ~ (2147468905 <= i < 2147468905 + 1) -> ~ (2147468906 <= i < 2147468906 + 1) -> ~ (2147468907 <= i < 2147468907 + 1) -> ~ (2147468908 <= i < 2147468908 + 1) -> ~ (2147468909 <= i < 2147468909 + 1) -> ~ (2147468910 <= i < 2147468910 + 1) -> ~ (2147468911 <= i < 2147468911 + 1) -> ~ (2147468912 <= i < 2147468912 + 1) -> ~ (2147468912 <= i < 2147468912 + 4) -> ~ (2147468913 <= i < 2147468913 + 1) -> ~ (2147468914 <= i < 2147468914 + 1) -> ~ (2147468915 <= i < 2147468915 + 1) -> ~ (2147468916 <= i < 2147468916 + 4) -> ~ (2147468920 <= i < 2147468920 + 1) -> ~ (2147468920 <= i < 2147468920 + 4) -> ~ (2147468921 <= i < 2147468921 + 1) -> ~ (2147468922 <= i < 2147468922 + 1) -> ~ (2147468923 <= i < 2147468923 + 1) -> ~ (2147468924 <= i < 2147468924 + 1) -> ~ (2147468924 <= i < 2147468924 + 4) -> ~ (2147468925 <= i < 2147468925 + 1) -> ~ (2147468926 <= i < 2147468926 + 1) -> ~ (2147468927 <= i < 2147468927 + 1) -> ~ (2147468928 <= i < 2147468928 + 4) -> ~ (2147468932 <= i < 2147468932 + 1) -> ~ (2147468932 <= i < 2147468932 + 4) -> ~ (2147468933 <= i < 2147468933 + 1) -> ~ (2147468934 <= i < 2147468934 + 1) -> ~ (2147468935 <= i < 2147468935 + 1) -> ~ (2147468936 <= i < 2147468936 + 1) -> ~ (2147468936 <= i < 2147468936 + 4) -> ~ (2147468937 <= i < 2147468937 + 1) -> ~ (2147468938 <= i < 2147468938 + 1) -> ~ (2147468939 <= i < 2147468939 + 1) -> ~ (2147468940 <= i < 2147468940 + 4) -> ~ (2147468944 <= i < 2147468944 + 4) -> ~ (2147468948 <= i < 2147468948 + 1) -> ~ (2147468948 <= i < 2147468948 + 4) -> ~ (2147468949 <= i < 2147468949 + 1) -> ~ (2147468950 <= i < 2147468950 + 1) -> ~ (2147468951 <= i < 2147468951 + 1) -> ~ (2147468952 <= i < 2147468952 + 1) -> ~ (2147468952 <= i < 2147468952 + 4) -> ~ (2147468953 <= i < 2147468953 + 1) -> ~ (2147468954 <= i < 2147468954 + 1) -> ~ (2147468955 <= i < 2147468955 + 1) -> ~ (2147468956 <= i < 2147468956 + 4) -> ~ (2147468960 <= i < 2147468960 + 1) -> ~ (2147468960 <= i < 2147468960 + 4) -> ~ (2147468961 <= i < 2147468961 + 1) -> ~ (2147468962 <= i < 2147468962 + 1) -> ~ (2147468963 <= i < 2147468963 + 1) -> ~ (2147468964 <= i < 2147468964 + 1) -> ~ (2147468965 <= i < 2147468965 + 1) -> ~ (2147468966 <= i < 2147468966 + 1) -> ~ (2147468967 <= i < 2147468967 + 1) -> ~ (2147468968 <= i < 2147468968 + 1) -> ~ (2147468969 <= i < 2147468969 + 1) -> ~ (2147468970 <= i < 2147468970 + 1) -> ~ (2147468971 <= i < 2147468971 + 1) -> ~ (2147468972 <= i < 2147468972 + 1) -> ~ (2147468973 <= i < 2147468973 + 1) -> ~ (2147468974 <= i < 2147468974 + 1) -> ~ (2147468975 <= i < 2147468975 + 1) -> ~ (2147468976 <= i < 2147468976 + 1) -> ~ (2147468977 <= i < 2147468977 + 1) -> ~ (2147468978 <= i < 2147468978 + 1) -> ~ (2147468979 <= i < 2147468979 + 1) -> ~ (2147468980 <= i < 2147468980 + 1) -> ~ (2147468981 <= i < 2147468981 + 1) -> ~ (2147468982 <= i < 2147468982 + 1) -> ~ (2147468983 <= i < 2147468983 + 1) -> ~ (2147468984 <= i < 2147468984 + 1) -> ~ (2147468985 <= i < 2147468985 + 1) -> ~ (2147468986 <= i < 2147468986 + 1) -> ~ (2147468987 <= i < 2147468987 + 1) -> ~ (2147468988 <= i < 2147468988 + 1) -> ~ (2147468989 <= i < 2147468989 + 1) -> ~ (2147468990 <= i < 2147468990 + 1) -> ~ (2147468991 <= i < 2147468991 + 1) -> ~ (2147468992 <= i < 2147468992 + 1) -> ~ (2147468993 <= i < 2147468993 + 1) -> ~ (2147468994 <= i < 2147468994 + 1) -> ~ (2147468995 <= i < 2147468995 + 1) -> ~ (2147468996 <= i < 2147468996 + 1) -> ~ (2147468997 <= i < 2147468997 + 1) -> ~ (2147468998 <= i < 2147468998 + 1) -> ~ (2147468999 <= i < 2147468999 + 1) -> ~ (2147469000 <= i < 2147469000 + 1) -> ~ (2147469001 <= i < 2147469001 + 1) -> ~ (2147469002 <= i < 2147469002 + 1) -> ~ (2147469003 <= i < 2147469003 + 1) -> ~ (2147469004 <= i < 2147469004 + 1) -> ~ (2147469005 <= i < 2147469005 + 1) -> ~ (2147469006 <= i < 2147469006 + 1) -> ~ (2147469007 <= i < 2147469007 + 1) -> ~ (2147469008 <= i < 2147469008 + 1) -> ~ (2147469009 <= i < 2147469009 + 1) -> ~ (2147469010 <= i < 2147469010 + 1) -> ~ (2147469011 <= i < 2147469011 + 1) -> ~ (2147469012 <= i < 2147469012 + 1) -> ~ (2147469013 <= i < 2147469013 + 1) -> ~ (2147469014 <= i < 2147469014 + 1) -> ~ (2147469015 <= i < 2147469015 + 1) -> ~ (2147469016 <= i < 2147469016 + 1) -> ~ (2147469017 <= i < 2147469017 + 1) -> ~ (2147469018 <= i < 2147469018 + 1) -> ~ (2147469019 <= i < 2147469019 + 1) -> ~ (2147469020 <= i < 2147469020 + 1) -> ~ (2147469020 <= i < 2147469020 + 4) -> ~ (2147469021 <= i < 2147469021 + 1) -> ~ (2147469022 <= i < 2147469022 + 1) -> ~ (2147469023 <= i < 2147469023 + 1) -> ~ (2147469024 <= i < 2147469024 + 4) -> ~ (2147469028 <= i < 2147469028 + 1) -> ~ (2147469028 <= i < 2147469028 + 4) -> ~ (2147469029 <= i < 2147469029 + 1) -> ~ (2147469030 <= i < 2147469030 + 1) -> ~ (2147469031 <= i < 2147469031 + 1) -> ~ (2147469032 <= i < 2147469032 + 1) -> ~ (2147469033 <= i < 2147469033 + 1) -> ~ (2147469034 <= i < 2147469034 + 1) -> ~ (2147469035 <= i < 2147469035 + 1) -> ~ (2147469036 <= i < 2147469036 + 1) -> ~ (2147469037 <= i < 2147469037 + 1) -> ~ (2147469038 <= i < 2147469038 + 1) -> ~ (2147469039 <= i < 2147469039 + 1) -> ~ (2147469072 <= i < 2147469072 + 1) -> ~ (2147469072 <= i < 2147469072 + 4) -> ~ (2147469073 <= i < 2147469073 + 1) -> ~ (2147469074 <= i < 2147469074 + 1) -> ~ (2147469075 <= i < 2147469075 + 1) -> ~ (2147469076 <= i < 2147469076 + 4) -> ~ (2147469080 <= i < 2147469080 + 1) -> ~ (2147469080 <= i < 2147469080 + 4) -> ~ (2147469081 <= i < 2147469081 + 1) -> ~ (2147469082 <= i < 2147469082 + 1) -> ~ (2147469083 <= i < 2147469083 + 1) -> ~ (2147469084 <= i < 2147469084 + 1) -> ~ (2147469085 <= i < 2147469085 + 1) -> ~ (2147469086 <= i < 2147469086 + 1) -> ~ (2147469087 <= i < 2147469087 + 1) -> ~ (2147469088 <= i < 2147469088 + 1) -> ~ (2147469089 <= i < 2147469089 + 1) -> ~ (2147469090 <= i < 2147469090 + 1) -> ~ (2147469091 <= i < 2147469091 + 1) -> ~ (2147469092 <= i < 2147469092 + 1) -> ~ (2147469092 <= i < 2147469092 + 4) -> ~ (2147469093 <= i < 2147469093 + 1) -> ~ (2147469094 <= i < 2147469094 + 1) -> ~ (2147469095 <= i < 2147469095 + 1) -> ~ (2147469096 <= i < 2147469096 + 4) -> ~ (2147469100 <= i < 2147469100 + 1) -> ~ (2147469100 <= i < 2147469100 + 4) -> ~ (2147469101 <= i < 2147469101 + 1) -> ~ (2147469102 <= i < 2147469102 + 1) -> ~ (2147469103 <= i < 2147469103 + 1) -> ~ (2147612664 <= i < 2147612664 + 184) -> ~ (2147612664 <= i < 2147612664 + 1) -> ~ (2147612664 <= i < 2147612664 + 4) -> ~ (2147612665 <= i < 2147612665 + 1) -> ~ (2147612666 <= i < 2147612666 + 1) -> ~ (2147612667 <= i < 2147612667 + 1) -> ~ (2147612668 <= i < 2147612668 + 4) -> ~ (2147612672 <= i < 2147612672 + 4) -> ~ (2147612676 <= i < 2147612676 + 4) -> ~ (2147612680 <= i < 2147612680 + 4) -> ~ (2147612684 <= i < 2147612684 + 4) -> ~ (2147612688 <= i < 2147612688 + 4) -> ~ (2147612692 <= i < 2147612692 + 8) -> ~ (2147612700 <= i < 2147612700 + 8) -> ~ (2147612708 <= i < 2147612708 + 8) -> ~ (2147612716 <= i < 2147612716 + 8) -> ~ (2147612724 <= i < 2147612724 + 8) -> ~ (2147612732 <= i < 2147612732 + 8) -> ~ (2147612740 <= i < 2147612740 + 8) -> ~ (2147612748 <= i < 2147612748 + 8) -> ~ (2147612756 <= i < 2147612756 + 8) -> ~ (2147612764 <= i < 2147612764 + 8) -> ~ (2147612772 <= i < 2147612772 + 8) -> ~ (2147612780 <= i < 2147612780 + 8) -> ~ (2147612788 <= i < 2147612788 + 8) -> ~ (2147612796 <= i < 2147612796 + 8) -> ~ (2147612804 <= i < 2147612804 + 8) -> ~ (2147612812 <= i < 2147612812 + 8) -> ~ (2147612820 <= i < 2147612820 + 8) -> ~ (2147612828 <= i < 2147612828 + 4) -> ~ (2147612828 <= i < 2147612828 + 8) -> ~ (2147612832 <= i < 2147612832 + 4) -> ~ (2147612836 <= i < 2147612836 + 4) -> ~ (2147612836 <= i < 2147612836 + 8) -> ~ (2147612840 <= i < 2147612840 + 4) -> ~ (2147612844 <= i < 2147612844 + 4) -> ~ (2147612844 <= i < 2147612844 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x118878 M) (st fx' R' 0x120258 M')
        /\ (forall x, In x KS_dpX4B_pre -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1181792
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 6) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 7) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 9) = Z_to_bv 64 1293752
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 6
        /\ getr R' (reg 14) = Z_to_bv 64 17293822569102704639
        /\ getr R' (reg 15) = Z_to_bv 64 1152920405095219200
        /\ getr R' (reg 16) = Z_to_bv 64 18446742974197923840
        /\ getr R' (reg 17) = Z_to_bv 64 66
        /\ getr R' (reg 18) = Z_to_bv 64 2
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 21) = Z_to_bv 64 6896960
        /\ getr R' (reg 22) = Z_to_bv 64 6
        /\ getr R' (reg 28) = Z_to_bv 64 1299632
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 6
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 6898976
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 1293752
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 1181792
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 10)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) 1149156
        /\ L5.u64_at RSEGS M' 1295744 0
        /\ L5.u64_at RSEGS M' 1299696 0
        /\ L5.u64_at RSEGS M' 2147612840 0
        /\ L5.u64_at RSEGS M' 2147612832 0
        /\ L5.u64_at RSEGS M' 2147612824 0
        /\ L5.u64_at RSEGS M' 2147612816 0
        /\ L5.u64_at RSEGS M' 2147612808 0
        /\ L5.u64_at RSEGS M' 2147612800 0
        /\ L5.u64_at RSEGS M' 2147612792 0
        /\ L5.u64_at RSEGS M' 2147612784 0
        /\ L5.u64_at RSEGS M' 2147612776 0
        /\ L5.u64_at RSEGS M' 2147612768 0
        /\ L5.u64_at RSEGS M' 2147612760 0
        /\ L5.u64_at RSEGS M' 2147612752 0
        /\ L5.u64_at RSEGS M' 2147612744 0
        /\ L5.u64_at RSEGS M' 2147612736 0
        /\ L5.u64_at RSEGS M' 2147612728 0
        /\ L5.u64_at RSEGS M' 2147612720 0
        /\ L5.u64_at RSEGS M' 2147612712 0
        /\ L5.u64_at RSEGS M' 2147612704 0
        /\ L5.u64_at RSEGS M' 2147612696 0
        /\ L5.u64_at RSEGS M' 2147612688 0
        /\ L5.u32_at RSEGS M' 2147612684 0
        /\ L5.u32_at RSEGS M' 2147612680 0
        /\ L5.u32_at RSEGS M' 2147612676 0
        /\ L5.u32_at RSEGS M' 2147612672 0
        /\ L5.u32_at RSEGS M' 2147612668 0
        /\ L5.u32_at RSEGS M' 2147612664 0
        /\ L5.u32_at RSEGS M' 2147469096 0
        /\ L5.u32_at RSEGS M' 2147469092 0
        /\ L5.u32_at RSEGS M' 2147469100 0
        /\ L5.u8_at RSEGS M' 2147469090 0
        /\ L5.u8_at RSEGS M' 2147469089 0
        /\ L5.u8_at RSEGS M' 2147469091 0
        /\ L5.u8_at RSEGS M' 2147469088 0
        /\ L5.u8_at RSEGS M' 2147469086 0
        /\ L5.u8_at RSEGS M' 2147469085 0
        /\ L5.u8_at RSEGS M' 2147469087 0
        /\ L5.u8_at RSEGS M' 2147469084 0
        /\ L5.u32_at RSEGS M' 2147469076 0
        /\ L5.u32_at RSEGS M' 2147469072 0
        /\ L5.u32_at RSEGS M' 2147469080 0
        /\ L5.u8_at RSEGS M' 2147469036 0
        /\ L5.u8_at RSEGS M' 2147469035 0
        /\ L5.u8_at RSEGS M' 2147469038 0
        /\ L5.u8_at RSEGS M' 2147469037 0
        /\ L5.u8_at RSEGS M' 2147469034 0
        /\ L5.u8_at RSEGS M' 2147469033 0
        /\ L5.u8_at RSEGS M' 2147469039 0
        /\ L5.u8_at RSEGS M' 2147469032 0
        /\ L5.u32_at RSEGS M' 2147469024 0
        /\ L5.u32_at RSEGS M' 2147469020 0
        /\ L5.u32_at RSEGS M' 2147469028 0
        /\ L5.u8_at RSEGS M' 2147469016 0
        /\ L5.u8_at RSEGS M' 2147469015 0
        /\ L5.u8_at RSEGS M' 2147469018 0
        /\ L5.u8_at RSEGS M' 2147469017 0
        /\ L5.u8_at RSEGS M' 2147469014 0
        /\ L5.u8_at RSEGS M' 2147469013 0
        /\ L5.u8_at RSEGS M' 2147469019 0
        /\ L5.u8_at RSEGS M' 2147469012 0
        /\ L5.u8_at RSEGS M' 2147469008 0
        /\ L5.u8_at RSEGS M' 2147469007 0
        /\ L5.u8_at RSEGS M' 2147469010 0
        /\ L5.u8_at RSEGS M' 2147469009 0
        /\ L5.u8_at RSEGS M' 2147469006 0
        /\ L5.u8_at RSEGS M' 2147469005 0
        /\ L5.u8_at RSEGS M' 2147469011 0
        /\ L5.u8_at RSEGS M' 2147469004 0
        /\ L5.u8_at RSEGS M' 2147469000 0
        /\ L5.u8_at RSEGS M' 2147468999 0
        /\ L5.u8_at RSEGS M' 2147469002 0
        /\ L5.u8_at RSEGS M' 2147469001 0
        /\ L5.u8_at RSEGS M' 2147468998 0
        /\ L5.u8_at RSEGS M' 2147468997 0
        /\ L5.u8_at RSEGS M' 2147469003 0
        /\ L5.u8_at RSEGS M' 2147468996 0
        /\ L5.u8_at RSEGS M' 2147468992 0
        /\ L5.u8_at RSEGS M' 2147468991 0
        /\ L5.u8_at RSEGS M' 2147468994 0
        /\ L5.u8_at RSEGS M' 2147468993 0
        /\ L5.u8_at RSEGS M' 2147468990 0
        /\ L5.u8_at RSEGS M' 2147468989 0
        /\ L5.u8_at RSEGS M' 2147468995 0
        /\ L5.u8_at RSEGS M' 2147468988 0
        /\ L5.u8_at RSEGS M' 2147468984 0
        /\ L5.u8_at RSEGS M' 2147468983 0
        /\ L5.u8_at RSEGS M' 2147468986 0
        /\ L5.u8_at RSEGS M' 2147468985 0
        /\ L5.u8_at RSEGS M' 2147468982 0
        /\ L5.u8_at RSEGS M' 2147468981 0
        /\ L5.u8_at RSEGS M' 2147468987 0
        /\ L5.u8_at RSEGS M' 2147468980 0
        /\ L5.u8_at RSEGS M' 2147468976 0
        /\ L5.u8_at RSEGS M' 2147468975 0
        /\ L5.u8_at RSEGS M' 2147468978 0
        /\ L5.u8_at RSEGS M' 2147468977 0
        /\ L5.u8_at RSEGS M' 2147468974 0
        /\ L5.u8_at RSEGS M' 2147468973 0
        /\ L5.u8_at RSEGS M' 2147468979 0
        /\ L5.u8_at RSEGS M' 2147468972 0
        /\ L5.u8_at RSEGS M' 2147468968 0
        /\ L5.u8_at RSEGS M' 2147468967 0
        /\ L5.u8_at RSEGS M' 2147468970 0
        /\ L5.u8_at RSEGS M' 2147468969 0
        /\ L5.u8_at RSEGS M' 2147468966 0
        /\ L5.u8_at RSEGS M' 2147468965 0
        /\ L5.u8_at RSEGS M' 2147468971 0
        /\ L5.u8_at RSEGS M' 2147468964 0
        /\ L5.u32_at RSEGS M' 2147468956 0
        /\ L5.u32_at RSEGS M' 2147468952 0
        /\ L5.u32_at RSEGS M' 2147468960 0
        /\ L5.u32_at RSEGS M' 2147468944 0
        /\ L5.u32_at RSEGS M' 2147468940 0
        /\ L5.u32_at RSEGS M' 2147468948 0
        /\ L5.u32_at RSEGS M' 2147468936 0
        /\ L5.u32_at RSEGS M' 2147468928 0
        /\ L5.u32_at RSEGS M' 2147468924 0
        /\ L5.u32_at RSEGS M' 2147468932 0
        /\ L5.u32_at RSEGS M' 2147468916 0
        /\ L5.u32_at RSEGS M' 2147468912 0
        /\ L5.u32_at RSEGS M' 2147468920 0
        /\ L5.u8_at RSEGS M' 2147468910 0
        /\ L5.u8_at RSEGS M' 2147468909 0
        /\ L5.u8_at RSEGS M' 2147468911 0
        /\ L5.u8_at RSEGS M' 2147468908 0
        /\ L5.u8_at RSEGS M' 2147468904 0
        /\ L5.u8_at RSEGS M' 2147468903 0
        /\ L5.u8_at RSEGS M' 2147468906 0
        /\ L5.u8_at RSEGS M' 2147468905 0
        /\ L5.u8_at RSEGS M' 2147468902 0
        /\ L5.u8_at RSEGS M' 2147468901 0
        /\ L5.u8_at RSEGS M' 2147468907 0
        /\ L5.u8_at RSEGS M' 2147468900 0
        /\ L5.u8_at RSEGS M' 2147468898 0
        /\ L5.u8_at RSEGS M' 2147468897 0
        /\ L5.u8_at RSEGS M' 2147468899 0
        /\ L5.u8_at RSEGS M' 2147468896 0
        /\ L5.u32_at RSEGS M' 2147468876 0
        /\ L5.u32_at RSEGS M' 2147468872 0
        /\ L5.u32_at RSEGS M' 2147468880 0
        /\ L5.u8_at RSEGS M' 2147468870 0
        /\ L5.u8_at RSEGS M' 2147468869 0
        /\ L5.u8_at RSEGS M' 2147468871 0
        /\ L5.u8_at RSEGS M' 2147468868 0
        /\ L5.u8_at RSEGS M' 2147468858 0
        /\ L5.u8_at RSEGS M' 2147468857 0
        /\ L5.u8_at RSEGS M' 2147468859 0
        /\ L5.u8_at RSEGS M' 2147468856 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (bv_unsigned (getr R (reg 22)))
        /\ L5.u8_at RSEGS M' 1295824 1
        /\ L5.u8_at RSEGS M' 6896976 1
        /\ L5.u64_at RSEGS M' 6896992 0
        /\ L5.u32_at RSEGS M' 6896984 32
        /\ L5.u32_at RSEGS M' 6897520 (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) 1147060).
Proof.
  intros sp_rng v40_rng v44_rng ra_val sp_val tp_val sp_win sp_al.
  remember (BG.E_R R (fun j => Z_to_bv 64 (V j)) (fun _ => [])) as Ein eqn:Ein_is.
  assert (in_lo : forall j, (j < 32)%nat -> ev Ein j = getr R (reg j)).
  { intros j j_lt. subst Ein. exact (BG.E_R_reg _ _ _ j j_lt). }
  assert (in_hi : forall j, (32 <= j)%nat -> ev Ein j = Z_to_bv 64 (V j)).
  { intros j j_ge. subst Ein. exact (BG.E_R_rest _ _ _ j j_ge). }
  assert (in_sp : bv_unsigned (ev Ein 2) = V 2%nat).
  { rewrite in_lo, sp_val by lia. exact (BG.unsigned_lit _ sp_rng). }
  assert (in_v40 : bv_unsigned (ev Ein 40) = V 40%nat).
  { rewrite in_hi by lia. exact (BG.unsigned_lit _ v40_rng). }
  assert (in_v44 : bv_unsigned (ev Ein 44) = V 44%nat).
  { rewrite in_hi by lia. exact (BG.unsigned_lit _ v44_rng). }
  assert (regs_in : regs_ok Ein PdpX4B_pre.regs0 R).
  { subst Ein. apply BG.regs_ok_slots; [reflexivity |].
    unfold PdpX4B_pre.regs0. cbn [BG.slots_ok].
    repeat refine (conj _ _); first [left; reflexivity | exact I | exact ra_val | exact tp_val | reflexivity]. }
  (* The entry knowledge kn0.  Its first two entries (the stack window and its alignment) come from hypotheses
     already in hand; every later entry is the next premise of the goal, taken in list order. *)
  pose proof (L5K.kentry_KRange RSEGS Ein M (EVar 2) _ _ _ in_sp sp_win) as ok_win.
  pose proof (L5K.kentry_KAlign RSEGS Ein M (EVar 2) 16 _ in_sp eq_refl sp_al) as ok_al.
  generalize (fun later => (@ListDef.Forall_cons _ _ _ _ ok_win (@ListDef.Forall_cons _ _ _ _ ok_al later)
                            : Forall (kentry_ok RSEGS Ein M) PdpX4B_pre.kn0)).
  let val x := lazymatch x with
               | ELit ?c => exact (@eq_refl Z c)
               | EVar 2 => exact in_sp
               | EVar 40 => exact in_v40
               | EVar 44 => exact in_v44
               end in
  repeat lazymatch goal with
  | |- (Forall _ (?cell :: _) -> _) -> _ -> _ =>
      let built := fresh "built" in let given := fresh "given" in let ok := fresh "ok" in
      intros built given;
      assert (ok : kentry_ok RSEGS Ein M cell) by
        lazymatch cell with
        | KWord (SA ?b ?off) 8 ?e => eapply (L5K.kentry_KWord8 RSEGS Ein M b off e); [val b | val e | lia | lia | exact given]
        | KWord (SA ?b ?off) 4 ?e => eapply (L5K.kentry_KWord4 RSEGS Ein M b off e); [val b | val e | lia | lia | exact given]
        | KWord (SA ?b ?off) 1 ?e => eapply (L5K.kentry_KWord1 RSEGS Ein M b off e); [val b | val e | lia | lia | lia | exact given]
        | KWr (SA ?b ?off) ?n => eapply (L5K.kentry_KWr RSEGS Ein M b off n); [val b | val n | lia | lia | lia | exact given]
        | KUnk (SA ?b ?off) ?n => eapply (L5K.kentry_KUnk RSEGS Ein M b off n); [val b | val n | lia | lia | lia | exact given]
        | KRange ?e _ _ => eapply (L5K.kentry_KRange RSEGS Ein M e); [val e | exact given]
        | KImg _ _ => apply L5K.kentry_KImg; [lia | lia | exact given]
        end;
      generalize (fun later => built (@ListDef.Forall_cons _ _ cell _ ok later)); clear built given ok
  end.
  intro built. pose proof (built (@ListDef.Forall_nil _ _)) as kn_ok. clear built.
  destruct (PdpX4B_pre.seg_sound_ax fx Ein R M regs_in kn_ok (@ListDef.Forall_nil _ _))
    as (fx1 & Eout & R1 & M1 & pick & ps & at_pick & agree & run & outs & _ & _ & frame & cells & grows).
  assert (no_more : PdpX4B_pre.SXALL = []) by (vm_compute; reflexivity).
  unfold PdpX4B_pre.PSS in at_pick. rewrite no_more in at_pick. cbn [app map] in at_pick.
  apply L5K.nth_error_single in at_pick. subst ps.
  (* What the exit environment says about the entry values. *)
  assert (same : forall j, (j < 56)%nat -> ev Eout j = ev Ein j).
  { intros j j_lt. symmetry. apply (proj1 agree). exact j_lt. }
  assert (out_sp : ev Eout 2 = Z_to_bv 64 (V 2%nat)) by (rewrite same, in_lo, sp_val by lia; reflexivity).
  assert (out_sp_u : bv_unsigned (ev Eout 2) = V 2%nat) by (rewrite same by lia; exact in_sp).
  assert (out_v40 : bv_unsigned (ev Eout 40) = V 40%nat) by (rewrite same by lia; exact in_v40).
  assert (out_v44 : bv_unsigned (ev Eout 44) = V 44%nat) by (rewrite same by lia; exact in_v44).
  exists fx1, R1, M1.
  (* Memory outside the footprint F0, first for every word address. *)
  lazymatch goal with |- _ /\ ?keepw /\ _ => assert (by_word : keepw) end.
  { intro a. pose proof (frame a) as keep. unfold PdpX4B_pre.F0 in keep. revert keep.
    repeat lazymatch goal with
    | |- (SGP.outside _ ((?b, ?off, ELit ?n) :: ?more) _ -> _) -> _ -> _ =>
        let keep := fresh "keep" in let away := fresh "away" in
        intros keep away;
        lazymatch b with
        | ELit ?z => generalize (fun far => keep (L5K.outside_cons_e Eout b off (ELit n) more a z n eq_refl eq_refl away far))
        | EVar 2 => generalize (fun far => keep (L5K.outside_cons_e Eout b off (ELit n) more a _ n out_sp_u eq_refl away far))
        end;
        clear keep away
    end.
    intro keep. exact (keep (L5K.outside_nil_e Eout a)). }
  split; [exact grows |]. split; [exact by_word |]. split.
  { intros i i_rng. generalize (by_word (Z_to_bv 64 i)). rewrite (BG.unsigned_lit i i_rng). exact (fun keep => keep). }
  split; [exact run |].
  split.
  { exact (BG.kept_regs Ein Eout R R1 PdpX4B_pre.regs0 PdpX4B_pre.regs_out0 56 KS_dpX4B_pre KS_dpX4B_pre_ok
             regs_in agree outs). }
  (* Registers the segment writes. *)
  repeat lazymatch goal with
  | |- getr R1 (Z_to_bv 5 (Z.of_nat ?r)) = _ /\ _ =>
      split; [ rewrite (BG.out_reg PdpX4B_pre.regs_out0 Eout R1 r outs) by lia;
               cbn [nth PdpX4B_pre.regs_out0 edenot];
               first [ reflexivity | rewrite out_sp; exact (BG.alu_add_lit _ _) ] | ]
  end.
  (* The exit cells cells0, one conjunct each, in list order. *)
  change (SR.ps_cells PdpX4B_pre.ps0) with PdpX4B_pre.cells0 in cells. unfold PdpX4B_pre.cells0 in cells.
  revert cells.
  let val x := lazymatch x with
               | ELit ?c => exact (@eq_refl Z c)
               | EVar 2 => exact out_sp_u
               | EVar 40 => exact out_v40
               | EVar 44 => exact out_v44
               | EVar ?j => cbn [edenot]; rewrite same, in_lo by lia; reflexivity
               end in
  let read here := lazymatch type of here with
    | kentry_ok _ _ _ (KWord (SA ?b ?off) 8 ?e) => eapply (u64_of_KWord8a Eout M1 b off e); [exact here | val b | val e | lia]
    | kentry_ok _ _ _ (KWord (SA ?b ?off) 4 ?e) => eapply (u32_of_KWord4a Eout M1 b off e); [exact here | val b | val e | lia]
    | kentry_ok _ _ _ (KWord (SA ?b ?off) 1 ?e) => eapply (u8_of_KWord1a Eout M1 b off e); [exact here | val b | val e | lia | lia]
    end in
  repeat lazymatch goal with
  | |- (forall K, In K (?cell :: ?more) -> _) -> _ =>
      let seen := fresh "seen" in let here := fresh "here" in
      intro seen; pose proof (seen cell (or_introl eq_refl)) as here;
      lazymatch goal with
      | |- _ /\ _ => split; [read here | generalize (fun K (later : In K more) => seen K (or_intror later)); clear seen here]
      | |- _ => read here
      end
  end.
Qed.
(* [comment removed for export] *)

End AS0DRVP_dpX4B_pre.
