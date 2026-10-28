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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_arvA_b LibSegBa_arvR0_b LibSegBa_arvB_b LibSegBa_arvF_b LibSegBa_arvS_b LibSegBa_arvC_b LibSegBa_arvE_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMARSVP.
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
Module ParvA := LibSegBa_arvA_b.
Definition KS_arvA_0 : list nat := Eval vm_compute in (BG.kept_list 60 ParvA.regs0 ParvA.regs_out0).
Lemma KS_arvA_0_ok : BG.kept_ok 60 ParvA.regs0 ParvA.regs_out0 KS_arvA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arvA_1 : list nat := Eval vm_compute in (BG.kept_list 60 ParvA.regs0 ParvA.regs_out1).
Lemma KS_arvA_1_ok : BG.kept_ok 60 ParvA.regs0 ParvA.regs_out1 KS_arvA_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arvA_2 : list nat := Eval vm_compute in (BG.kept_list 60 ParvA.regs0 ParvA.regs_out2).
Lemma KS_arvA_2_ok : BG.kept_ok 60 ParvA.regs0 ParvA.regs_out2 KS_arvA_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arvA_3 : list nat := Eval vm_compute in (BG.kept_list 60 ParvA.regs0 ParvA.regs_out3).
Lemma KS_arvA_3_ok : BG.kept_ok 60 ParvA.regs0 ParvA.regs_out3 KS_arvA_3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 38%nat) -> getr R (reg 12) = Z_to_bv 64 (V 37%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) -> 0 <= (V 33%nat) <= 16384 -> 0 <= (V 38%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb3bfc M) (st fx' R' 0xb3db4 M')
        /\ (forall x, In x KS_arvA_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ (((V 38%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0xb3bfc M) (st fx' R' 0xb3d24 M')
        /\ (forall x, In x KS_arvA_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ (V 38%nat) <= (V 33%nat)
        /\ 1 <= (((V 33%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 38%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0xb3bfc M) (st fx' R' 0xb3cd8 M')
        /\ (forall x, In x KS_arvA_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ (V 33%nat) < (V 38%nat)
        /\ 1 <= (((V 33%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 38%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0xb3bfc M) (st fx' R' 0xb3c5c M')
        /\ (forall x, In x KS_arvA_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ (((V 33%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 38%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K13l; move K13l before pvzI8; pose proof (proj2 pvzI8) as K13r; move K13r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E ParvA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvA.kn0).
  { unfold know_ok, ParvA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear - HV33l HV33r K13l K13r) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParvA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvA.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold ParvA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc ParvA.ps0) with 0xb3db4 in Hms. change (SR.ps_regs ParvA.ps0) with (map (fun i => (i, nth i ParvA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParvA.ps0) with ParvA.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvA.regs0 ParvA.regs_out0 60 KS_arvA_0 KS_arvA_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParvA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc ParvA.ps1) with 0xb3d24 in Hms. change (SR.ps_regs ParvA.ps1) with (map (fun i => (i, nth i ParvA.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParvA.ps1) with ParvA.cells1 in Hcells. unfold ParvA.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvA.regs0 ParvA.regs_out1 60 KS_arvA_1 KS_arvA_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParvA.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth ParvA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth ParvA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth ParvA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth ParvA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth ParvA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth ParvA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth ParvA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth ParvA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc ParvA.ps2) with 0xb3cd8 in Hms. change (SR.ps_regs ParvA.ps2) with (map (fun i => (i, nth i ParvA.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParvA.ps2) with ParvA.cells2 in Hcells. unfold ParvA.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvA.regs0 ParvA.regs_out2 60 KS_arvA_2 KS_arvA_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParvA.regs_out2 E' R' 2 Hregs) by (clear; lia). cbn [nth ParvA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out2 E' R' 8 Hregs) by (clear; lia). cbn [nth ParvA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out2 E' R' 9 Hregs) by (clear; lia). cbn [nth ParvA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth ParvA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth ParvA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth ParvA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth ParvA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out2 E' R' 22 Hregs) by (clear; lia). cbn [nth ParvA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. 
    change (SR.ps_pc ParvA.ps3) with 0xb3c5c in Hms. change (SR.ps_regs ParvA.ps3) with (map (fun i => (i, nth i ParvA.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParvA.ps3) with ParvA.cells3 in Hcells. unfold ParvA.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvA.regs0 ParvA.regs_out3 60 KS_arvA_3 KS_arvA_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParvA.regs_out3 E' R' 2 Hregs) by (clear; lia). cbn [nth ParvA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out3 E' R' 8 Hregs) by (clear; lia). cbn [nth ParvA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out3 E' R' 9 Hregs) by (clear; lia). cbn [nth ParvA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out3 E' R' 18 Hregs) by (clear; lia). cbn [nth ParvA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out3 E' R' 19 Hregs) by (clear; lia). cbn [nth ParvA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out3 E' R' 21 Hregs) by (clear; lia). cbn [nth ParvA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvA.regs_out3 E' R' 22 Hregs) by (clear; lia). cbn [nth ParvA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParvR0 := LibSegBa_arvR0_b.
Definition KS_arvR0_0 : list nat := Eval vm_compute in (BG.kept_list 60 ParvR0.regs0 ParvR0.regs_out0).
Lemma KS_arvR0_0_ok : BG.kept_ok 60 ParvR0.regs0 ParvR0.regs_out0 KS_arvR0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arvR0_1 : list nat := Eval vm_compute in (BG.kept_list 60 ParvR0.regs0 ParvR0.regs_out1).
Lemma KS_arvR0_1_ok : BG.kept_ok 60 ParvR0.regs0 ParvR0.regs_out1 KS_arvR0_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvR0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 38%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> 1 <= (V 38%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb3c5c M) (st fx' R' 0xb3cd8 M')
        /\ (forall x, In x KS_arvR0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ 16384 < (V 38%nat))
      \/ (msteps RSEGS (st fx R 0xb3c5c M) (st fx' R' 0xb29f8 M')
        /\ (forall x, In x KS_arvR0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 736408
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 16384
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + 264)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 36%nat) + 264) / 8) + 2147450880)
        /\ (V 38%nat) <= 16384)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G21 G22 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 K14 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K15l; move K15l before pvzI8; pose proof (proj2 pvzI8) as K15r; move K15r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E ParvR0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvR0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvR0.kn0).
  { unfold know_ok, ParvR0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParvR0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvR0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvR0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc ParvR0.ps0) with 0xb3cd8 in Hms. change (SR.ps_regs ParvR0.ps0) with (map (fun i => (i, nth i ParvR0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParvR0.ps0) with ParvR0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvR0.regs0 ParvR0.regs_out0 60 KS_arvR0_0 KS_arvR0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParvR0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvR0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvR0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParvR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc ParvR0.ps1) with 0xb29f8 in Hms. change (SR.ps_regs ParvR0.ps1) with (map (fun i => (i, nth i ParvR0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParvR0.ps1) with ParvR0.cells1 in Hcells. unfold ParvR0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvR0.regs0 ParvR0.regs_out1 60 KS_arvR0_1 KS_arvR0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParvR0.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvR0.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvR0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvR0.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth ParvR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvR0.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth ParvR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvR0.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth ParvR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParvB := LibSegBa_arvB_b.
Definition KS_arvB_0 : list nat := Eval vm_compute in (BG.kept_list 60 ParvB.regs0 ParvB.regs_out0).
Lemma KS_arvB_0_ok : BG.kept_ok 60 ParvB.regs0 ParvB.regs_out0 KS_arvB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arvB_1 : list nat := Eval vm_compute in (BG.kept_list 60 ParvB.regs0 ParvB.regs_out1).
Lemma KS_arvB_1_ok : BG.kept_ok 60 ParvB.regs0 ParvB.regs_out1 KS_arvB_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 38%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 43%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 20) = Z_to_bv 64 ((V 36%nat) + 264) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 264) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> 0 <= (V 43%nat) <= 16384 -> 1 <= (V 38%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 280) <= bv_unsigned a < ((V 36%nat) + 280) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 280) <= i < ((V 36%nat) + 280) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb3c98 M) (st fx' R' 0xb3cd8 M')
        /\ (forall x, In x KS_arvB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)
        /\ (V 43%nat) < (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) (V 43%nat))
      \/ (msteps RSEGS (st fx R 0xb3c98 M) (st fx' R' 0xb3d24 M')
        /\ (forall x, In x KS_arvB_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)
        /\ (V 38%nat) <= (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) (V 43%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E ParvB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvB.kn0).
  { unfold know_ok, ParvB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParvB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvB.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 280) <= bv_unsigned a < (vz_36 + 280) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold ParvB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc ParvB.ps0) with 0xb3cd8 in Hms. change (SR.ps_regs ParvB.ps0) with (map (fun i => (i, nth i ParvB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParvB.ps0) with ParvB.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvB.regs0 ParvB.regs_out0 60 KS_arvB_0 KS_arvB_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParvB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K13l K13r) | clear; lia]. 
  - right.
    change (SR.ps_pc ParvB.ps1) with 0xb3d24 in Hms. change (SR.ps_regs ParvB.ps1) with (map (fun i => (i, nth i ParvB.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParvB.ps1) with ParvB.cells1 in Hcells. unfold ParvB.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvB.regs0 ParvB.regs_out1 60 KS_arvB_1 KS_arvB_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParvB.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvB.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParvB.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth ParvB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K13l K13r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParvF := LibSegBa_arvF_b.
Definition KS_arvF : list nat := Eval vm_compute in (BG.kept_list 60 ParvF.regs0 ParvF.regs_out0).
Lemma KS_arvF_ok : BG.kept_ok 60 ParvF.regs0 ParvF.regs_out0 KS_arvF = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 38%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> 1 <= (V 35%nat) <= 140737488355328 -> L5.defined M ((V 36%nat) + 256) 8 ->
  1 <= (V 33%nat) <= 16384 -> 1 <= (V 38%nat) <= 16384 -> 0 <= ((V 33%nat) - (V 38%nat)) <= 16383 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 8) -> ~ (((V 36%nat) + 280) <= bv_unsigned a < ((V 36%nat) + 280) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 8) -> ~ (((V 36%nat) + 280) <= i < ((V 36%nat) + 280) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3d24 M) (st fx' R' 0xb3db4 M')
        /\ (forall x, In x KS_arvF -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 35%nat) + (V 38%nat))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) ((V 33%nat) - (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) ((V 35%nat) + (V 38%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G12 G18 G19 G21 G22 K0 K1 K2 pvzI16 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 pvzI17 K16 K17 K18 K19 K20 K21 pvzI18 K23 pvzI19 pvzI20 pvzI21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV50l; move HV50l before pvzI13; pose proof (proj2 pvzI13) as HV50r; move HV50r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV51l; move HV51l before pvzI14; pose proof (proj2 pvzI14) as HV51r; move HV51r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV52l; move HV52l before pvzI15; pose proof (proj2 pvzI15) as HV52r; move HV52r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K3l; move K3l before pvzI16; pose proof (proj2 pvzI16) as K3r; move K3r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K15l; move K15l before pvzI17; pose proof (proj2 pvzI17) as K15r; move K15r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K22l; move K22l before pvzI18; pose proof (proj2 pvzI18) as K22r; move K22r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K24l; move K24l before pvzI19; pose proof (proj2 pvzI19) as K24r; move K24r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K25l; move K25l before pvzI20; pose proof (proj2 pvzI20) as K25r; move K25r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K26l; move K26l before pvzI21; pose proof (proj2 pvzI21) as K26r; move K26r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E ParvF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvF.kn0).
  { unfold know_ok, ParvF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K20; lia | clear - HV2l HV2r K3l K3r K20; lia | clear - HV2l HV2r K3l K3r K20; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r K20; lia | clear - HV2l HV2r K3l K3r K20; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r K20; lia | clear - HV2l HV2r K3l K3r K20; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r K20; lia | clear - HV2l HV2r K3l K3r K20; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K3l K3r K20; lia | clear - HV2l HV2r K3l K3r K20; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K20; lia | clear - HV2l HV2r K3l K3r K20; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K20; lia | clear - HV2l HV2r K3l K3r K20; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K20; lia | clear - HV2l HV2r K3l K3r K20; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K20; lia | clear - HV2l HV2r K3l K3r K20; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K20; lia | clear - HV2l HV2r K3l K3r K20; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K15l K15r K17 K20; lia | clear - HV36l HV36r K15l K15r K17 K20; lia | clear - HV36l HV36r K15l K15r K17 K20; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K15l K15r K17 K20; lia | clear - HV36l HV36r K15l K15r K17 K20; lia | clear - HV36l HV36r K15l K15r K17 K20; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r) | clear - HV36l HV36r K15l K15r K17 K20; lia | clear - HV36l HV36r K15l K15r K17 K20; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K15l K15r K17 K20; lia | clear - HV36l HV36r K15l K15r K17 K20; lia | clear - HV36l HV36r K15l K15r K17 K20; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K24l K24r K26l K26r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r K26l K26r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K24l K24r K26l K26r HV38l HV38r K25l K25r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParvF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvF.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 8) -> ~ ((vz_36 + 280) <= bv_unsigned a < (vz_36 + 280) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold ParvF.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K15l K15r K17 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K15l K15r K17 K20 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K15l K15r K17 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K15l K15r K17 K20 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvF.ps0) with 0xb3db4 in Hms. change (SR.ps_regs ParvF.ps0) with (map (fun i => (i, nth i ParvF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvF.ps0) with ParvF.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvF.regs0 ParvF.regs_out0 60 KS_arvF KS_arvF_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvF.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth ParvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K15l K15r K17 K20) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K24l K24r K26l K26r HV38l HV38r K25l K25r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K15l K15r K17 K20) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K22l K22r HV38l HV38r K25l K25r K26l K26r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParvS := LibSegBa_arvS_b.
Definition KS_arvS : list nat := Eval vm_compute in (BG.kept_list 60 ParvS.regs0 ParvS.regs_out0).
Lemma KS_arvS_ok : BG.kept_ok 60 ParvS.regs0 ParvS.regs_out0 KS_arvS = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 38%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  1 <= (V 38%nat) <= 18446744073709551615 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u64_at RSEGS M (V 37%nat) (V 39%nat) -> L5.u64_at RSEGS M ((V 37%nat) + 8) ((V 39%nat) + (V 40%nat)) -> 0 <= (V 39%nat) <= 140737488355328 -> 0 <= (V 40%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) + 8) <= bv_unsigned a < ((V 37%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) + 8) <= i < ((V 37%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3cd8 M) (st fx' R' 0xabb00 M')
        /\ (forall x, In x KS_arvS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 736480
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = getr R (reg 11)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 20) = getr R (reg 20)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 37%nat) + 8) ((V 39%nat) + (V 40%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G21 G22 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 pvzI9 pvzI10 K14 K15 K16 K17 K18 K19 K20 K21 pvzI11 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K13l; move K13l before pvzI10; pose proof (proj2 pvzI10) as K13r; move K13r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K22l; move K22l before pvzI11; pose proof (proj2 pvzI11) as K22r; move K22r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E ParvS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvS.kn0).
  { unfold know_ok, ParvS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K18; lia | clear - HV2l HV2r K3l K3r K11 K18; lia | clear - HV2l HV2r K3l K3r K11 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K19) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K19) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K19) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K19) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K19; lia | clear - HV36l HV36r K6l K6r K8 K11 K19; lia | clear - HV36l HV36r K6l K6r K8 K11 K19; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K19) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K19; lia | clear - HV36l HV36r K6l K6r K8 K11 K19; lia | clear - HV36l HV36r K6l K6r K8 K11 K19; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K19) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K13l K13r K15 K18 K19) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K13l K13r K15 K18 K19) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K13l K13r K15 K18 K19) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K13l K13r K15 K18 K19) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K13l K13r K15 K18 K19; lia | clear - HV37l HV37r K13l K13r K15 K18 K19; lia | clear - HV37l HV37r K13l K13r K15 K18 K19; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K13l K13r K15 K18 K19) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K13l K13r K15 K18 K19; lia | clear - HV37l HV37r K13l K13r K15 K18 K19; lia | clear - HV37l HV37r K13l K13r K15 K18 K19; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K13l K13r K15 K18 K19) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K13l K13r K15 K18 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K13l K13r K15 K18 K19) | evalEk ZA ltac:(clear - HV39l HV39r K22l K22r) | clear - HV37l HV37r K13l K13r K15 K18 K19; lia | clear - HV37l HV37r K13l K13r K15 K18 K19; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K13l K13r K15 K18 K19) | evalEk ZA ltac:(clear - HV39l HV39r K22l K22r HV40l HV40r K23l K23r) | clear - HV37l HV37r K13l K13r K15 K18 K19; lia | clear - HV37l HV37r K13l K13r K15 K18 K19; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParvS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_37 + 8) <= bv_unsigned a < (vz_37 + 8) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold ParvS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K13l K13r K15 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K13l K13r K15 K18 K19 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvS.ps0) with 0xabb00 in Hms. change (SR.ps_regs ParvS.ps0) with (map (fun i => (i, nth i ParvS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvS.ps0) with ParvS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvS.regs0 ParvS.regs_out0 60 KS_arvS KS_arvS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvS.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg ParvS.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParvS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvS.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth ParvS.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg ParvS.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth ParvS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K13l K13r K15 K18 K19) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K22l K22r HV40l HV40r K23l K23r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParvC := LibSegBa_arvC_b.
Definition KS_arvC : list nat := Eval vm_compute in (BG.kept_list 60 ParvC.regs0 ParvC.regs_out0).
Lemma KS_arvC_ok : BG.kept_ok 60 ParvC.regs0 ParvC.regs_out0 KS_arvC = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 38%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> 140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3ce0 M) (st fx' R' 0xb5500 M')
        /\ (forall x, In x KS_arvC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 736496
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 G19 G21 G22 K0 pvzI5 K2 pvzI6 K4 pvzI7 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K1l; move K1l before pvzI5; pose proof (proj2 pvzI5) as K1r; move K1r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K5l; move K5l before pvzI7; pose proof (proj2 pvzI7) as K5r; move K5r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E ParvC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvC.kn0).
  { unfold know_ok, ParvC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r) | clear; lia | exact K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K5l K5r) | clear; lia | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParvC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvC.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvC.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvC.ps0) with 0xb5500 in Hms. change (SR.ps_regs ParvC.ps0) with (map (fun i => (i, nth i ParvC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvC.ps0) with ParvC.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvC.regs0 ParvC.regs_out0 60 KS_arvC KS_arvC_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvC.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvC.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvC.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvC.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParvC.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParvE := LibSegBa_arvE_b.
Definition KS_arvE : list nat := Eval vm_compute in (BG.kept_list 60 ParvE.regs0 ParvE.regs_out0).
Lemma KS_arvE_ok : BG.kept_ok 60 ParvE.regs0 ParvE.regs_out0 KS_arvE = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 38%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) -> 1 <= (V 38%nat) <= 18446744073709551615 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 80)) ->
  ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) -> L5.u64_at RSEGS M (V 37%nat) (V 39%nat) -> L5.u64_at RSEGS M ((V 37%nat) + 8) ((V 39%nat) + (V 40%nat)) -> 0 <= (V 39%nat) <= 140737488355328 ->
  0 <= (V 40%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3cf0 M) (st fx' R' 0xb3db4 M')
        /\ (forall x, In x KS_arvE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G18 G19 G21 G22 K0 K1 K2 pvzI16 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 pvzI17 K16 K17 K18 K19 K20 pvzI18 pvzI19 K23 K24 K25 K26 K27 K28 K29 K30 pvzI20 pvzI21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV50l; move HV50l before pvzI13; pose proof (proj2 pvzI13) as HV50r; move HV50r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV51l; move HV51l before pvzI14; pose proof (proj2 pvzI14) as HV51r; move HV51r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV52l; move HV52l before pvzI15; pose proof (proj2 pvzI15) as HV52r; move HV52r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K3l; move K3l before pvzI16; pose proof (proj2 pvzI16) as K3r; move K3r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K15l; move K15l before pvzI17; pose proof (proj2 pvzI17) as K15r; move K15r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K21l; move K21l before pvzI18; pose proof (proj2 pvzI18) as K21r; move K21r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K22l; move K22l before pvzI19; pose proof (proj2 pvzI19) as K22r; move K22r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K31l; move K31l before pvzI20; pose proof (proj2 pvzI20) as K31r; move K31r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K32l; move K32l before pvzI21; pose proof (proj2 pvzI21) as K32r; move K32r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E ParvE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvE.kn0).
  { unfold know_ok, ParvE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K20 K27; lia | clear - HV2l HV2r K3l K3r K20 K27; lia | clear - HV2l HV2r K3l K3r K20 K27; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r K20 K27; lia | clear - HV2l HV2r K3l K3r K20 K27; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r K20 K27; lia | clear - HV2l HV2r K3l K3r K20 K27; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r K20 K27; lia | clear - HV2l HV2r K3l K3r K20 K27; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K3l K3r K20 K27; lia | clear - HV2l HV2r K3l K3r K20 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K20 K27; lia | clear - HV2l HV2r K3l K3r K20 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K20 K27; lia | clear - HV2l HV2r K3l K3r K20 K27; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K20 K27; lia | clear - HV2l HV2r K3l K3r K20 K27; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K20 K27; lia | clear - HV2l HV2r K3l K3r K20 K27; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K20 K27; lia | clear - HV2l HV2r K3l K3r K20 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20 K28) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20 K28) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20 K28) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20 K28) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K15l K15r K17 K20 K28; lia | clear - HV36l HV36r K15l K15r K17 K20 K28; lia | clear - HV36l HV36r K15l K15r K17 K20 K28; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20 K28) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K15l K15r K17 K20 K28; lia | clear - HV36l HV36r K15l K15r K17 K20 K28; lia | clear - HV36l HV36r K15l K15r K17 K20 K28; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20 K28) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K22l K22r K24 K27 K28) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K22l K22r K24 K27 K28) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K22l K22r K24 K27 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K22l K22r K24 K27 K28) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K22l K22r K24 K27 K28; lia | clear - HV37l HV37r K22l K22r K24 K27 K28; lia | clear - HV37l HV37r K22l K22r K24 K27 K28; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K22l K22r K24 K27 K28) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K22l K22r K24 K27 K28; lia | clear - HV37l HV37r K22l K22r K24 K27 K28; lia | clear - HV37l HV37r K22l K22r K24 K27 K28; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K20 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K22l K22r K24 K27 K28) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K17 K20 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K22l K22r K24 K27 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K22l K22r K24 K27 K28) | evalEk ZA ltac:(clear - HV39l HV39r K31l K31r) | clear - HV37l HV37r K22l K22r K24 K27 K28; lia | clear - HV37l HV37r K22l K22r K24 K27 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K22l K22r K24 K27 K28) | evalEk ZA ltac:(clear - HV39l HV39r K31l K31r HV40l HV40r K32l K32r) | clear - HV37l HV37r K22l K22r K24 K27 K28; lia | clear - HV37l HV37r K22l K22r K24 K27 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K31l K31r) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParvE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvE.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvE.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvE.ps0) with 0xb3db4 in Hms. change (SR.ps_regs ParvE.ps0) with (map (fun i => (i, nth i ParvE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvE.ps0) with ParvE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvE.regs0 ParvE.regs_out0 60 KS_arvE KS_arvE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth ParvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth ParvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth ParvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth ParvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvE.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvE.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth ParvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvE.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth ParvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvE.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth ParvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvE.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth ParvE.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

End PMARSVP.
