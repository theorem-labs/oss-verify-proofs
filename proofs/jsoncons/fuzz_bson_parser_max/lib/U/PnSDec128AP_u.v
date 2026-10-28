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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_dkA_u LibSegBs_dkB_u LibSegBs_dkZ0_u LibSegBs_dkZ1_u LibSegBs_dkSC_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSDAP.
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
Module PdkA := LibSegBs_dkA_u.
Definition KS_dkA_0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkA.regs0 PdkA.regs_out0).
Lemma KS_dkA_0_ok : BG.kept_ok 80 PdkA.regs0 PdkA.regs_out0 KS_dkA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkA_1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkA.regs0 PdkA.regs_out1).
Lemma KS_dkA_1_ok : BG.kept_ok 80 PdkA.regs0 PdkA.regs_out1 KS_dkA_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 240) 240 -> 4096 <= (V 33%nat) <= 140737488355286 ->
  L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 240) + 240 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 240)) -> 4096 <= (V 35%nat) <= 140737488355312 -> aligned (V 35%nat) 8 ->
  L5.u64_at RSEGS M (V 35%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 37%nat) -> (((V 2%nat) - 240) + 240 <= (V 35%nat) \/ (V 35%nat) + 16 <= ((V 2%nat) - 240)) -> ((V 33%nat) + 42 <= (V 35%nat) \/ (V 35%nat) + 16 <= (V 33%nat)) ->
  L5.img_clear M 65536 754672 -> L5.u8_at RSEGS M 820640 1 -> L5.u8_at RSEGS M 820672 1 -> L5.u8_at RSEGS M 820616 16 ->
  L5.defined M 820617 8 -> L5.u8_at RSEGS M 820648 6 -> L5.defined M 820649 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38a78 M) (st fx' R' 0x38afc M')
        /\ (forall x, In x KS_dkA_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 42)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EVar 37) (ELit 0))) <= 0
        /\ L5KA.zeros_at M' ((V 2%nat) - 216) 144
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x38a78 M) (st fx' R' 0x38afc M')
        /\ (forall x, In x KS_dkA_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 42)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 10) = Z_to_bv 64 45
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ L5.u8_at RSEGS M' (V 33%nat) 45
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EVar 37) (ELit 0))) <= 1
        /\ L5KA.zeros_at M' ((V 2%nat) - 216) 144
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
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 pvzI6 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PdkA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkA.kn0).
  { unfold know_ok, PdkA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K10) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K10) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K10; lia | clear - HV2l HV2r K0l K0r K5 K10; lia | clear - HV2l HV2r K0l K0r K5 K10; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11; lia | clear - HV33l HV33r K3l K3r K5 K11; lia | clear - HV33l HV33r K3l K3r K5 K11; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K10 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K10 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K10 K11) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV35l HV35r K6l K6r K10 K11; lia | clear - HV35l HV35r K6l K6r K10 K11; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K10 K11) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV35l HV35r K6l K6r K10 K11; lia | clear - HV35l HV35r K6l K6r K10 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K10 K11) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K10 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K18]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 240) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PdkA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K10 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PdkA.ps0) with 0x38afc in Hms. change (SR.ps_regs PdkA.ps0) with (map (fun i => (i, nth i PdkA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkA.ps0) with PdkA.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkA.regs0 PdkA.regs_out0 80 KS_dkA_0 KS_dkA_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PdkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PdkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PdkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PdkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  - right.
    change (SR.ps_pc PdkA.ps1) with 0x38afc in Hms. change (SR.ps_regs PdkA.ps1) with (map (fun i => (i, nth i PdkA.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkA.ps1) with PdkA.cells1 in Hcells. unfold PdkA.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkA.regs0 PdkA.regs_out1 80 KS_dkA_1 KS_dkA_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkA.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PdkA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkA.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PdkA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkA.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PdkA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkA.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkA.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PdkA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkA.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkB := LibSegBs_dkB_u.
Definition KS_dkB_0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkB.regs0 PdkB.regs_out0).
Lemma KS_dkB_0_ok : BG.kept_ok 80 PdkB.regs0 PdkB.regs_out0 KS_dkB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkB_1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkB.regs0 PdkB.regs_out1).
Lemma KS_dkB_1_ok : BG.kept_ok 80 PdkB.regs0 PdkB.regs_out1 KS_dkB_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkB_2 : list nat := Eval vm_compute in (BG.kept_list 80 PdkB.regs0 PdkB.regs_out2).
Lemma KS_dkB_2_ok : BG.kept_ok 80 PdkB.regs0 PdkB.regs_out2 KS_dkB_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkB_3 : list nat := Eval vm_compute in (BG.kept_list 80 PdkB.regs0 PdkB.regs_out3).
Lemma KS_dkB_3_ok : BG.kept_ok 80 PdkB.regs0 PdkB.regs_out3 KS_dkB_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkB_4 : list nat := Eval vm_compute in (BG.kept_list 80 PdkB.regs0 PdkB.regs_out4).
Lemma KS_dkB_4_ok : BG.kept_ok 80 PdkB.regs0 PdkB.regs_out4 KS_dkB_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkB_5 : list nat := Eval vm_compute in (BG.kept_list 80 PdkB.regs0 PdkB.regs_out5).
Lemma KS_dkB_5_ok : BG.kept_ok 80 PdkB.regs0 PdkB.regs_out5 KS_dkB_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkB_6 : list nat := Eval vm_compute in (BG.kept_list 80 PdkB.regs0 PdkB.regs_out6).
Lemma KS_dkB_6_ok : BG.kept_ok 80 PdkB.regs0 PdkB.regs_out6 KS_dkB_6 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma dkB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 240) 240 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 240) + 240 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 240)) -> L5.img_clear M 65536 754672 ->
  4096 <= (V 35%nat) <= 140737488355312 -> aligned (V 35%nat) 8 -> L5.u64_at RSEGS M (V 35%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 37%nat) ->
  (((V 2%nat) - 240) + 240 <= (V 35%nat) \/ (V 35%nat) + 16 <= ((V 2%nat) - 240)) -> ((V 33%nat) + 42 <= (V 35%nat) \/ (V 35%nat) + 16 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38afc M) (st fx' R' 0x39080 M')
        /\ (forall x, In x KS_dkB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1610612736
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land ((V 37%nat) / 4294967296) 1610612736)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 37%nat) / 4294967296)
        /\ (((Z.land ((V 37%nat) / 4294967296) 1610612736) - 1610612736) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38afc M) (st fx' R' 0x38cb0 M')
        /\ (forall x, In x KS_dkB_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 37%nat) / 4294967296) / 131072)
        /\ getr R' (reg 11) = Z_to_bv 64 16383
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAluw Instr.ALU_ADD (EVar 36) (ELit 0))
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551608
        /\ bv_unsigned (getr R' (reg 14)) = (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 36%nat) / 4294967296)
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 2%nat) - 232)
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 2%nat) - 232)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 36) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ ((((V 36%nat) / 4294967296) - 0) mod 2 ^ 64) < 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 32768) (EVar 37)) (ELit 61))) (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL (EVar 37) (ELit 32)) (ELit 16383))) (EVar 37)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 220) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 224) ((V 36%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 228) (V 37%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 232) ((((16384 * (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952)) mod 2 ^ 64) + (Z.land ((V 37%nat) / 4294967296) 16383)) mod 2 ^ 64)
        /\ 1 <= (((Z.land ((V 37%nat) / 4294967296) 1610612736) - 1610612736) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38afc M) (st fx' R' 0x38bc4 M')
        /\ (forall x, In x KS_dkB_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 18446744073709551607
        /\ getr R' (reg 6) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 7) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 37%nat) / 4294967296) / 131072)
        /\ getr R' (reg 11) = Z_to_bv 64 16383
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 240)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 76)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551580
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 2%nat) - 216)
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 19) = Z_to_bv 64 3
        /\ getr R' (reg 28) = Z_to_bv 64 1000000000
        /\ getr R' (reg 29) = Z_to_bv 64 14757395259826634752
        /\ getr R' (reg 30) = Z_to_bv 64 10
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 36) (ELit 0)) (ELit 0)) (ELit 1))) <= 0
        /\ ((((V 36%nat) / 4294967296) - 0) mod 2 ^ 64) < 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 32768) (EVar 37)) (ELit 61))) (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL (EVar 37) (ELit 32)) (ELit 16383))) (EVar 37)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 220) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 224) ((V 36%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 228) (V 37%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 232) ((((16384 * (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952)) mod 2 ^ 64) + (Z.land ((V 37%nat) / 4294967296) 16383)) mod 2 ^ 64)
        /\ 1 <= (((Z.land ((V 37%nat) / 4294967296) 1610612736) - 1610612736) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38afc M) (st fx' R' 0x38cb0 M')
        /\ (forall x, In x KS_dkB_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 37%nat) / 4294967296) / 131072)
        /\ getr R' (reg 11) = Z_to_bv 64 16383
        /\ getr R' (reg 12) = Z_to_bv 64 7
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551608
        /\ bv_unsigned (getr R' (reg 14)) = (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 36%nat) / 4294967296)
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 2%nat) - 232)
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 2%nat) - 232)
        /\ 7 < (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952)
        /\ 1 <= ((((V 36%nat) / 4294967296) - 0) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 32768) (EVar 37)) (ELit 61))) (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL (EVar 37) (ELit 32)) (ELit 16383))) (EVar 37)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 220) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 224) ((V 36%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 228) (V 37%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 232) ((((16384 * (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952)) mod 2 ^ 64) + (Z.land ((V 37%nat) / 4294967296) 16383)) mod 2 ^ 64)
        /\ 1 <= (((Z.land ((V 37%nat) / 4294967296) 1610612736) - 1610612736) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38afc M) (st fx' R' 0x38bc4 M')
        /\ (forall x, In x KS_dkB_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 18446744073709551607
        /\ getr R' (reg 6) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 7) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 37%nat) / 4294967296) / 131072)
        /\ getr R' (reg 11) = Z_to_bv 64 16383
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 240)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 76)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551580
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 2%nat) - 216)
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 19) = Z_to_bv 64 3
        /\ getr R' (reg 28) = Z_to_bv 64 1000000000
        /\ getr R' (reg 29) = Z_to_bv 64 14757395259826634752
        /\ getr R' (reg 30) = Z_to_bv 64 10
        /\ (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952) <= 7
        /\ 1 <= ((((V 36%nat) / 4294967296) - 0) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 32768) (EVar 37)) (ELit 61))) (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL (EVar 37) (ELit 32)) (ELit 16383))) (EVar 37)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 220) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 224) ((V 36%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 228) (V 37%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 232) ((((16384 * (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952)) mod 2 ^ 64) + (Z.land ((V 37%nat) / 4294967296) 16383)) mod 2 ^ 64)
        /\ 1 <= (((Z.land ((V 37%nat) / 4294967296) 1610612736) - 1610612736) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38afc M) (st fx' R' 0x38cb0 M')
        /\ (forall x, In x KS_dkB_5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 37%nat) / 4294967296) / 131072)
        /\ getr R' (reg 11) = Z_to_bv 64 16383
        /\ getr R' (reg 12) = Z_to_bv 64 7
        /\ getr R' (reg 13) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 32768) (EVar 37)) (ELit 61))) (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL (EVar 37) (ELit 32)) (ELit 16383))) (EVar 37)) (ELit 0))
        /\ bv_unsigned (getr R' (reg 14)) = (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 36%nat) / 4294967296)
        /\ bv_unsigned (getr R' (reg 16)) = ((((16384 * (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952)) mod 2 ^ 64) + (Z.land ((V 37%nat) / 4294967296) 16383)) mod 2 ^ 64)
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 2%nat) - 232)
        /\ 7 < (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 32768) (EVar 37)) (ELit 61))) (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL (EVar 37) (ELit 32)) (ELit 16383))) (EVar 37)) (ELit 0)) (ELit 0)) (ELit 1))) <= 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 220) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 224) ((V 36%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 228) (V 37%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 232) ((((16384 * (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952)) mod 2 ^ 64) + (Z.land ((V 37%nat) / 4294967296) 16383)) mod 2 ^ 64)
        /\ 1 <= (((Z.land ((V 37%nat) / 4294967296) 1610612736) - 1610612736) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38afc M) (st fx' R' 0x38bc4 M')
        /\ (forall x, In x KS_dkB_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 18446744073709551607
        /\ getr R' (reg 6) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 7) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 37%nat) / 4294967296) / 131072)
        /\ getr R' (reg 11) = Z_to_bv 64 16383
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 240)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 76)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551580
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 2%nat) - 216)
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 19) = Z_to_bv 64 3
        /\ getr R' (reg 28) = Z_to_bv 64 1000000000
        /\ getr R' (reg 29) = Z_to_bv 64 14757395259826634752
        /\ getr R' (reg 30) = Z_to_bv 64 10
        /\ (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952) <= 7
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 32768) (EVar 37)) (ELit 61))) (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL (EVar 37) (ELit 32)) (ELit 16383))) (EVar 37)) (ELit 0)) (ELit 0)) (ELit 1))) <= 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 220) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 224) ((V 36%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 228) (V 37%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 232) ((((16384 * (((32768 * (V 37%nat)) mod 2 ^ 64) / 2305843009213693952)) mod 2 ^ 64) + (Z.land ((V 37%nat) / 4294967296) 16383)) mod 2 ^ 64)
        /\ 1 <= (((Z.land ((V 37%nat) / 4294967296) 1610612736) - 1610612736) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G18 G19 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI17 K13 K14 K15 pvzI18 K17 K18 K19 K20 K21 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K12l; move K12l before pvzI17; pose proof (proj2 pvzI17) as K12r; move K12r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K16l; move K16l before pvzI18; pose proof (proj2 pvzI18) as K16r; move K16r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K22l; move K22l before pvzI19; pose proof (proj2 pvzI19) as K22r; move K22r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkB.kn0).
  { unfold know_ok, PdkB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K20; lia | clear - HV2l HV2r K0l K0r K14 K20; lia | clear - HV2l HV2r K0l K0r K14 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14 K20; lia | clear - HV2l HV2r K0l K0r K14 K20; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14 K20; lia | clear - HV2l HV2r K0l K0r K14 K20; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14 K20; lia | clear - HV2l HV2r K0l K0r K14 K20; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14 K20; lia | clear - HV2l HV2r K0l K0r K14 K20; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14 K20; lia | clear - HV2l HV2r K0l K0r K14 K20; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14 K20; lia | clear - HV2l HV2r K0l K0r K14 K20; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14 K20; lia | clear - HV2l HV2r K0l K0r K14 K20; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14 K20; lia | clear - HV2l HV2r K0l K0r K14 K20; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14 K20; lia | clear - HV2l HV2r K0l K0r K14 K20; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14 K21) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14 K21; lia | clear - HV33l HV33r K12l K12r K14 K21; lia | clear - HV33l HV33r K12l K12r K14 K21; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14 K21) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K16l K16r K20 K21) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K16l K16r K20 K21) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K16l K16r K20 K21) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV35l HV35r K16l K16r K20 K21; lia | clear - HV35l HV35r K16l K16r K20 K21; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K16l K16r K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV35l HV35r K16l K16r K20 K21; lia | clear - HV35l HV35r K16l K16r K20 K21; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K16l K16r K20 K21) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K16l K16r K20 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkB.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 232) <= bv_unsigned a < (vz_2 - 232) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K20 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PdkB.ps0) with 0x39080 in Hms. change (SR.ps_regs PdkB.ps0) with (map (fun i => (i, nth i PdkB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkB.ps0) with PdkB.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkB.regs0 PdkB.regs_out0 80 KS_dkB_0 KS_dkB_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkB.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PdkB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PdkB.ps1) with 0x38cb0 in Hms. change (SR.ps_regs PdkB.ps1) with (map (fun i => (i, nth i PdkB.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkB.ps1) with PdkB.cells1 in Hcells. unfold PdkB.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkB.regs0 PdkB.regs_out1 80 KS_dkB_1 KS_dkB_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkB.regs_out1 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkB.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PdkB.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkB.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PdkB.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out1 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc PdkB.ps2) with 0x38bc4 in Hms. change (SR.ps_regs PdkB.ps2) with (map (fun i => (i, nth i PdkB.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkB.ps2) with PdkB.cells2 in Hcells. unfold PdkB.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkB.regs0 PdkB.regs_out2 80 KS_dkB_2 KS_dkB_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 6 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 7 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 28 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 29 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out2 E' R' 30 Hregs) by (clear; lia). cbn [nth PdkB.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc PdkB.ps3) with 0x38cb0 in Hms. change (SR.ps_regs PdkB.ps3) with (map (fun i => (i, nth i PdkB.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkB.ps3) with PdkB.cells3 in Hcells. unfold PdkB.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkB.regs0 PdkB.regs_out3 80 KS_dkB_3 KS_dkB_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkB.regs_out3 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkB.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkB.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out3 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkB.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out3 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkB.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out3 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkB.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out3 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkB.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PdkB.regs_out3 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkB.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out3 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkB.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out3 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkB.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc PdkB.ps4) with 0x38bc4 in Hms. change (SR.ps_regs PdkB.ps4) with (map (fun i => (i, nth i PdkB.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkB.ps4) with PdkB.cells4 in Hcells. unfold PdkB.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkB.regs0 PdkB.regs_out4 80 KS_dkB_4 KS_dkB_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 6 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 7 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 28 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 29 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out4 E' R' 30 Hregs) by (clear; lia). cbn [nth PdkB.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc PdkB.ps5) with 0x38cb0 in Hms. change (SR.ps_regs PdkB.ps5) with (map (fun i => (i, nth i PdkB.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkB.ps5) with PdkB.cells5 in Hcells. unfold PdkB.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkB.regs0 PdkB.regs_out5 80 KS_dkB_5 KS_dkB_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkB.regs_out5 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkB.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out5 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkB.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out5 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkB.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out5 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkB.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out5 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkB.regs_out5]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PdkB.regs_out5 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkB.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PdkB.regs_out5 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkB.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out5 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkB.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PdkB.regs_out5 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkB.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. 
    change (SR.ps_pc PdkB.ps6) with 0x38bc4 in Hms. change (SR.ps_regs PdkB.ps6) with (map (fun i => (i, nth i PdkB.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkB.ps6) with PdkB.cells6 in Hcells. unfold PdkB.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkB.regs0 PdkB.regs_out6 80 KS_dkB_6 KS_dkB_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 6 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 7 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 28 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 29 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkB.regs_out6 E' R' 30 Hregs) by (clear; lia). cbn [nth PdkB.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K20) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkZ0 := LibSegBs_dkZ0_u.
Definition KS_dkZ0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkZ0.regs0 PdkZ0.regs_out0).
Lemma KS_dkZ0_ok : BG.kept_ok 80 PdkZ0.regs0 PdkZ0.regs_out0 KS_dkZ0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkZ0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 240) 240 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 240) + 240 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 240)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 38%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 216) <= bv_unsigned a < ((V 2%nat) - 216) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 216) <= i < ((V 2%nat) - 216) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38cb0 M) (st fx' R' 0x38cec M')
        /\ (forall x, In x KS_dkZ0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 216)
        /\ getr R' (reg 14) = Z_to_bv 64 48
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 216) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G18 pvzI13 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI14 K13 K14 K15 pvzI15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV60l; move HV60l before pvzI4; pose proof (proj2 pvzI4) as HV60r; move HV60r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV61l; move HV61l before pvzI5; pose proof (proj2 pvzI5) as HV61r; move HV61r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV62l; move HV62l before pvzI6; pose proof (proj2 pvzI6) as HV62r; move HV62r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV63l; move HV63l before pvzI7; pose proof (proj2 pvzI7) as HV63r; move HV63r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV64l; move HV64l before pvzI8; pose proof (proj2 pvzI8) as HV64r; move HV64r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV65l; move HV65l before pvzI9; pose proof (proj2 pvzI9) as HV65r; move HV65r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV66l; move HV66l before pvzI10; pose proof (proj2 pvzI10) as HV66r; move HV66r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV67l; move HV67l before pvzI11; pose proof (proj2 pvzI11) as HV67r; move HV67r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV68l; move HV68l before pvzI12; pose proof (proj2 pvzI12) as HV68r; move HV68r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K0l; move K0l before pvzI13; pose proof (proj2 pvzI13) as K0r; move K0r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K12l; move K12l before pvzI14; pose proof (proj2 pvzI14) as K12r; move K12r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K16l; move K16l before pvzI15; pose proof (proj2 pvzI15) as K16r; move K16r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkZ0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkZ0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkZ0.kn0).
  { unfold know_ok, PdkZ0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkZ0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkZ0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 216) <= bv_unsigned a < (vz_2 - 216) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkZ0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkZ0.ps0) with 0x38cec in Hms. change (SR.ps_regs PdkZ0.ps0) with (map (fun i => (i, nth i PdkZ0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkZ0.ps0) with PdkZ0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkZ0.regs0 PdkZ0.regs_out0 80 KS_dkZ0 KS_dkZ0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkZ0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkZ0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkZ0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkZ0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkZ0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkZ0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkZ1 := LibSegBs_dkZ1_u.
Definition KS_dkZ1_0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkZ1.regs0 PdkZ1.regs_out0).
Lemma KS_dkZ1_0_ok : BG.kept_ok 80 PdkZ1.regs0 PdkZ1.regs_out0 KS_dkZ1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkZ1_1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkZ1.regs0 PdkZ1.regs_out1).
Lemma KS_dkZ1_1_ok : BG.kept_ok 80 PdkZ1.regs0 PdkZ1.regs_out1 KS_dkZ1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkZ1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 15) = Z_to_bv 64 18446744073709551580 -> getr R (reg 16) = Z_to_bv 64 ((V 2%nat) - 216) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 240) 240 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 240) + 240 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 240)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 38%nat) <= 1 -> 0 <= (V 51%nat) <= 9 -> L5.u32_at RSEGS M ((V 2%nat) - 216) (V 51%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38c94 M) (st fx' R' 0x38cd0 M')
        /\ (forall x, In x KS_dkZ1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 36
        /\ getr R' (reg 14) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551611
        /\ (((V 51%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38c94 M) (st fx' R' 0x38cec M')
        /\ (forall x, In x KS_dkZ1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 36
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 216)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 51%nat) + 48)
        /\ 1 <= (((V 51%nat) - 0) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G15 G16 G18 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI15 K13 K14 K15 pvzI16 pvzI17 K18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV51l; move HV51l before pvzI4; pose proof (proj2 pvzI4) as HV51r; move HV51r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkZ1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkZ1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkZ1.kn0).
  { unfold know_ok, PdkZ1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV51l HV51r K17l K17r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K18]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkZ1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkZ1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PdkZ1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PdkZ1.ps0) with 0x38cd0 in Hms. change (SR.ps_regs PdkZ1.ps0) with (map (fun i => (i, nth i PdkZ1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkZ1.ps0) with PdkZ1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkZ1.regs0 PdkZ1.regs_out0 80 KS_dkZ1_0 KS_dkZ1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkZ1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkZ1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkZ1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PdkZ1.ps1) with 0x38cec in Hms. change (SR.ps_regs PdkZ1.ps1) with (map (fun i => (i, nth i PdkZ1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkZ1.ps1) with PdkZ1.cells1 in Hcells. unfold PdkZ1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkZ1.regs0 PdkZ1.regs_out1 80 KS_dkZ1_1 KS_dkZ1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkZ1.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkZ1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkZ1.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkZ1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkZ1.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkZ1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkSC := LibSegBs_dkSC_u.
Definition KS_dkSC_0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkSC.regs0 PdkSC.regs_out0).
Lemma KS_dkSC_0_ok : BG.kept_ok 80 PdkSC.regs0 PdkSC.regs_out0 KS_dkSC_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkSC_1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkSC.regs0 PdkSC.regs_out1).
Lemma KS_dkSC_1_ok : BG.kept_ok 80 PdkSC.regs0 PdkSC.regs_out1 KS_dkSC_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkSC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 12) = Z_to_bv 64 (36 - (V 52%nat)) -> getr R (reg 15) = Z_to_bv 64 18446744073709551611 -> getr R (reg 16) = Z_to_bv 64 (((V 2%nat) - 216) + (4 * (V 52%nat))) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 240) 240 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 240) + 240 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 240)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 38%nat) <= 1 -> 0 <= (V 52%nat) <= 34 -> L5.u32_at RSEGS M ((((V 2%nat) - 216) + (4 * (V 52%nat))) + 4) (V 53%nat) -> 0 <= (V 53%nat) <= 9 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38cd0 M) (st fx' R' 0x38cd0 M')
        /\ (forall x, In x KS_dkSC_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 (((-1) * (V 52%nat)) + 35)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 2%nat) + (4 * (V 52%nat))) - 212)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 2%nat) + (4 * (V 52%nat))) - 212)
        /\ (((V 53%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38cd0 M) (st fx' R' 0x38cec M')
        /\ (forall x, In x KS_dkSC_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 (((-1) * (V 52%nat)) + 35)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 2%nat) + (4 * (V 52%nat))) - 212)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 53%nat) + 48)
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 2%nat) + (4 * (V 52%nat))) - 212)
        /\ 1 <= (((V 53%nat) - 0) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 G2 G8 G9 G12 G15 G16 G18 pvzI15 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI16 K13 K14 K15 pvzI17 pvzI18 K18 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV52l; move HV52l before pvzI4; pose proof (proj2 pvzI4) as HV52r; move HV52r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV53l; move HV53l before pvzI5; pose proof (proj2 pvzI5) as HV53r; move HV53r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV60l; move HV60l before pvzI6; pose proof (proj2 pvzI6) as HV60r; move HV60r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV61l; move HV61l before pvzI7; pose proof (proj2 pvzI7) as HV61r; move HV61r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV62l; move HV62l before pvzI8; pose proof (proj2 pvzI8) as HV62r; move HV62r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV63l; move HV63l before pvzI9; pose proof (proj2 pvzI9) as HV63r; move HV63r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV64l; move HV64l before pvzI10; pose proof (proj2 pvzI10) as HV64r; move HV64r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV65l; move HV65l before pvzI11; pose proof (proj2 pvzI11) as HV65r; move HV65r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV66l; move HV66l before pvzI12; pose proof (proj2 pvzI12) as HV66r; move HV66r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV67l; move HV67l before pvzI13; pose proof (proj2 pvzI13) as HV67r; move HV67r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV68l; move HV68l before pvzI14; pose proof (proj2 pvzI14) as HV68r; move HV68r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K0l; move K0l before pvzI15; pose proof (proj2 pvzI15) as K0r; move K0r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K12l; move K12l before pvzI16; pose proof (proj2 pvzI16) as K12r; move K12r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K16l; move K16l before pvzI17; pose proof (proj2 pvzI17) as K16r; move K16r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K17l; move K17l before pvzI18; pose proof (proj2 pvzI18) as K17r; move K17r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K19l; move K19l before pvzI19; pose proof (proj2 pvzI19) as K19r; move K19r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 52%nat => vz_52 | 53%nat => vz_53 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkSC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkSC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkSC.kn0).
  { unfold know_ok, PdkSC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 HV52l HV52r K17l K17r) | evalEk ZA ltac:(clear - HV53l HV53r K19l K19r) | clear - HV2l HV2r K0l K0r K14 HV52l HV52r K17l K17r; lia | clear - HV2l HV2r K0l K0r K14 HV52l HV52r K17l K17r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkSC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkSC.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PdkSC.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PdkSC.ps0) with 0x38cd0 in Hms. change (SR.ps_regs PdkSC.ps0) with (map (fun i => (i, nth i PdkSC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkSC.ps0) with PdkSC.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkSC.regs0 PdkSC.regs_out0 80 KS_dkSC_0 KS_dkSC_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkSC.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkSC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkSC.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkSC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkSC.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkSC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkSC.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkSC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PdkSC.ps1) with 0x38cec in Hms. change (SR.ps_regs PdkSC.ps1) with (map (fun i => (i, nth i PdkSC.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkSC.ps1) with PdkSC.cells1 in Hcells. unfold PdkSC.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkSC.regs0 PdkSC.regs_out1 80 KS_dkSC_1 KS_dkSC_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkSC.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkSC.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkSC.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkSC.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkSC.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkSC.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkSC.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkSC.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

End PNSDAP.
