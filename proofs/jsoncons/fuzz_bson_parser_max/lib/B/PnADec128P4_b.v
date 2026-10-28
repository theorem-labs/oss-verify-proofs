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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_adkRD0_b LibSegBa_adkRD1_b LibSegBa_adkRD2_b LibSegBa_adkRD3_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADP4.
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
Module PadkRD0 := LibSegBa_adkRD0_b.
Definition KS_adkRD0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRD0.regs0 PadkRD0.regs_out0).
Lemma KS_adkRD0_ok : BG.kept_ok 80 PadkRD0.regs0 PadkRD0.regs_out0 KS_adkRD0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkRD0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 50%nat) + 64) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 28) -> getr R (reg 19) = Z_to_bv 64 3 -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 21) = Z_to_bv 64 (V 48%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 0 -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 ((V 50%nat) + 64) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 256)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> 1 <= (V 48%nat) <= 999999999 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 32) <= bv_unsigned a < ((V 50%nat) + 32) + 36) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 32) <= i < ((V 50%nat) + 32) + 36) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb420c M) (st fx' R' 0xb4230 M')
        /\ (forall x, In x KS_adkRD0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = getr R (reg 1)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 50%nat) + 28)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EVar 48)) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))
        /\ getr R' (reg 21) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 32) (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 36) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 40) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 44) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 48) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 52) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 56) (((((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 60) (((((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 64) (((V 48%nat) + ((18446744073709551606 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI4 K1 K2 pvzI5 K4 K5 K6 K7 K8 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV48l; move HV48l before pvzI2; pose proof (proj2 pvzI2) as HV48r; move HV48r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV50l; move HV50l before pvzI3; pose proof (proj2 pvzI3) as HV50r; move HV50r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K9l; move K9l before pvzI6; pose proof (proj2 pvzI6) as K9r; move K9r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkRD0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkRD0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkRD0.kn0).
  { unfold know_ok, PadkRD0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K6 K7 K8; lia | clear - HV50l HV50r K3l K3r K6 K7 K8; lia | clear - HV50l HV50r K3l K3r K6 K7 K8; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkRD0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkRD0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 32) <= bv_unsigned a < (vz_50 + 32) + 36) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkRD0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K6 K7 K8 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkRD0.ps0) with 0xb4230 in Hms. change (SR.ps_regs PadkRD0.ps0) with (map (fun i => (i, nth i PadkRD0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkRD0.ps0) with PadkRD0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRD0.regs0 PadkRD0.regs_out0 80 KS_adkRD0 KS_adkRD0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkRD0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkRD0.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadkRD0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRD0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkRD0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkRD0.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
  split. { rewrite (BG.out_reg PadkRD0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkRD0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadkRD0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD0.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PadkRD0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD0.regs_out0 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkRD0.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkRD1 := LibSegBa_adkRD1_b.
Definition KS_adkRD1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRD1.regs0 PadkRD1.regs_out0).
Lemma KS_adkRD1_ok : BG.kept_ok 80 PadkRD1.regs0 PadkRD1.regs_out0 KS_adkRD1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkRD1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 50%nat) + 100) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 64) -> getr R (reg 19) = Z_to_bv 64 2 -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 21) = Z_to_bv 64 (V 48%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 ((V 50%nat) + 100) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 256)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> 1 <= (V 48%nat) <= 999999999 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 68) <= bv_unsigned a < ((V 50%nat) + 68) + 36) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 68) <= i < ((V 50%nat) + 68) + 36) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb420c M) (st fx' R' 0xb4230 M')
        /\ (forall x, In x KS_adkRD1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = getr R (reg 1)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 50%nat) + 64)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EVar 48)) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))
        /\ getr R' (reg 21) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 1
        /\ getr R' (reg 25) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 68) (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 72) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 76) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 80) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 84) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 88) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 92) (((((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 96) (((((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 100) (((V 48%nat) + ((18446744073709551606 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI4 K1 K2 pvzI5 K4 K5 K6 K7 K8 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV48l; move HV48l before pvzI2; pose proof (proj2 pvzI2) as HV48r; move HV48r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV50l; move HV50l before pvzI3; pose proof (proj2 pvzI3) as HV50r; move HV50r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K9l; move K9l before pvzI6; pose proof (proj2 pvzI6) as K9r; move K9r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkRD1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkRD1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkRD1.kn0).
  { unfold know_ok, PadkRD1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K6 K7 K8; lia | clear - HV50l HV50r K3l K3r K6 K7 K8; lia | clear - HV50l HV50r K3l K3r K6 K7 K8; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkRD1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkRD1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 68) <= bv_unsigned a < (vz_50 + 68) + 36) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkRD1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K6 K7 K8 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkRD1.ps0) with 0xb4230 in Hms. change (SR.ps_regs PadkRD1.ps0) with (map (fun i => (i, nth i PadkRD1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkRD1.ps0) with PadkRD1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRD1.regs0 PadkRD1.regs_out0 80 KS_adkRD1 KS_adkRD1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkRD1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkRD1.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadkRD1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkRD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkRD1.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
  split. { rewrite (BG.out_reg PadkRD1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkRD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadkRD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PadkRD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD1.regs_out0 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkRD1.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkRD2 := LibSegBa_adkRD2_b.
Definition KS_adkRD2 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRD2.regs0 PadkRD2.regs_out0).
Lemma KS_adkRD2_ok : BG.kept_ok 80 PadkRD2.regs0 PadkRD2.regs_out0 KS_adkRD2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkRD2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 50%nat) + 136) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 100) -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 21) = Z_to_bv 64 (V 48%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 2 -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 ((V 50%nat) + 136) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 256)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> 1 <= (V 48%nat) <= 999999999 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 104) <= bv_unsigned a < ((V 50%nat) + 104) + 36) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 104) <= i < ((V 50%nat) + 104) + 36) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb420c M) (st fx' R' 0xb4230 M')
        /\ (forall x, In x KS_adkRD2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = getr R (reg 1)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 50%nat) + 100)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EVar 48)) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))
        /\ getr R' (reg 21) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 2
        /\ getr R' (reg 25) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 104) (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 108) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 112) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 116) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 120) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 124) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 128) (((((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 132) (((((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 136) (((V 48%nat) + ((18446744073709551606 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI4 K1 K2 pvzI5 K4 K5 K6 K7 K8 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV48l; move HV48l before pvzI2; pose proof (proj2 pvzI2) as HV48r; move HV48r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV50l; move HV50l before pvzI3; pose proof (proj2 pvzI3) as HV50r; move HV50r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K9l; move K9l before pvzI6; pose proof (proj2 pvzI6) as K9r; move K9r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkRD2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkRD2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkRD2.kn0).
  { unfold know_ok, PadkRD2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K6 K7 K8; lia | clear - HV50l HV50r K3l K3r K6 K7 K8; lia | clear - HV50l HV50r K3l K3r K6 K7 K8; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkRD2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkRD2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 104) <= bv_unsigned a < (vz_50 + 104) + 36) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkRD2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K6 K7 K8 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkRD2.ps0) with 0xb4230 in Hms. change (SR.ps_regs PadkRD2.ps0) with (map (fun i => (i, nth i PadkRD2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkRD2.ps0) with PadkRD2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRD2.regs0 PadkRD2.regs_out0 80 KS_adkRD2 KS_adkRD2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkRD2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkRD2.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadkRD2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkRD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkRD2.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
  split. { rewrite (BG.out_reg PadkRD2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkRD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadkRD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD2.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PadkRD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD2.regs_out0 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkRD2.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkRD3 := LibSegBa_adkRD3_b.
Definition KS_adkRD3 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRD3.regs0 PadkRD3.regs_out0).
Lemma KS_adkRD3_ok : BG.kept_ok 80 PadkRD3.regs0 PadkRD3.regs_out0 KS_adkRD3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkRD3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 50%nat) + 172) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 136) -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 21) = Z_to_bv 64 (V 48%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 ((V 50%nat) + 172) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 256)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> 1 <= (V 48%nat) <= 999999999 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 140) <= bv_unsigned a < ((V 50%nat) + 140) + 36) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 140) <= i < ((V 50%nat) + 140) + 36) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb420c M) (st fx' R' 0xb4230 M')
        /\ (forall x, In x KS_adkRD3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = getr R (reg 1)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 50%nat) + 136)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EMd Instr.M_MUL (ELit 4294967296) (EVar 48)) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))) (ELit 14757395259826634752)) (ELit 35))
        /\ getr R' (reg 21) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 3
        /\ getr R' (reg 25) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 140) (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 144) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 148) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 152) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 156) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 160) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 164) (((((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 168) (((((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 172) (((V 48%nat) + ((18446744073709551606 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI4 K1 K2 pvzI5 K4 K5 K6 K7 K8 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV48l; move HV48l before pvzI2; pose proof (proj2 pvzI2) as HV48r; move HV48r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV50l; move HV50l before pvzI3; pose proof (proj2 pvzI3) as HV50r; move HV50r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K9l; move K9l before pvzI6; pose proof (proj2 pvzI6) as K9r; move K9r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkRD3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkRD3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkRD3.kn0).
  { unfold know_ok, PadkRD3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K6 K7 K8; lia | clear - HV50l HV50r K3l K3r K6 K7 K8; lia | clear - HV50l HV50r K3l K3r K6 K7 K8; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkRD3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkRD3.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 140) <= bv_unsigned a < (vz_50 + 140) + 36) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkRD3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K6 K7 K8 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkRD3.ps0) with 0xb4230 in Hms. change (SR.ps_regs PadkRD3.ps0) with (map (fun i => (i, nth i PadkRD3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkRD3.ps0) with PadkRD3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRD3.regs0 PadkRD3.regs_out0 80 KS_adkRD3 KS_adkRD3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkRD3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkRD3.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadkRD3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkRD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkRD3.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
  split. { rewrite (BG.out_reg PadkRD3.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkRD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD3.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadkRD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD3.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PadkRD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRD3.regs_out0 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkRD3.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia].
Qed.
(* [comment removed for export] *)

End PNADP4.
