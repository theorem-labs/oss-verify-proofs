(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BigLinkZA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Eb0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_027S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBEPP3.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).

Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5KA.zpolyA_sound E Vz e z A Pz)).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, BL.MM. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.

Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u64_of_KWord8; eauto. Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u32_of_KWord4; eauto. Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof. intros K Ha Hv Hr ->. eapply L5K.u8_of_KWord1; eauto. Qed.

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

Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].

Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.

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

Local Ltac den_tac := first [reflexivity | lia | idtac].

Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.

Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
  repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].

Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].

Module PbpkG1 := BndP_Eb_027S9.LibSegEb_bpkG1.
Definition KS_bpkG1 : list nat := Eval vm_compute in (BG.kept_list 60 PbpkG1.regs0 PbpkG1.regs_out0).
Lemma KS_bpkG1_ok : BG.kept_ok 60 PbpkG1.regs0 PbpkG1.regs_out0 KS_bpkG1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpkG1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 2 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 64) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + 24) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + 24) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 8 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 3 -> 4096 <= (V 40%nat) <= 140737488355280 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 24) 24 -> L5KA.zeros_at M ((((V 40%nat) + 24) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 24) \/ ((V 40%nat) + 24) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + 24) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 24) \/ ((V 40%nat) + 24) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 56 <= ((V 40%nat) + 24) \/ ((V 40%nat) + 24) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 24) \/ ((V 40%nat) + 24) + 24 <= (V 34%nat)) -> (65536 + 6864896 <= ((V 40%nat) + 24) \/ ((V 40%nat) + 24) + 24 <= 65536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737868 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 24) + 0) <= bv_unsigned a < (((V 40%nat) + 24) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 24) + 0) <= i < (((V 40%nat) + 24) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0be4 M) (st fx' R' 0x792dc M')
        /\ (forall x, In x KS_bpkG1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 40%nat) + 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 G19 G20 G21 pvzI14 K1 K2 K3 K4 K5 K6 pvzI15 K8 K9 K10 K11 K12 K13 K14 K15 pvzI16 K17 pvzI17 K19 K20 K21 K22 K23 K24 pvzI18 pvzI19 K27 K28 K29 K30 pvzI20 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV21l; move HV21l before pvzI2; pose proof (proj2 pvzI2) as HV21r; move HV21r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K7l; move K7l before pvzI15; pose proof (proj2 pvzI15) as K7r; move K7r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K18l; move K18l before pvzI17; pose proof (proj2 pvzI17) as K18r; move K18r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K31l; move K31l before pvzI20; pose proof (proj2 pvzI20) as K31r; move K31r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 21%nat => Z_to_bv 64 vz_21 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 21%nat => vz_21 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbpkG1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpkG1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpkG1.kn0).
  { unfold know_ok, PbpkG1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K50]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpkG1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpkG1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 208) -> ~ (((vz_40 + 24) + 0) <= bv_unsigned a < ((vz_40 + 24) + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbpkG1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpkG1.ps0) with 0x792dc in Hms. change (SR.ps_regs PbpkG1.ps0) with (map (fun i => (i, nth i PbpkG1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpkG1.ps0) with PbpkG1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpkG1.regs0 PbpkG1.regs_out0 60 KS_bpkG1 KS_bpkG1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K25l K25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia].
Qed.

Module PbpkG2 := BndP_Eb_027S9.LibSegEb_bpkG2.
Definition KS_bpkG2 : list nat := Eval vm_compute in (BG.kept_list 60 PbpkG2.regs0 PbpkG2.regs_out0).
Lemma KS_bpkG2_ok : BG.kept_ok 60 PbpkG2.regs0 PbpkG2.regs_out0 KS_bpkG2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpkG2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 4 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 19) = Z_to_bv 64 2 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 64) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + 48) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + 48) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 8 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 3 -> 4096 <= (V 40%nat) <= 140737488355232 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 48) 24 -> L5KA.zeros_at M ((((V 40%nat) + 48) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 48) \/ ((V 40%nat) + 48) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + 48) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 48) \/ ((V 40%nat) + 48) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 56 <= ((V 40%nat) + 48) \/ ((V 40%nat) + 48) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 48) \/ ((V 40%nat) + 48) + 24 <= (V 34%nat)) -> (65536 + 6864896 <= ((V 40%nat) + 48) \/ ((V 40%nat) + 48) + 24 <= 65536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737868 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 48) + 0) <= bv_unsigned a < (((V 40%nat) + 48) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 48) + 0) <= i < (((V 40%nat) + 48) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0be4 M) (st fx' R' 0x792dc M')
        /\ (forall x, In x KS_bpkG2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 56)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 48) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 40%nat) + 96)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 G19 G20 G21 pvzI14 K1 K2 K3 K4 K5 K6 pvzI15 K8 K9 K10 K11 K12 K13 K14 K15 pvzI16 K17 pvzI17 K19 K20 K21 K22 K23 K24 pvzI18 pvzI19 K27 K28 K29 K30 pvzI20 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV21l; move HV21l before pvzI2; pose proof (proj2 pvzI2) as HV21r; move HV21r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K7l; move K7l before pvzI15; pose proof (proj2 pvzI15) as K7r; move K7r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K18l; move K18l before pvzI17; pose proof (proj2 pvzI17) as K18r; move K18r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K31l; move K31l before pvzI20; pose proof (proj2 pvzI20) as K31r; move K31r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 21%nat => Z_to_bv 64 vz_21 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 21%nat => vz_21 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbpkG2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpkG2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpkG2.kn0).
  { unfold know_ok, PbpkG2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K50]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpkG2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpkG2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 208) -> ~ (((vz_40 + 48) + 0) <= bv_unsigned a < ((vz_40 + 48) + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbpkG2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpkG2.ps0) with 0x792dc in Hms. change (SR.ps_regs PbpkG2.ps0) with (map (fun i => (i, nth i PbpkG2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpkG2.ps0) with PbpkG2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpkG2.regs0 PbpkG2.regs_out0 60 KS_bpkG2 KS_bpkG2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K25l K25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia].
Qed.

Module PbpkG3 := BndP_Eb_027S9.LibSegEb_bpkG3.
Definition KS_bpkG3 : list nat := Eval vm_compute in (BG.kept_list 60 PbpkG3.regs0 PbpkG3.regs_out0).
Lemma KS_bpkG3_ok : BG.kept_ok 60 PbpkG3.regs0 PbpkG3.regs_out0 KS_bpkG3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpkG3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 8 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 19) = Z_to_bv 64 4 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 64) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + 96) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + 96) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 8 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 3 -> 4096 <= (V 40%nat) <= 140737488355136 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 96) 24 -> L5KA.zeros_at M ((((V 40%nat) + 96) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 96) \/ ((V 40%nat) + 96) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + 96) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 96) \/ ((V 40%nat) + 96) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 56 <= ((V 40%nat) + 96) \/ ((V 40%nat) + 96) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 96) \/ ((V 40%nat) + 96) + 24 <= (V 34%nat)) -> (65536 + 6864896 <= ((V 40%nat) + 96) \/ ((V 40%nat) + 96) + 24 <= 65536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737868 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 96) + 0) <= bv_unsigned a < (((V 40%nat) + 96) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 96) + 0) <= i < (((V 40%nat) + 96) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0be4 M) (st fx' R' 0x792dc M')
        /\ (forall x, In x KS_bpkG3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 104)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 96) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 40%nat) + 192)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 96)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + 96)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 G19 G20 G21 pvzI14 K1 K2 K3 K4 K5 K6 pvzI15 K8 K9 K10 K11 K12 K13 K14 K15 pvzI16 K17 pvzI17 K19 K20 K21 K22 K23 K24 pvzI18 pvzI19 K27 K28 K29 K30 pvzI20 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV21l; move HV21l before pvzI2; pose proof (proj2 pvzI2) as HV21r; move HV21r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K7l; move K7l before pvzI15; pose proof (proj2 pvzI15) as K7r; move K7r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K18l; move K18l before pvzI17; pose proof (proj2 pvzI17) as K18r; move K18r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K31l; move K31l before pvzI20; pose proof (proj2 pvzI20) as K31r; move K31r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 21%nat => Z_to_bv 64 vz_21 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 21%nat => vz_21 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbpkG3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpkG3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpkG3.kn0).
  { unfold know_ok, PbpkG3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K50]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpkG3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpkG3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 208) -> ~ (((vz_40 + 96) + 0) <= bv_unsigned a < ((vz_40 + 96) + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbpkG3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpkG3.ps0) with 0x792dc in Hms. change (SR.ps_regs PbpkG3.ps0) with (map (fun i => (i, nth i PbpkG3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpkG3.ps0) with PbpkG3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpkG3.regs0 PbpkG3.regs_out0 60 KS_bpkG3 KS_bpkG3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG3.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpkG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K25l K25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia].
Qed.

Module PbpkG4 := BndP_Eb_027S9.LibSegEb_bpkG4.
Definition KS_bpkG4 : list nat := Eval vm_compute in (BG.kept_list 60 PbpkG4.regs0 PbpkG4.regs_out0).
Lemma KS_bpkG4_ok : BG.kept_ok 60 PbpkG4.regs0 PbpkG4.regs_out0 KS_bpkG4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpkG4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 16 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 19) = Z_to_bv 64 8 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 64) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + 192) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + 192) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 8 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 3 -> 4096 <= (V 40%nat) <= 140737488354944 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 192) 24 -> L5KA.zeros_at M ((((V 40%nat) + 192) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 192) \/ ((V 40%nat) + 192) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + 192) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 192) \/ ((V 40%nat) + 192) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 56 <= ((V 40%nat) + 192) \/ ((V 40%nat) + 192) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 192) \/ ((V 40%nat) + 192) + 24 <= (V 34%nat)) -> (65536 + 6864896 <= ((V 40%nat) + 192) \/ ((V 40%nat) + 192) + 24 <= 65536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737868 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 192) + 0) <= bv_unsigned a < (((V 40%nat) + 192) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 192) + 0) <= i < (((V 40%nat) + 192) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0be4 M) (st fx' R' 0x792dc M')
        /\ (forall x, In x KS_bpkG4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 200)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 192) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 40%nat) + 384)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 192)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + 192)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 G19 G20 G21 pvzI14 K1 K2 K3 K4 K5 K6 pvzI15 K8 K9 K10 K11 K12 K13 K14 K15 pvzI16 K17 pvzI17 K19 K20 K21 K22 K23 K24 pvzI18 pvzI19 K27 K28 K29 K30 pvzI20 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV21l; move HV21l before pvzI2; pose proof (proj2 pvzI2) as HV21r; move HV21r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K7l; move K7l before pvzI15; pose proof (proj2 pvzI15) as K7r; move K7r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K18l; move K18l before pvzI17; pose proof (proj2 pvzI17) as K18r; move K18r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K31l; move K31l before pvzI20; pose proof (proj2 pvzI20) as K31r; move K31r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 21%nat => Z_to_bv 64 vz_21 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 21%nat => vz_21 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbpkG4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpkG4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpkG4.kn0).
  { unfold know_ok, PbpkG4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K50]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpkG4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpkG4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 208) -> ~ (((vz_40 + 192) + 0) <= bv_unsigned a < ((vz_40 + 192) + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbpkG4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpkG4.ps0) with 0x792dc in Hms. change (SR.ps_regs PbpkG4.ps0) with (map (fun i => (i, nth i PbpkG4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpkG4.ps0) with PbpkG4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpkG4.regs0 PbpkG4.regs_out0 60 KS_bpkG4 KS_bpkG4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG4.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpkG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K25l K25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia].
Qed.

Module PbpkG5 := BndP_Eb_027S9.LibSegEb_bpkG5.
Definition KS_bpkG5 : list nat := Eval vm_compute in (BG.kept_list 60 PbpkG5.regs0 PbpkG5.regs_out0).
Lemma KS_bpkG5_ok : BG.kept_ok 60 PbpkG5.regs0 PbpkG5.regs_out0 KS_bpkG5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpkG5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 32 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 19) = Z_to_bv 64 16 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 64) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + 384) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + 384) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 8 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 3 -> 4096 <= (V 40%nat) <= 140737488354560 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 384) 24 -> L5KA.zeros_at M ((((V 40%nat) + 384) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 384) \/ ((V 40%nat) + 384) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + 384) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 384) \/ ((V 40%nat) + 384) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 56 <= ((V 40%nat) + 384) \/ ((V 40%nat) + 384) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 384) \/ ((V 40%nat) + 384) + 24 <= (V 34%nat)) -> (65536 + 6864896 <= ((V 40%nat) + 384) \/ ((V 40%nat) + 384) + 24 <= 65536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737868 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 384) + 0) <= bv_unsigned a < (((V 40%nat) + 384) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 384) + 0) <= i < (((V 40%nat) + 384) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0be4 M) (st fx' R' 0x792dc M')
        /\ (forall x, In x KS_bpkG5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 392)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 384) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 40%nat) + 768)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 384)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + 384)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 G19 G20 G21 pvzI14 K1 K2 K3 K4 K5 K6 pvzI15 K8 K9 K10 K11 K12 K13 K14 K15 pvzI16 K17 pvzI17 K19 K20 K21 K22 K23 K24 pvzI18 pvzI19 K27 K28 K29 K30 pvzI20 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV21l; move HV21l before pvzI2; pose proof (proj2 pvzI2) as HV21r; move HV21r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K7l; move K7l before pvzI15; pose proof (proj2 pvzI15) as K7r; move K7r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K18l; move K18l before pvzI17; pose proof (proj2 pvzI17) as K18r; move K18r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K31l; move K31l before pvzI20; pose proof (proj2 pvzI20) as K31r; move K31r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 21%nat => Z_to_bv 64 vz_21 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 21%nat => vz_21 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbpkG5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpkG5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpkG5.kn0).
  { unfold know_ok, PbpkG5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K50]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpkG5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpkG5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 208) -> ~ (((vz_40 + 384) + 0) <= bv_unsigned a < ((vz_40 + 384) + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbpkG5.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpkG5.ps0) with 0x792dc in Hms. change (SR.ps_regs PbpkG5.ps0) with (map (fun i => (i, nth i PbpkG5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpkG5.ps0) with PbpkG5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpkG5.regs0 PbpkG5.regs_out0 60 KS_bpkG5 KS_bpkG5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG5.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpkG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K25l K25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia].
Qed.

Module PbpkG6 := BndP_Eb_027S9.LibSegEb_bpkG6.
Definition KS_bpkG6 : list nat := Eval vm_compute in (BG.kept_list 60 PbpkG6.regs0 PbpkG6.regs_out0).
Lemma KS_bpkG6_ok : BG.kept_ok 60 PbpkG6.regs0 PbpkG6.regs_out0 KS_bpkG6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpkG6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 64 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 19) = Z_to_bv 64 32 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 64) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + 768) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + 768) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 8 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 3 -> 4096 <= (V 40%nat) <= 140737488353792 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 768) 24 -> L5KA.zeros_at M ((((V 40%nat) + 768) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 768) \/ ((V 40%nat) + 768) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + 768) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 768) \/ ((V 40%nat) + 768) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 56 <= ((V 40%nat) + 768) \/ ((V 40%nat) + 768) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 768) \/ ((V 40%nat) + 768) + 24 <= (V 34%nat)) -> (65536 + 6864896 <= ((V 40%nat) + 768) \/ ((V 40%nat) + 768) + 24 <= 65536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737868 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 768) + 0) <= bv_unsigned a < (((V 40%nat) + 768) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 768) + 0) <= i < (((V 40%nat) + 768) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0be4 M) (st fx' R' 0x792dc M')
        /\ (forall x, In x KS_bpkG6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 776)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 768) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 40%nat) + 1536)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 768)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + 768)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 G19 G20 G21 pvzI14 K1 K2 K3 K4 K5 K6 pvzI15 K8 K9 K10 K11 K12 K13 K14 K15 pvzI16 K17 pvzI17 K19 K20 K21 K22 K23 K24 pvzI18 pvzI19 K27 K28 K29 K30 pvzI20 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV21l; move HV21l before pvzI2; pose proof (proj2 pvzI2) as HV21r; move HV21r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K7l; move K7l before pvzI15; pose proof (proj2 pvzI15) as K7r; move K7r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K18l; move K18l before pvzI17; pose proof (proj2 pvzI17) as K18r; move K18r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K31l; move K31l before pvzI20; pose proof (proj2 pvzI20) as K31r; move K31r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 21%nat => Z_to_bv 64 vz_21 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 21%nat => vz_21 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbpkG6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpkG6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpkG6.kn0).
  { unfold know_ok, PbpkG6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K50]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpkG6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpkG6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 208) -> ~ (((vz_40 + 768) + 0) <= bv_unsigned a < ((vz_40 + 768) + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbpkG6.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpkG6.ps0) with 0x792dc in Hms. change (SR.ps_regs PbpkG6.ps0) with (map (fun i => (i, nth i PbpkG6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpkG6.ps0) with PbpkG6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpkG6.regs0 PbpkG6.regs_out0 60 KS_bpkG6 KS_bpkG6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG6.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpkG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K25l K25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia].
Qed.

Module PbpkG7 := BndP_Eb_027S9.LibSegEb_bpkG7.
Definition KS_bpkG7 : list nat := Eval vm_compute in (BG.kept_list 60 PbpkG7.regs0 PbpkG7.regs_out0).
Lemma KS_bpkG7_ok : BG.kept_ok 60 PbpkG7.regs0 PbpkG7.regs_out0 KS_bpkG7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpkG7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 128 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 19) = Z_to_bv 64 64 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 64) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + 1536) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + 1536) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 8 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 3 -> 4096 <= (V 40%nat) <= 140737488352256 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 1536) 24 -> L5KA.zeros_at M ((((V 40%nat) + 1536) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 1536) \/ ((V 40%nat) + 1536) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + 1536) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 1536) \/ ((V 40%nat) + 1536) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 56 <= ((V 40%nat) + 1536) \/ ((V 40%nat) + 1536) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 1536) \/ ((V 40%nat) + 1536) + 24 <= (V 34%nat)) -> (65536 + 6864896 <= ((V 40%nat) + 1536) \/ ((V 40%nat) + 1536) + 24 <= 65536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737868 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 1536) + 0) <= bv_unsigned a < (((V 40%nat) + 1536) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 1536) + 0) <= i < (((V 40%nat) + 1536) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0be4 M) (st fx' R' 0x792dc M')
        /\ (forall x, In x KS_bpkG7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 1544)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 1536) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 40%nat) + 3072)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 1536)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + 1536)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 G19 G20 G21 pvzI14 K1 K2 K3 K4 K5 K6 pvzI15 K8 K9 K10 K11 K12 K13 K14 K15 pvzI16 K17 pvzI17 K19 K20 K21 K22 K23 K24 pvzI18 pvzI19 K27 K28 K29 K30 pvzI20 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV21l; move HV21l before pvzI2; pose proof (proj2 pvzI2) as HV21r; move HV21r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K7l; move K7l before pvzI15; pose proof (proj2 pvzI15) as K7r; move K7r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K18l; move K18l before pvzI17; pose proof (proj2 pvzI17) as K18r; move K18r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K31l; move K31l before pvzI20; pose proof (proj2 pvzI20) as K31r; move K31r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 21%nat => Z_to_bv 64 vz_21 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 21%nat => vz_21 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbpkG7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpkG7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpkG7.kn0).
  { unfold know_ok, PbpkG7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K50]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpkG7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpkG7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 208) -> ~ (((vz_40 + 1536) + 0) <= bv_unsigned a < ((vz_40 + 1536) + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbpkG7.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpkG7.ps0) with 0x792dc in Hms. change (SR.ps_regs PbpkG7.ps0) with (map (fun i => (i, nth i PbpkG7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpkG7.ps0) with PbpkG7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpkG7.regs0 PbpkG7.regs_out0 60 KS_bpkG7 KS_bpkG7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG7.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpkG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K25l K25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia].
Qed.

Module PbpkG8 := BndP_Eb_027S9.LibSegEb_bpkG8.
Definition KS_bpkG8 : list nat := Eval vm_compute in (BG.kept_list 60 PbpkG8.regs0 PbpkG8.regs_out0).
Lemma KS_bpkG8_ok : BG.kept_ok 60 PbpkG8.regs0 PbpkG8.regs_out0 KS_bpkG8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpkG8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 256 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 19) = Z_to_bv 64 128 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 64) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + 3072) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + 3072) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 8 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 3 -> 4096 <= (V 40%nat) <= 140737488349184 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 3072) 24 -> L5KA.zeros_at M ((((V 40%nat) + 3072) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 3072) \/ ((V 40%nat) + 3072) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + 3072) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 3072) \/ ((V 40%nat) + 3072) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 56 <= ((V 40%nat) + 3072) \/ ((V 40%nat) + 3072) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 3072) \/ ((V 40%nat) + 3072) + 24 <= (V 34%nat)) -> (65536 + 6864896 <= ((V 40%nat) + 3072) \/ ((V 40%nat) + 3072) + 24 <= 65536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737868 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 3072) + 0) <= bv_unsigned a < (((V 40%nat) + 3072) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 3072) + 0) <= i < (((V 40%nat) + 3072) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0be4 M) (st fx' R' 0x792dc M')
        /\ (forall x, In x KS_bpkG8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 3080)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 3072) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 40%nat) + 6144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 3072)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + 3072)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 G19 G20 G21 pvzI14 K1 K2 K3 K4 K5 K6 pvzI15 K8 K9 K10 K11 K12 K13 K14 K15 pvzI16 K17 pvzI17 K19 K20 K21 K22 K23 K24 pvzI18 pvzI19 K27 K28 K29 K30 pvzI20 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV21l; move HV21l before pvzI2; pose proof (proj2 pvzI2) as HV21r; move HV21r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K7l; move K7l before pvzI15; pose proof (proj2 pvzI15) as K7r; move K7r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K18l; move K18l before pvzI17; pose proof (proj2 pvzI17) as K18r; move K18r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K31l; move K31l before pvzI20; pose proof (proj2 pvzI20) as K31r; move K31r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 21%nat => Z_to_bv 64 vz_21 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 21%nat => vz_21 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbpkG8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpkG8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpkG8.kn0).
  { unfold know_ok, PbpkG8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K50]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpkG8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpkG8.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 208) -> ~ (((vz_40 + 3072) + 0) <= bv_unsigned a < ((vz_40 + 3072) + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbpkG8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpkG8.ps0) with 0x792dc in Hms. change (SR.ps_regs PbpkG8.ps0) with (map (fun i => (i, nth i PbpkG8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpkG8.ps0) with PbpkG8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpkG8.regs0 PbpkG8.regs_out0 60 KS_bpkG8 KS_bpkG8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG8.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpkG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K25l K25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia].
Qed.

Module PbpkG9 := BndP_Eb_027S9.LibSegEb_bpkG9.
Definition KS_bpkG9 : list nat := Eval vm_compute in (BG.kept_list 60 PbpkG9.regs0 PbpkG9.regs_out0).
Lemma KS_bpkG9_ok : BG.kept_ok 60 PbpkG9.regs0 PbpkG9.regs_out0 KS_bpkG9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpkG9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 512 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 19) = Z_to_bv 64 256 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 64) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + 6144) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + 6144) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 8 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 3 -> 4096 <= (V 40%nat) <= 140737488343040 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 6144) 24 -> L5KA.zeros_at M ((((V 40%nat) + 6144) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 6144) \/ ((V 40%nat) + 6144) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + 6144) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 6144) \/ ((V 40%nat) + 6144) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 56 <= ((V 40%nat) + 6144) \/ ((V 40%nat) + 6144) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 6144) \/ ((V 40%nat) + 6144) + 24 <= (V 34%nat)) -> (65536 + 6864896 <= ((V 40%nat) + 6144) \/ ((V 40%nat) + 6144) + 24 <= 65536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737868 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 6144) + 0) <= bv_unsigned a < (((V 40%nat) + 6144) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 6144) + 0) <= i < (((V 40%nat) + 6144) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0be4 M) (st fx' R' 0x792dc M')
        /\ (forall x, In x KS_bpkG9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 6152)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 6144) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 40%nat) + 12288)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 6144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + 6144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 G19 G20 G21 pvzI14 K1 K2 K3 K4 K5 K6 pvzI15 K8 K9 K10 K11 K12 K13 K14 K15 pvzI16 K17 pvzI17 K19 K20 K21 K22 K23 K24 pvzI18 pvzI19 K27 K28 K29 K30 pvzI20 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV21l; move HV21l before pvzI2; pose proof (proj2 pvzI2) as HV21r; move HV21r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K7l; move K7l before pvzI15; pose proof (proj2 pvzI15) as K7r; move K7r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K18l; move K18l before pvzI17; pose proof (proj2 pvzI17) as K18r; move K18r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K31l; move K31l before pvzI20; pose proof (proj2 pvzI20) as K31r; move K31r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 21%nat => Z_to_bv 64 vz_21 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 21%nat => vz_21 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbpkG9.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpkG9.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpkG9.kn0).
  { unfold know_ok, PbpkG9.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K50]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpkG9.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpkG9.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 208) -> ~ (((vz_40 + 6144) + 0) <= bv_unsigned a < ((vz_40 + 6144) + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbpkG9.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpkG9.ps0) with 0x792dc in Hms. change (SR.ps_regs PbpkG9.ps0) with (map (fun i => (i, nth i PbpkG9.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpkG9.ps0) with PbpkG9.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpkG9.regs0 PbpkG9.regs_out0 60 KS_bpkG9 KS_bpkG9_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG9.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpkG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K25l K25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia].
Qed.

Module PbpkG10 := BndP_Eb_027S9.LibSegEb_bpkG10.
Definition KS_bpkG10 : list nat := Eval vm_compute in (BG.kept_list 60 PbpkG10.regs0 PbpkG10.regs_out0).
Lemma KS_bpkG10_ok : BG.kept_ok 60 PbpkG10.regs0 PbpkG10.regs_out0 KS_bpkG10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpkG10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 1024 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 19) = Z_to_bv 64 512 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 64) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + 12288) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + 12288) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 8 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 3 -> 4096 <= (V 40%nat) <= 140737488330752 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 12288) 24 -> L5KA.zeros_at M ((((V 40%nat) + 12288) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 12288) \/ ((V 40%nat) + 12288) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + 12288) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 12288) \/ ((V 40%nat) + 12288) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 56 <= ((V 40%nat) + 12288) \/ ((V 40%nat) + 12288) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 12288) \/ ((V 40%nat) + 12288) + 24 <= (V 34%nat)) -> (65536 + 6864896 <= ((V 40%nat) + 12288) \/ ((V 40%nat) + 12288) + 24 <= 65536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737868 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 12288) + 0) <= bv_unsigned a < (((V 40%nat) + 12288) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 12288) + 0) <= i < (((V 40%nat) + 12288) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0be4 M) (st fx' R' 0x792dc M')
        /\ (forall x, In x KS_bpkG10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 12296)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 12288) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 40%nat) + 24576)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 12288)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + 12288)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 G19 G20 G21 pvzI14 K1 K2 K3 K4 K5 K6 pvzI15 K8 K9 K10 K11 K12 K13 K14 K15 pvzI16 K17 pvzI17 K19 K20 K21 K22 K23 K24 pvzI18 pvzI19 K27 K28 K29 K30 pvzI20 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV21l; move HV21l before pvzI2; pose proof (proj2 pvzI2) as HV21r; move HV21r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K7l; move K7l before pvzI15; pose proof (proj2 pvzI15) as K7r; move K7r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K18l; move K18l before pvzI17; pose proof (proj2 pvzI17) as K18r; move K18r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K31l; move K31l before pvzI20; pose proof (proj2 pvzI20) as K31r; move K31r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 21%nat => Z_to_bv 64 vz_21 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 21%nat => vz_21 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbpkG10.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpkG10.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpkG10.kn0).
  { unfold know_ok, PbpkG10.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K50]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpkG10.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpkG10.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 208) -> ~ (((vz_40 + 12288) + 0) <= bv_unsigned a < ((vz_40 + 12288) + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbpkG10.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpkG10.ps0) with 0x792dc in Hms. change (SR.ps_regs PbpkG10.ps0) with (map (fun i => (i, nth i PbpkG10.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpkG10.ps0) with PbpkG10.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpkG10.regs0 PbpkG10.regs_out0 60 KS_bpkG10 KS_bpkG10_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG10.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpkG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K25l K25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia].
Qed.

Module PbpkG11 := BndP_Eb_027S9.LibSegEb_bpkG11.
Definition KS_bpkG11 : list nat := Eval vm_compute in (BG.kept_list 60 PbpkG11.regs0 PbpkG11.regs_out0).
Lemma KS_bpkG11_ok : BG.kept_ok 60 PbpkG11.regs0 PbpkG11.regs_out0 KS_bpkG11 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpkG11_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 2048 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 88) -> getr R (reg 19) = Z_to_bv 64 1024 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 64) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355263 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 7 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 56 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 56 <= 65536) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 32) ((V 36%nat) + 24576) -> L5.u64_at RSEGS M ((V 33%nat) + 40) ((V 36%nat) + 24576) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 8 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 56 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 3 -> 4096 <= (V 40%nat) <= 140737488306176 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 24576) 24 -> L5KA.zeros_at M ((((V 40%nat) + 24576) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 24576) \/ ((V 40%nat) + 24576) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + 24576) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 24576) \/ ((V 40%nat) + 24576) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 56 <= ((V 40%nat) + 24576) \/ ((V 40%nat) + 24576) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 24576) \/ ((V 40%nat) + 24576) + 24 <= (V 34%nat)) -> (65536 + 6864896 <= ((V 40%nat) + 24576) \/ ((V 40%nat) + 24576) + 24 <= 65536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 737868 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 32) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 32) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 33%nat) + 24) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 24576) + 0) <= bv_unsigned a < (((V 40%nat) + 24576) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ ((((V 40%nat) + 24576) + 0) <= i < (((V 40%nat) + 24576) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0be4 M) (st fx' R' 0x792dc M')
        /\ (forall x, In x KS_bpkG11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737940
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 24584)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 24576) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 40%nat) + 49152)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 24576)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 40%nat) + 24576)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 33%nat) + 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 G19 G20 G21 pvzI14 K1 K2 K3 K4 K5 K6 pvzI15 K8 K9 K10 K11 K12 K13 K14 K15 pvzI16 K17 pvzI17 K19 K20 K21 K22 K23 K24 pvzI18 pvzI19 K27 K28 K29 K30 pvzI20 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV21l; move HV21l before pvzI2; pose proof (proj2 pvzI2) as HV21r; move HV21r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K7l; move K7l before pvzI15; pose proof (proj2 pvzI15) as K7r; move K7r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K18l; move K18l before pvzI17; pose proof (proj2 pvzI17) as K18r; move K18r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K31l; move K31l before pvzI20; pose proof (proj2 pvzI20) as K31r; move K31r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 21%nat => Z_to_bv 64 vz_21 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 21%nat => vz_21 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbpkG11.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpkG11.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpkG11.kn0).
  { unfold know_ok, PbpkG11.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | clear - HV34l HV34r K18l K18r K20 K23 K24 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K24 K34) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | clear - HV2l HV2r K0l K0r K11 K23 K32; lia | exactA K50]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpkG11.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpkG11.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 208) -> ~ (((vz_40 + 24576) + 0) <= bv_unsigned a < ((vz_40 + 24576) + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbpkG11.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K32 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpkG11.ps0) with 0x792dc in Hms. change (SR.ps_regs PbpkG11.ps0) with (map (fun i => (i, nth i PbpkG11.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpkG11.ps0) with PbpkG11.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpkG11.regs0 PbpkG11.regs_out0 60 KS_bpkG11 KS_bpkG11_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpkG11.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpkG11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K25l K25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K26l K26r K30 K31l K31r K32 K33 K34 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K24 K33) | clear; lia].
Qed.

End PEBEPP3.
