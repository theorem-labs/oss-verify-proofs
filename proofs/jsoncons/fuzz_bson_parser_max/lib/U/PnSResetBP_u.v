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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_rbSS_u LibSegBs_rbSL_u LibSegBs_rbLS_u LibSegBs_rbLL_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRBP.
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
Module PrbSS := LibSegBs_rbSS_u.
Definition KS_rbSS : list nat := Eval vm_compute in (BG.kept_list 48 PrbSS.regs0 PrbSS.regs_out0).
Lemma KS_rbSS_ok : BG.kept_ok 48 PrbSS.regs0 PrbSS.regs_out0 KS_rbSS = true. Proof. vm_compute. reflexivity. Qed.
Lemma rbSS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 416 ->
  4096 <= (bv_unsigned (getr R (reg 10))) <= 140737488355328 -> aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 416 <= ((V 2%nat) - 80)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 320) (V 35%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 392) (V 36%nat) -> 4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 16 -> 40 <= (V 39%nat) <= 81920 ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 408) ((V 36%nat) + (V 39%nat)) -> L5.writable RSEGS M (V 36%nat) 40 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 40 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 40 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 416 <= (V 36%nat)) ->
  L5.u8_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 344) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = false -> L5.u8_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 368) (V 34%nat) ->
  0 <= (V 34%nat) <= 255 -> Z.testbit (V 34%nat) 0 = false ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 328) (V 35%nat) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 400) ((V 36%nat) + 40) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 40) <= bv_unsigned a < ((V 2%nat) - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 8) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 328) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 328) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 400) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 400) + 8) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 344) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 344) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 368) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 368) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 40) <= i < ((V 2%nat) - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= i < ((bv_unsigned (getr R (reg 10))) + 8) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 328) <= i < ((bv_unsigned (getr R (reg 10))) + 328) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 400) <= i < ((bv_unsigned (getr R (reg 10))) + 400) + 8) -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 344) <= i < ((bv_unsigned (getr R (reg 10))) + 344) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 368) <= i < ((bv_unsigned (getr R (reg 10))) + 368) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36a90 M) (st fx' R' 0x36bb8 M')
        /\ (forall x, In x KS_rbSS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 40
        /\ getr R' (reg 12) = Z_to_bv 64 40
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 400) ((V 36%nat) + 40)
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.u32_at RSEGS M' (V 36%nat) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 32) 0
        /\ (L5.u8_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 368) 0 /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + 368) + 1) 0)
        /\ (L5.u8_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 344) 0 /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + 344) + 1) 0)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 328) (V 35%nat)
        /\ (L5.u8_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 8) 1 /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + 8) + 1) 0)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 pvzI7 K1 K2 K3 pvzI8 K5 K6 K7 K8 pvzI9 K10 pvzI10 K12 K13 K14 K15 K16 pvzI11 K18 K19 pvzI12 K21 K22 K23.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K9l; move K9l before pvzI9; pose proof (proj2 pvzI9) as K9r; move K9r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K11l; move K11l before pvzI10; pose proof (proj2 pvzI10) as K11r; move K11r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K17l; move K17l before pvzI11; pose proof (proj2 pvzI11) as K17r; move K17r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K20l; move K20l before pvzI12; pose proof (proj2 pvzI12) as K20r; move K20r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PrbSS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrbSS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrbSS.kn0).
  { unfold know_ok, PrbSS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K14; lia | clear - HV2l HV2r K0l K0r K6 K14; lia | clear - HV2l HV2r K0l K0r K6 K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K4l K4r K6 K15) | evalEk ZA ltac:(clear) | clear - K4l K4r K6 K15; lia | clear - K4l K4r K6 K15; lia | clear - K4l K4r K6 K15; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K4l K4r K6 K15) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K4l K4r K6 K15) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K6 K15) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - K4l K4r K6 K15; lia | clear - K4l K4r K6 K15; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15) | clear - K4l K4r K6 K15; lia | clear - K4l K4r K6 K15; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15) | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 HV39l HV39r K11l K11r) | clear - K4l K4r K6 K15; lia | clear - K4l K4r K6 K15; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K9l K9r K14 K15; lia | clear - HV36l HV36r K9l K9r K14 K15; lia | clear - HV36l HV36r K9l K9r K14 K15; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K6 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K4l K4r K6 K15) | evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K18) | clear - K4l K4r K6 K15; lia | clear - K4l K4r K6 K15; lia | byte_tac ltac:(clear - HV33l HV33r K17l K17r K18) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K18) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K18) | clear; lia | rewrite (L5K.land1_bit0_false vz_33 ltac:(clear - HV33l HV33r K17l K17r K18; lia) K18); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K4l K4r K6 K15) | evalEk ZA ltac:(clear - HV34l HV34r K20l K20r K21) | clear - K4l K4r K6 K15; lia | clear - K4l K4r K6 K15; lia | byte_tac ltac:(clear - HV34l HV34r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV34l HV34r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_false vz_34 ltac:(clear - HV34l HV34r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - K4l K4r K6 K15; lia | clear - K4l K4r K6 K15; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15) | clear - K4l K4r K6 K15; lia | clear - K4l K4r K6 K15; lia | exactA K23]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrbSS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrbSS.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 40) <= bv_unsigned a < (vz_2 - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 8) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 328) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 328) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 400) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 400) + 8) -> ~ ((vz_36 + 0) <= bv_unsigned a < (vz_36 + 0) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 344) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 344) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 368) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 368) + 2) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold PrbSS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K9l K9r K14 K15 Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 Hn6; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrbSS.ps0) with 0x36bb8 in Hms. change (SR.ps_regs PrbSS.ps0) with (map (fun i => (i, nth i PrbSS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrbSS.ps0) with PrbSS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrbSS.regs0 PrbSS.regs_out0 48 KS_rbSS KS_rbSS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrbSS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrbSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrbSS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrbSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrbSS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrbSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8x2_of_KWord2a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  split. { eapply u8x2_of_KWord2a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u8x2_of_KWord2a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrbSL := LibSegBs_rbSL_u.
Definition KS_rbSL : list nat := Eval vm_compute in (BG.kept_list 48 PrbSL.regs0 PrbSL.regs_out0).
Lemma KS_rbSL_ok : BG.kept_ok 48 PrbSL.regs0 PrbSL.regs_out0 KS_rbSL = true. Proof. vm_compute. reflexivity. Qed.
Lemma rbSL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 416 ->
  4096 <= (bv_unsigned (getr R (reg 10))) <= 140737488355328 -> aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 416 <= ((V 2%nat) - 80)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 320) (V 35%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 392) (V 36%nat) -> 4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 16 -> 40 <= (V 39%nat) <= 81920 ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 408) ((V 36%nat) + (V 39%nat)) -> L5.writable RSEGS M (V 36%nat) 40 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 40 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 40 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 416 <= (V 36%nat)) ->
  L5.u8_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 344) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = false -> L5.u8_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 368) (V 34%nat) ->
  0 <= (V 34%nat) <= 255 -> Z.testbit (V 34%nat) 0 = true -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 384) (V 38%nat) -> 4096 <= (V 38%nat) <= 140737488355328 ->
  L5.writable RSEGS M (V 38%nat) 1 -> (((V 2%nat) - 80) + 80 <= (V 38%nat) \/ (V 38%nat) + 1 <= ((V 2%nat) - 80)) -> ((V 38%nat) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 416 <= (V 38%nat)) -> ((V 38%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 40 <= (V 38%nat)) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 328) (V 35%nat) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 400) ((V 36%nat) + 40) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 40) <= bv_unsigned a < ((V 2%nat) - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 8) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 328) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 328) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 400) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 400) + 8) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 344) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 344) + 2) -> ~ (((V 38%nat) + 0) <= bv_unsigned a < ((V 38%nat) + 0) + 1) -> ~ (((bv_unsigned (getr R (reg 10))) + 376) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 376) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 40) <= i < ((V 2%nat) - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= i < ((bv_unsigned (getr R (reg 10))) + 8) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 328) <= i < ((bv_unsigned (getr R (reg 10))) + 328) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 400) <= i < ((bv_unsigned (getr R (reg 10))) + 400) + 8) -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 344) <= i < ((bv_unsigned (getr R (reg 10))) + 344) + 2) -> ~ (((V 38%nat) + 0) <= i < ((V 38%nat) + 0) + 1) -> ~ (((bv_unsigned (getr R (reg 10))) + 376) <= i < ((bv_unsigned (getr R (reg 10))) + 376) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36a90 M) (st fx' R' 0x36bb8 M')
        /\ (forall x, In x KS_rbSL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 40
        /\ getr R' (reg 12) = Z_to_bv 64 40
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 400) ((V 36%nat) + 40)
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.u32_at RSEGS M' (V 36%nat) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 32) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 376) 0
        /\ L5.u8_at RSEGS M' (V 38%nat) 0
        /\ (L5.u8_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 344) 0 /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + 344) + 1) 0)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 328) (V 35%nat)
        /\ (L5.u8_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 8) 1 /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + 8) + 1) 0)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 K3 pvzI9 K5 K6 K7 K8 pvzI10 K10 pvzI11 K12 K13 K14 K15 K16 pvzI12 K18 K19 pvzI13 K21 K22 pvzI14 K24 K25 K26 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K9l; move K9l before pvzI10; pose proof (proj2 pvzI10) as K9r; move K9r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K17l; move K17l before pvzI12; pose proof (proj2 pvzI12) as K17r; move K17r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K20l; move K20l before pvzI13; pose proof (proj2 pvzI13) as K20r; move K20r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K23l; move K23l before pvzI14; pose proof (proj2 pvzI14) as K23r; move K23r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PrbSL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrbSL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrbSL.kn0).
  { unfold know_ok, PrbSL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K25) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K25) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K25) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K14 K25; lia | clear - HV2l HV2r K0l K0r K6 K14 K25; lia | clear - HV2l HV2r K0l K0r K6 K14 K25; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | evalEk ZA ltac:(clear) | clear - K4l K4r K6 K15 K26; lia | clear - K4l K4r K6 K15 K26; lia | clear - K4l K4r K6 K15 K26; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - K4l K4r K6 K15 K26; lia | clear - K4l K4r K6 K15 K26; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | clear - K4l K4r K6 K15 K26; lia | clear - K4l K4r K6 K15 K26; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27 HV39l HV39r K11l K11r) | clear - K4l K4r K6 K15 K26; lia | clear - K4l K4r K6 K15 K26; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K9l K9r K14 K15 K27; lia | clear - HV36l HV36r K9l K9r K14 K15 K27; lia | clear - HV36l HV36r K9l K9r K14 K15 K27; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K18) | clear - K4l K4r K6 K15 K26; lia | clear - K4l K4r K6 K15 K26; lia | byte_tac ltac:(clear - HV33l HV33r K17l K17r K18) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K18) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K18) | clear; lia | rewrite (L5K.land1_bit0_false vz_33 ltac:(clear - HV33l HV33r K17l K17r K18; lia) K18); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | evalEk ZA ltac:(clear - HV34l HV34r K20l K20r K21) | clear - K4l K4r K6 K15 K26; lia | clear - K4l K4r K6 K15 K26; lia | byte_tac ltac:(clear - HV34l HV34r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV34l HV34r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_true vz_34 ltac:(clear - HV34l HV34r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | evalEk ZA ltac:(clear - HV38l HV38r K23l K23r K25 K26 K27) | clear - K4l K4r K6 K15 K26; lia | clear - K4l K4r K6 K15 K26; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K23l K23r K25 K26 K27) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K23l K23r K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K23l K23r K25 K26 K27; lia | clear - HV38l HV38r K23l K23r K25 K26 K27; lia | clear - HV38l HV38r K23l K23r K25 K26 K27; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K23l K23r K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K23l K23r K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K23l K23r K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - K4l K4r K6 K15 K26; lia | clear - K4l K4r K6 K15 K26; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K26) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | clear - K4l K4r K6 K15 K26; lia | clear - K4l K4r K6 K15 K26; lia | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrbSL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrbSL.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 40) <= bv_unsigned a < (vz_2 - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 8) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 328) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 328) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 400) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 400) + 8) -> ~ ((vz_36 + 0) <= bv_unsigned a < (vz_36 + 0) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 344) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 344) + 2) -> ~ ((vz_38 + 0) <= bv_unsigned a < (vz_38 + 0) + 1) -> ~ (((bv_unsigned (getr R (reg 10))) + 376) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 376) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7. apply Hfr. unfold PrbSL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K14 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K14 K25 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K26) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K26) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K26 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K26) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K26 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K9l K9r K14 K15 K27 Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K26) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K26 Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV38l HV38r K23l K23r K25 K26 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV38l HV38r K23l K23r K25 K26 K27 Hn6; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K26) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K26 Hn7; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrbSL.ps0) with 0x36bb8 in Hms. change (SR.ps_regs PrbSL.ps0) with (map (fun i => (i, nth i PrbSL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrbSL.ps0) with PrbSL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrbSL.regs0 PrbSL.regs_out0 48 KS_rbSL KS_rbSL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrbSL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrbSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrbSL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrbSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrbSL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrbSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K26) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV38l HV38r K23l K23r K25 K26 K27) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8x2_of_KWord2a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K26) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u8x2_of_KWord2a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K14 K25) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K14 K25) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrbLS := LibSegBs_rbLS_u.
Definition KS_rbLS : list nat := Eval vm_compute in (BG.kept_list 48 PrbLS.regs0 PrbLS.regs_out0).
Lemma KS_rbLS_ok : BG.kept_ok 48 PrbLS.regs0 PrbLS.regs_out0 KS_rbLS = true. Proof. vm_compute. reflexivity. Qed.
Lemma rbLS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 416 ->
  4096 <= (bv_unsigned (getr R (reg 10))) <= 140737488355328 -> aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 416 <= ((V 2%nat) - 80)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 320) (V 35%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 392) (V 36%nat) -> 4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 16 -> 40 <= (V 39%nat) <= 81920 ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 408) ((V 36%nat) + (V 39%nat)) -> L5.writable RSEGS M (V 36%nat) 40 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 40 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 40 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 416 <= (V 36%nat)) ->
  L5.u8_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 344) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 360) (V 37%nat) ->
  4096 <= (V 37%nat) <= 140737488355328 -> L5.writable RSEGS M (V 37%nat) 1 -> (((V 2%nat) - 80) + 80 <= (V 37%nat) \/ (V 37%nat) + 1 <= ((V 2%nat) - 80)) -> ((V 37%nat) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 416 <= (V 37%nat)) ->
  ((V 37%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 40 <= (V 37%nat)) -> L5.u8_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 368) (V 34%nat) -> 0 <= (V 34%nat) <= 255 -> Z.testbit (V 34%nat) 0 = false ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 328) (V 35%nat) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 400) ((V 36%nat) + 40) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 40) <= bv_unsigned a < ((V 2%nat) - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 8) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 328) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 328) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 400) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 400) + 8) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 40) -> ~ (((V 37%nat) + 0) <= bv_unsigned a < ((V 37%nat) + 0) + 1) -> ~ (((bv_unsigned (getr R (reg 10))) + 352) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 352) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 368) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 368) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 40) <= i < ((V 2%nat) - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= i < ((bv_unsigned (getr R (reg 10))) + 8) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 328) <= i < ((bv_unsigned (getr R (reg 10))) + 328) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 400) <= i < ((bv_unsigned (getr R (reg 10))) + 400) + 8) -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 40) -> ~ (((V 37%nat) + 0) <= i < ((V 37%nat) + 0) + 1) -> ~ (((bv_unsigned (getr R (reg 10))) + 352) <= i < ((bv_unsigned (getr R (reg 10))) + 352) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 368) <= i < ((bv_unsigned (getr R (reg 10))) + 368) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36a90 M) (st fx' R' 0x36bb8 M')
        /\ (forall x, In x KS_rbLS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 40
        /\ getr R' (reg 12) = Z_to_bv 64 40
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 400) ((V 36%nat) + 40)
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.u32_at RSEGS M' (V 36%nat) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 32) 0
        /\ (L5.u8_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 368) 0 /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + 368) + 1) 0)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 352) 0
        /\ L5.u8_at RSEGS M' (V 37%nat) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 328) (V 35%nat)
        /\ (L5.u8_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 8) 1 /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + 8) + 1) 0)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 K3 pvzI9 K5 K6 K7 K8 pvzI10 K10 pvzI11 K12 K13 K14 K15 K16 pvzI12 K18 K19 pvzI13 K21 K22 K23 K24 K25 pvzI14 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K9l; move K9l before pvzI10; pose proof (proj2 pvzI10) as K9r; move K9r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K17l; move K17l before pvzI12; pose proof (proj2 pvzI12) as K17r; move K17r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K20l; move K20l before pvzI13; pose proof (proj2 pvzI13) as K20r; move K20r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K26l; move K26l before pvzI14; pose proof (proj2 pvzI14) as K26r; move K26r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PrbLS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrbLS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrbLS.kn0).
  { unfold know_ok, PrbLS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K14 K22; lia | clear - HV2l HV2r K0l K0r K6 K14 K22; lia | clear - HV2l HV2r K0l K0r K6 K14 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | evalEk ZA ltac:(clear) | clear - K4l K4r K6 K15 K23; lia | clear - K4l K4r K6 K15 K23; lia | clear - K4l K4r K6 K15 K23; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - K4l K4r K6 K15 K23; lia | clear - K4l K4r K6 K15 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | clear - K4l K4r K6 K15 K23; lia | clear - K4l K4r K6 K15 K23; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 HV39l HV39r K11l K11r) | clear - K4l K4r K6 K15 K23; lia | clear - K4l K4r K6 K15 K23; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K9l K9r K14 K15 K24; lia | clear - HV36l HV36r K9l K9r K14 K15 K24; lia | clear - HV36l HV36r K9l K9r K14 K15 K24; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K18) | clear - K4l K4r K6 K15 K23; lia | clear - K4l K4r K6 K15 K23; lia | byte_tac ltac:(clear - HV33l HV33r K17l K17r K18) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K18) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K18) | clear; lia | rewrite (L5K.land1_bit0_true vz_33 ltac:(clear - HV33l HV33r K17l K17r K18; lia) K18); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24) | clear - K4l K4r K6 K15 K23; lia | clear - K4l K4r K6 K15 K23; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r K22 K23 K24; lia | clear - HV37l HV37r K20l K20r K22 K23 K24; lia | clear - HV37l HV37r K20l K20r K22 K23 K24; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K27) | clear - K4l K4r K6 K15 K23; lia | clear - K4l K4r K6 K15 K23; lia | byte_tac ltac:(clear - HV34l HV34r K26l K26r K27) | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K27) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K27) | clear; lia | rewrite (L5K.land1_bit0_false vz_34 ltac:(clear - HV34l HV34r K26l K26r K27; lia) K27); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - K4l K4r K6 K15 K23; lia | clear - K4l K4r K6 K15 K23; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | clear - K4l K4r K6 K15 K23; lia | clear - K4l K4r K6 K15 K23; lia | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrbLS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrbLS.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 40) <= bv_unsigned a < (vz_2 - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 8) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 328) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 328) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 400) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 400) + 8) -> ~ ((vz_36 + 0) <= bv_unsigned a < (vz_36 + 0) + 40) -> ~ ((vz_37 + 0) <= bv_unsigned a < (vz_37 + 0) + 1) -> ~ (((bv_unsigned (getr R (reg 10))) + 352) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 352) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 368) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 368) + 2) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7. apply Hfr. unfold PrbLS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K14 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K23 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K23 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K23 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K9l K9r K14 K15 K24 Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K20l K20r K22 K23 K24 Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K23 Hn6; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K23 Hn7; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrbLS.ps0) with 0x36bb8 in Hms. change (SR.ps_regs PrbLS.ps0) with (map (fun i => (i, nth i PrbLS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrbLS.ps0) with PrbLS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrbLS.regs0 PrbLS.regs_out0 48 KS_rbLS KS_rbLS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrbLS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrbLS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrbLS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrbLS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrbLS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrbLS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8x2_of_KWord2a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u8x2_of_KWord2a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrbLL := LibSegBs_rbLL_u.
Definition KS_rbLL : list nat := Eval vm_compute in (BG.kept_list 48 PrbLL.regs0 PrbLL.regs_out0).
Lemma KS_rbLL_ok : BG.kept_ok 48 PrbLL.regs0 PrbLL.regs_out0 KS_rbLL = true. Proof. vm_compute. reflexivity. Qed.
Lemma rbLL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 416 ->
  4096 <= (bv_unsigned (getr R (reg 10))) <= 140737488355328 -> aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 416 <= ((V 2%nat) - 80)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 320) (V 35%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 392) (V 36%nat) -> 4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 16 -> 40 <= (V 39%nat) <= 81920 ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 408) ((V 36%nat) + (V 39%nat)) -> L5.writable RSEGS M (V 36%nat) 40 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 40 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 40 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 416 <= (V 36%nat)) ->
  L5.u8_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 344) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 360) (V 37%nat) ->
  4096 <= (V 37%nat) <= 140737488355328 -> L5.writable RSEGS M (V 37%nat) 1 -> (((V 2%nat) - 80) + 80 <= (V 37%nat) \/ (V 37%nat) + 1 <= ((V 2%nat) - 80)) -> ((V 37%nat) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 416 <= (V 37%nat)) ->
  ((V 37%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 40 <= (V 37%nat)) -> L5.u8_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 368) (V 34%nat) -> 0 <= (V 34%nat) <= 255 -> Z.testbit (V 34%nat) 0 = true ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 384) (V 38%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> L5.writable RSEGS M (V 38%nat) 1 -> (((V 2%nat) - 80) + 80 <= (V 38%nat) \/ (V 38%nat) + 1 <= ((V 2%nat) - 80)) ->
  ((V 38%nat) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 416 <= (V 38%nat)) -> ((V 38%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 40 <= (V 38%nat)) -> ((V 37%nat) + 1 <= (V 38%nat) \/ (V 38%nat) + 1 <= (V 37%nat)) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 328) (V 35%nat) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 400) ((V 36%nat) + 40) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 40) <= bv_unsigned a < ((V 2%nat) - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 8) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 328) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 328) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 400) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 400) + 8) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 40) -> ~ (((V 37%nat) + 0) <= bv_unsigned a < ((V 37%nat) + 0) + 1) -> ~ (((bv_unsigned (getr R (reg 10))) + 352) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 352) + 8) -> ~ (((V 38%nat) + 0) <= bv_unsigned a < ((V 38%nat) + 0) + 1) -> ~ (((bv_unsigned (getr R (reg 10))) + 376) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 376) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 40) <= i < ((V 2%nat) - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= i < ((bv_unsigned (getr R (reg 10))) + 8) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 328) <= i < ((bv_unsigned (getr R (reg 10))) + 328) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 400) <= i < ((bv_unsigned (getr R (reg 10))) + 400) + 8) -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 40) -> ~ (((V 37%nat) + 0) <= i < ((V 37%nat) + 0) + 1) -> ~ (((bv_unsigned (getr R (reg 10))) + 352) <= i < ((bv_unsigned (getr R (reg 10))) + 352) + 8) -> ~ (((V 38%nat) + 0) <= i < ((V 38%nat) + 0) + 1) -> ~ (((bv_unsigned (getr R (reg 10))) + 376) <= i < ((bv_unsigned (getr R (reg 10))) + 376) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36a90 M) (st fx' R' 0x36bb8 M')
        /\ (forall x, In x KS_rbLL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 40
        /\ getr R' (reg 12) = Z_to_bv 64 40
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 400) ((V 36%nat) + 40)
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.u32_at RSEGS M' (V 36%nat) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 32) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 376) 0
        /\ L5.u8_at RSEGS M' (V 38%nat) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 352) 0
        /\ L5.u8_at RSEGS M' (V 37%nat) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 328) (V 35%nat)
        /\ (L5.u8_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 8) 1 /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + 8) + 1) 0)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 pvzI9 K1 K2 K3 pvzI10 K5 K6 K7 K8 pvzI11 K10 pvzI12 K12 K13 K14 K15 K16 pvzI13 K18 K19 pvzI14 K21 K22 K23 K24 K25 pvzI15 K27 K28 pvzI16 K30 K31 K32 K33 K34 K35 K36.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV39l; move HV39l before pvzI8; pose proof (proj2 pvzI8) as HV39r; move HV39r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K4l; move K4l before pvzI10; pose proof (proj2 pvzI10) as K4r; move K4r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K9l; move K9l before pvzI11; pose proof (proj2 pvzI11) as K9r; move K9r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K11l; move K11l before pvzI12; pose proof (proj2 pvzI12) as K11r; move K11r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K17l; move K17l before pvzI13; pose proof (proj2 pvzI13) as K17r; move K17r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K20l; move K20l before pvzI14; pose proof (proj2 pvzI14) as K20r; move K20r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K26l; move K26l before pvzI15; pose proof (proj2 pvzI15) as K26r; move K26r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K29l; move K29l before pvzI16; pose proof (proj2 pvzI16) as K29r; move K29r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PrbLL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrbLL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrbLL.kn0).
  { unfold know_ok, PrbLL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22 K31) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22 K31) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22 K31) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K14 K22 K31; lia | clear - HV2l HV2r K0l K0r K6 K14 K22 K31; lia | clear - HV2l HV2r K0l K0r K6 K14 K22 K31; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear) | clear - K4l K4r K6 K15 K23 K32; lia | clear - K4l K4r K6 K15 K23 K32; lia | clear - K4l K4r K6 K15 K23 K32; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22 K31) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - K4l K4r K6 K15 K23 K32; lia | clear - K4l K4r K6 K15 K23 K32; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | clear - K4l K4r K6 K15 K23 K32; lia | clear - K4l K4r K6 K15 K23 K32; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33 HV39l HV39r K11l K11r) | clear - K4l K4r K6 K15 K23 K32; lia | clear - K4l K4r K6 K15 K23 K32; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K9l K9r K14 K15 K24 K33; lia | clear - HV36l HV36r K9l K9r K14 K15 K24 K33; lia | clear - HV36l HV36r K9l K9r K14 K15 K24 K33; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22 K31) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K18) | clear - K4l K4r K6 K15 K23 K32; lia | clear - K4l K4r K6 K15 K23 K32; lia | byte_tac ltac:(clear - HV33l HV33r K17l K17r K18) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K18) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K18) | clear; lia | rewrite (L5K.land1_bit0_true vz_33 ltac:(clear - HV33l HV33r K17l K17r K18; lia) K18); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24 K34) | clear - K4l K4r K6 K15 K23 K32; lia | clear - K4l K4r K6 K15 K23 K32; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24 K34) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24 K34) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r K22 K23 K24 K34; lia | clear - HV37l HV37r K20l K20r K22 K23 K24 K34; lia | clear - HV37l HV37r K20l K20r K22 K23 K24 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22 K31) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24 K34) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K27) | clear - K4l K4r K6 K15 K23 K32; lia | clear - K4l K4r K6 K15 K23 K32; lia | byte_tac ltac:(clear - HV34l HV34r K26l K26r K27) | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K27) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K27) | clear; lia | rewrite (L5K.land1_bit0_true vz_34 ltac:(clear - HV34l HV34r K26l K26r K27; lia) K27); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear - HV38l HV38r K29l K29r K31 K32 K33 K34) | clear - K4l K4r K6 K15 K23 K32; lia | clear - K4l K4r K6 K15 K23 K32; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K29l K29r K31 K32 K33 K34) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K29l K29r K31 K32 K33 K34) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K29l K29r K31 K32 K33 K34; lia | clear - HV38l HV38r K29l K29r K31 K32 K33 K34; lia | clear - HV38l HV38r K29l K29r K31 K32 K33 K34; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22 K31) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K29l K29r K31 K32 K33 K34) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K29l K29r K31 K32 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K29l K29r K31 K32 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K29l K29r K31 K32 K33 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - K4l K4r K6 K15 K23 K32; lia | clear - K4l K4r K6 K15 K23 K32; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk ZA ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | clear - K4l K4r K6 K15 K23 K32; lia | clear - K4l K4r K6 K15 K23 K32; lia | exactA K36]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrbLL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrbLL.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 40) <= bv_unsigned a < (vz_2 - 40) + 40) -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 8) + 2) -> ~ (((bv_unsigned (getr R (reg 10))) + 328) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 328) + 8) -> ~ (((bv_unsigned (getr R (reg 10))) + 400) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 400) + 8) -> ~ ((vz_36 + 0) <= bv_unsigned a < (vz_36 + 0) + 40) -> ~ ((vz_37 + 0) <= bv_unsigned a < (vz_37 + 0) + 1) -> ~ (((bv_unsigned (getr R (reg 10))) + 352) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 352) + 8) -> ~ ((vz_38 + 0) <= bv_unsigned a < (vz_38 + 0) + 1) -> ~ (((bv_unsigned (getr R (reg 10))) + 376) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 376) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8. apply Hfr. unfold PrbLL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22 K31) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K14 K22 K31 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K23 K32 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K23 K32 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K23 K32 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K9l K9r K14 K15 K24 K33 Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K20l K20r K22 K23 K24 K34 Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K23 K32 Hn6; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV38l HV38r K29l K29r K31 K32 K33 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV38l HV38r K29l K29r K31 K32 K33 K34 Hn7; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K6 K15 K23 K32 Hn8; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrbLL.ps0) with 0x36bb8 in Hms. change (SR.ps_regs PrbLL.ps0) with (map (fun i => (i, nth i PrbLL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrbLL.ps0) with PrbLL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrbLL.regs0 PrbLL.regs_out0 48 KS_rbLL KS_rbLL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrbLL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrbLL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrbLL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrbLL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrbLL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrbLL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K9l K9r K14 K15 K24 K33) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV38l HV38r K29l K29r K31 K32 K33 K34) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22 K23 K24 K34) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u8x2_of_KWord2a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K6 K15 K23 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22 K31) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K14 K22 K31) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNSRBP.
