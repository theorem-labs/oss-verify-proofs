(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_brcA_u LibSegBs_brcB_u LibSegBs_brcC_u LibSegBs_brcD_u LibSegBs_brcE_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRCP.
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
Module PbrcA := LibSegBs_brcA_u.
Definition KS_brcA : list nat := Eval vm_compute in (BG.kept_list 52 PbrcA.regs0 PbrcA.regs_out0).
Lemma KS_brcA_ok : BG.kept_ok 52 PbrcA.regs0 PbrcA.regs_out0 KS_brcA = true. Proof. vm_compute. reflexivity. Qed.
Lemma brcA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 33%nat) + 432) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) ->
  140735332483232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 140735332483232 <= (V 33%nat) <= 140737488354624 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 704 <= ((V 2%nat) - 160)) -> L5.writable RSEGS M (V 33%nat) 416 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 16) -> ~ (((V 33%nat) + 24) <= bv_unsigned a < ((V 33%nat) + 24) + 16) -> ~ (((V 33%nat) + 104) <= bv_unsigned a < ((V 33%nat) + 104) + 136) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 16) -> ~ (((V 33%nat) + 24) <= i < ((V 33%nat) + 24) + 16) -> ~ (((V 33%nat) + 104) <= i < ((V 33%nat) + 104) + 136) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36410 M) (st fx' R' 0x81bdc M')
        /\ (forall x, In x KS_brcA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 222804
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 104)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 152)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 432)
        /\ L5KA.zeros_at M' ((V 33%nat) + 160) 80
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 136) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 128) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 120) 6
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 112) 4098
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 144) ((V 33%nat) + 40)
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 140) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 32) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 24) 726984
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 152) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 104) 727024
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 222616
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 222304
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 12) 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 10) 0
        /\ (L5.u8_at RSEGS M' ((V 33%nat) + 8) 1 /\ L5.u8_at RSEGS M' (((V 33%nat) + 8) + 1) 0)
        /\ L5.u64_at RSEGS M' (V 33%nat) 726752
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros Rg2 Rg33 Rg34 Rr2 Rr10 Rr11 Rr12 Bd2 Al2 Wr Bd33 Al33 Sp Wr2 Ic.
  unfold aligned in *.
  (* the start environment: variable 2 is the caller's V 2, the other registers come from R, variables above 31 from V *)
  pose (Ein := {| ev := fun j => if (j =? 2)%nat then Z_to_bv 64 (V 2%nat)
                                  else ev (BG.E_R R (fun j0 => Z_to_bv 64 (V j0)) (fun _ => [])) j;
                  eb := fun _ => [] |}).
  pose (Vin := fun j : nat => if (j =? 2)%nat then V 2%nat else if (j =? 33)%nat then V 33%nat else if (j =? 34)%nat then V 34%nat else bv_unsigned (ev Ein j)).
  assert (Uin : forall j, bv_unsigned (ev Ein j) = Vin j).
  { intros j. unfold Vin.
    destruct (Nat.eqb_spec j 2) as [->|_]; [unfold Ein; cbn [ev Nat.eqb]; apply BG.unsigned_lit; exact Rg2|].
    destruct (Nat.eqb_spec j 33) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 33) by lia; apply BG.unsigned_lit; exact Rg33|].
    destruct (Nat.eqb_spec j 34) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 34) by lia; apply BG.unsigned_lit; exact Rg34|].
    reflexivity. }
  (* the segment's three preconditions: registers, known facts, facts on the env's byte buffers *)
  assert (RK : regs_ok Ein PbrcA.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. unfold PbrcA.regs0. cbn [tl BG.slots]. repeat split. all: slotP Uin. }
  assert (KK : know_ok RSEGS Ein M PbrcA.kn0).
  { unfold know_ok, PbrcA.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    all: lazymatch goal with
      | |- kentry_ok _ _ _ (KRange (EVar ?n) _ _) =>
          apply (L5K.kentry_KRange _ _ _ _ _ _ (V n)); [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | lia]
      | |- kentry_ok _ _ _ (KAlign (EVar ?n) _) =>
          apply (L5K.kentry_KAlign _ _ _ _ _ (V n)); [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | lia | lia]
      | |- kentry_ok _ _ _ (KWr {| a_base := EVar ?n; a_off := _ |} (ELit ?k)) =>
          apply (L5K.kentry_KWr _ _ _ _ _ _ (V n) k);
            [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | reflexivity | lia | lia | lia | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
      | |- kentry_ok _ _ _ (KDisj {| a_base := ?b1; a_off := _ |} (ELit ?k1) {| a_base := ?b2; a_off := _ |} (ELit ?k2)) =>
          let a1 := (let b := b1 in lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in let a2 := (let b := b2 in lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in
          apply (L5K.kentry_KDisj _ _ _ _ _ _ _ _ _ a1 k1 a2 k2);
            [first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])] | reflexivity | first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])] | reflexivity | lia]
      | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | assumption]
      | |- kentry_ok _ _ _ (KWord {| a_base := EVar ?n; a_off := _ |} 8 _) =>
          (eapply (L5K.kentry_KWord8 _ _ _ _ _ _ (V n));
             [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | idtac | lia | lia | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]);
          first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])]
      | |- kentry_ok _ _ _ (KWord {| a_base := EVar ?n; a_off := _ |} 4 _) =>
          (eapply (L5K.kentry_KWord4 _ _ _ _ _ _ (V n));
             [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | idtac | lia | lia | match goal with Q : L5.u32_at _ _ _ _ |- _ => exactA Q end]);
          first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])]
      end. }
  assert (BK : SGP.bfacts_ok PbrcA.BR Ein) by (unfold SGP.bfacts_ok, PbrcA.BR; apply Forall_nil).
  (* run the segment *)
  destruct (PbrcA.seg_sound_ax fx Ein R M RK KK BK)
    as (fx' & Eout & R' & M' & k & ps & Pick & Agr & Run & Rout & X0 & Rgn & Frame & Cells & Grow).
  vm_compute in Pick. apply L5K.nth_error_single in Pick. subst ps.
  cbn [SR.ps_pc SR.ps_regs SR.ps_cells] in Run, Rout, Cells.
  exists fx', R', M'.
  split; [exact Grow|].
  (* the frame: a byte outside the written regions keeps its value *)
  match goal with |- ?Fr /\ _ => assert (KeepA : Fr) end.
  { intros x; intros. apply Frame. unfold PbrcA.F0.
    repeat lazymatch goal with
      | |- SGP.outside _ [] _ => apply L5K.outside_nil_e
      | |- SGP.outside _ ((?b, _, ELit ?len) :: _) _ =>
          let a := (lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in
          apply (L5K.outside_cons_e _ _ _ _ _ _ a len); [first [reflexivity | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ]] | reflexivity | lia | ]
      end. }
  split; [exact KeepA|].
  split; [intros i Ri; intros; apply KeepA; rewrite (BG.unsigned_lit i Ri); assumption|].
  split; [exact Run|].
  split; [intros x Hx; exact (BG.kept_regs Ein Eout R R' PbrcA.regs0 PbrcA.regs_out0 52 KS_brcA KS_brcA_ok RK Agr Rout x Hx)|].
  (* every remaining conjunct is an output register or a cell the segment wrote *)
  repeat split.
  all: lazymatch goal with
    | |- getr _ (Z_to_bv 5 (Z.of_nat ?i)) = Z_to_bv 64 _ =>
        let G := fresh "G" in
        pose proof (Rout i _ ltac:(simpl; repeat (first [left; reflexivity | right]))) as [_ G]; rewrite G; clear G;
        eapply word_of_zpoly;
          [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity]
          | cbn [L5KA.zpolyA]; unfold Vin; cbv beta iota zeta delta [Nat.eqb]; zp_norm; f_equal;
            first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia] ]
    | |- L5.u8_at _ _ (?F ?n + ?o + 1) _ =>
        (* the high byte of a two-byte cell at V n + o *)
        eapply proj2, (u8x2_of_KWord2a Eout M' (EVar n) o _ (F n) _ (F n + o));
          [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
          | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | reflexivity | reflexivity ]
    | |- L5.u8_at _ _ (?F ?n + ?o) _ =>
        first
          [ eapply (u8_of_KWord1a Eout M' (EVar n) o _ (F n));
              [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
              | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | lia ]
          | (* the low byte of a two-byte cell *)
            eapply proj1, (u8x2_of_KWord2a Eout M' (EVar n) o _ (F n) _ (F n + o));
              [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
              | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | reflexivity | reflexivity ] ]
    | |- ?G =>
        let addr := lazymatch G with
          | L5KA.zeros_at _ ?a _ => a | L5.u64_at _ _ ?a _ => a | L5.u32_at _ _ ?a _ => a | L5.u8_at _ _ ?a _ => a end in
        let av := lazymatch addr with ?x + _ => x | ?x - _ => x | _ => addr end in
        let bn := lazymatch av with _ ?n => n end in
        let off := lazymatch addr with _ + ?o => o | _ - ?o => let o' := eval vm_compute in (Z.opp o) in o' | _ => constr:(0) end in
        lazymatch G with
        | L5KA.zeros_at _ _ _ => eapply (zeros_of_KZeroa Eout M' (EVar bn) off _ av)
        | L5.u64_at _ _ _ _ => eapply (u64_of_KWord8a Eout M' (EVar bn) off _ av)
        | L5.u32_at _ _ _ _ => eapply (u32_of_KWord4a Eout M' (EVar bn) off _ av)
        | L5.u8_at _ _ _ _ => eapply (u8_of_KWord1a Eout M' (EVar bn) off _ av)
        end;
        [ apply Cells; simpl; repeat (first [left; reflexivity | right])
        | (lazymatch goal with
           | |- bv_unsigned (edenot _ (ELit _)) = _ => reflexivity
           | |- bv_unsigned _ = _ => eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ]
           | |- _ => lia end) .. ]
    end.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrcB := LibSegBs_brcB_u.
Definition KS_brcB : list nat := Eval vm_compute in (BG.kept_list 52 PbrcB.regs0 PbrcB.regs_out0).
Lemma KS_brcB_ok : BG.kept_ok 52 PbrcB.regs0 PbrcB.regs_out0 KS_brcB = true. Proof. vm_compute. reflexivity. Qed.
Lemma brcB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 104) ->
  140735332483232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 140735332483232 <= (V 33%nat) <= 140737488354624 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 704 <= ((V 2%nat) - 160)) -> L5.writable RSEGS M (V 33%nat) 416 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 24) <= bv_unsigned a < ((V 33%nat) + 24) + 8) -> ~ (((V 33%nat) + 40) <= bv_unsigned a < ((V 33%nat) + 40) + 8) -> ~ (((V 33%nat) + 104) <= bv_unsigned a < ((V 33%nat) + 104) + 8) -> ~ (((V 33%nat) + 240) <= bv_unsigned a < ((V 33%nat) + 240) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 24) <= i < ((V 33%nat) + 24) + 8) -> ~ (((V 33%nat) + 40) <= i < ((V 33%nat) + 40) + 8) -> ~ (((V 33%nat) + 104) <= i < ((V 33%nat) + 104) + 8) -> ~ (((V 33%nat) + 240) <= i < ((V 33%nat) + 240) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36654 M) (st fx' R' 0x81bdc M')
        /\ (forall x, In x KS_brcB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 222864
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 740424
        /\ getr R' (reg 12) = Z_to_bv 64 726912
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 40) 740424
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 24) 726872
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 104) 726912
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 248) 18446744073709551615
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 240) 0).
Proof.
  intros Rg2 Rg33 Rr2 Rr8 Rr9 Bd2 Al2 Wr Bd33 Al33 Sp Wr2 Ic.
  unfold aligned in *.
  (* the start environment: variable 2 is the caller's V 2, the other registers come from R, variables above 31 from V *)
  pose (Ein := {| ev := fun j => if (j =? 2)%nat then Z_to_bv 64 (V 2%nat)
                                  else ev (BG.E_R R (fun j0 => Z_to_bv 64 (V j0)) (fun _ => [])) j;
                  eb := fun _ => [] |}).
  pose (Vin := fun j : nat => if (j =? 2)%nat then V 2%nat else if (j =? 33)%nat then V 33%nat else bv_unsigned (ev Ein j)).
  assert (Uin : forall j, bv_unsigned (ev Ein j) = Vin j).
  { intros j. unfold Vin.
    destruct (Nat.eqb_spec j 2) as [->|_]; [unfold Ein; cbn [ev Nat.eqb]; apply BG.unsigned_lit; exact Rg2|].
    destruct (Nat.eqb_spec j 33) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 33) by lia; apply BG.unsigned_lit; exact Rg33|].
    reflexivity. }
  (* the segment's three preconditions: registers, known facts, facts on the env's byte buffers *)
  assert (RK : regs_ok Ein PbrcB.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. unfold PbrcB.regs0. cbn [tl BG.slots]. repeat split. all: slotP Uin. }
  assert (KK : know_ok RSEGS Ein M PbrcB.kn0).
  { unfold know_ok, PbrcB.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    all: lazymatch goal with
      | |- kentry_ok _ _ _ (KRange (EVar ?n) _ _) =>
          apply (L5K.kentry_KRange _ _ _ _ _ _ (V n)); [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | lia]
      | |- kentry_ok _ _ _ (KAlign (EVar ?n) _) =>
          apply (L5K.kentry_KAlign _ _ _ _ _ (V n)); [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | lia | lia]
      | |- kentry_ok _ _ _ (KWr {| a_base := EVar ?n; a_off := _ |} (ELit ?k)) =>
          apply (L5K.kentry_KWr _ _ _ _ _ _ (V n) k);
            [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | reflexivity | lia | lia | lia | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
      | |- kentry_ok _ _ _ (KDisj {| a_base := ?b1; a_off := _ |} (ELit ?k1) {| a_base := ?b2; a_off := _ |} (ELit ?k2)) =>
          let a1 := (let b := b1 in lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in let a2 := (let b := b2 in lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in
          apply (L5K.kentry_KDisj _ _ _ _ _ _ _ _ _ a1 k1 a2 k2);
            [first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])] | reflexivity | first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])] | reflexivity | lia]
      | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | assumption]
      | |- kentry_ok _ _ _ (KWord {| a_base := EVar ?n; a_off := _ |} 8 _) =>
          (eapply (L5K.kentry_KWord8 _ _ _ _ _ _ (V n));
             [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | idtac | lia | lia | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]);
          first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])]
      | |- kentry_ok _ _ _ (KWord {| a_base := EVar ?n; a_off := _ |} 4 _) =>
          (eapply (L5K.kentry_KWord4 _ _ _ _ _ _ (V n));
             [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | idtac | lia | lia | match goal with Q : L5.u32_at _ _ _ _ |- _ => exactA Q end]);
          first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])]
      end. }
  assert (BK : SGP.bfacts_ok PbrcB.BR Ein) by (unfold SGP.bfacts_ok, PbrcB.BR; apply Forall_nil).
  (* run the segment *)
  destruct (PbrcB.seg_sound_ax fx Ein R M RK KK BK)
    as (fx' & Eout & R' & M' & k & ps & Pick & Agr & Run & Rout & X0 & Rgn & Frame & Cells & Grow).
  vm_compute in Pick. apply L5K.nth_error_single in Pick. subst ps.
  cbn [SR.ps_pc SR.ps_regs SR.ps_cells] in Run, Rout, Cells.
  exists fx', R', M'.
  split; [exact Grow|].
  (* the frame: a byte outside the written regions keeps its value *)
  match goal with |- ?Fr /\ _ => assert (KeepA : Fr) end.
  { intros x; intros. apply Frame. unfold PbrcB.F0.
    repeat lazymatch goal with
      | |- SGP.outside _ [] _ => apply L5K.outside_nil_e
      | |- SGP.outside _ ((?b, _, ELit ?len) :: _) _ =>
          let a := (lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in
          apply (L5K.outside_cons_e _ _ _ _ _ _ a len); [first [reflexivity | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ]] | reflexivity | lia | ]
      end. }
  split; [exact KeepA|].
  split; [intros i Ri; intros; apply KeepA; rewrite (BG.unsigned_lit i Ri); assumption|].
  split; [exact Run|].
  split; [intros x Hx; exact (BG.kept_regs Ein Eout R R' PbrcB.regs0 PbrcB.regs_out0 52 KS_brcB KS_brcB_ok RK Agr Rout x Hx)|].
  (* every remaining conjunct is an output register or a cell the segment wrote *)
  repeat split.
  all: lazymatch goal with
    | |- getr _ (Z_to_bv 5 (Z.of_nat ?i)) = Z_to_bv 64 _ =>
        let G := fresh "G" in
        pose proof (Rout i _ ltac:(simpl; repeat (first [left; reflexivity | right]))) as [_ G]; rewrite G; clear G;
        eapply word_of_zpoly;
          [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity]
          | cbn [L5KA.zpolyA]; unfold Vin; cbv beta iota zeta delta [Nat.eqb]; zp_norm; f_equal;
            first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia] ]
    | |- L5.u8_at _ _ (?F ?n + ?o + 1) _ =>
        (* the high byte of a two-byte cell at V n + o *)
        eapply proj2, (u8x2_of_KWord2a Eout M' (EVar n) o _ (F n) _ (F n + o));
          [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
          | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | reflexivity | reflexivity ]
    | |- L5.u8_at _ _ (?F ?n + ?o) _ =>
        first
          [ eapply (u8_of_KWord1a Eout M' (EVar n) o _ (F n));
              [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
              | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | lia ]
          | (* the low byte of a two-byte cell *)
            eapply proj1, (u8x2_of_KWord2a Eout M' (EVar n) o _ (F n) _ (F n + o));
              [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
              | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | reflexivity | reflexivity ] ]
    | |- ?G =>
        let addr := lazymatch G with
          | L5KA.zeros_at _ ?a _ => a | L5.u64_at _ _ ?a _ => a | L5.u32_at _ _ ?a _ => a | L5.u8_at _ _ ?a _ => a end in
        let av := lazymatch addr with ?x + _ => x | ?x - _ => x | _ => addr end in
        let bn := lazymatch av with _ ?n => n end in
        let off := lazymatch addr with _ + ?o => o | _ - ?o => let o' := eval vm_compute in (Z.opp o) in o' | _ => constr:(0) end in
        lazymatch G with
        | L5KA.zeros_at _ _ _ => eapply (zeros_of_KZeroa Eout M' (EVar bn) off _ av)
        | L5.u64_at _ _ _ _ => eapply (u64_of_KWord8a Eout M' (EVar bn) off _ av)
        | L5.u32_at _ _ _ _ => eapply (u32_of_KWord4a Eout M' (EVar bn) off _ av)
        | L5.u8_at _ _ _ _ => eapply (u8_of_KWord1a Eout M' (EVar bn) off _ av)
        end;
        [ apply Cells; simpl; repeat (first [left; reflexivity | right])
        | (lazymatch goal with
           | |- bv_unsigned (edenot _ (ELit _)) = _ => reflexivity
           | |- bv_unsigned _ = _ => eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ]
           | |- _ => lia end) .. ]
    end.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrcC := LibSegBs_brcC_u.
Definition KS_brcC : list nat := Eval vm_compute in (BG.kept_list 52 PbrcC.regs0 PbrcC.regs_out0).
Lemma KS_brcC_ok : BG.kept_ok 52 PbrcC.regs0 PbrcC.regs_out0 KS_brcC = true. Proof. vm_compute. reflexivity. Qed.
Lemma brcC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 104) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 432) ->
  140735332483232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 140735332483232 <= (V 33%nat) <= 140737488354624 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 704 <= ((V 2%nat) - 160)) -> L5.writable RSEGS M (V 33%nat) 416 -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) 222616 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 33%nat) + 432) 740792 ->
  L5.u64_at RSEGS M ((V 33%nat) + 592) ((V 33%nat) + 448) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 40) <= bv_unsigned a < ((V 33%nat) + 40) + 8) -> ~ (((V 33%nat) + 56) <= bv_unsigned a < ((V 33%nat) + 56) + 48) -> ~ (((V 33%nat) + 256) <= bv_unsigned a < ((V 33%nat) + 256) + 56) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 40) <= i < ((V 33%nat) + 40) + 8) -> ~ (((V 33%nat) + 56) <= i < ((V 33%nat) + 56) + 48) -> ~ (((V 33%nat) + 256) <= i < ((V 33%nat) + 256) + 56) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36690 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_brcC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 222680
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 16384
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 552)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 304) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 296) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 288) 16384
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 280) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 272) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 264) ((V 33%nat) + 448)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 256) ((V 33%nat) + 432)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 40) 727080
        /\ L5KA.zeros_at M' ((V 33%nat) + 56) 48).
Proof.
  intros Rg2 Rg33 Rr2 Rr8 Rr9 Rr18 Bd2 Al2 Wr Bd33 Al33 Sp Wr2 Ic Mq Mq2 Mq3 Mq4 Mq5.
  unfold aligned in *.
  (* the start environment: variable 2 is the caller's V 2, the other registers come from R, variables above 31 from V *)
  pose (Ein := {| ev := fun j => if (j =? 2)%nat then Z_to_bv 64 (V 2%nat)
                                  else ev (BG.E_R R (fun j0 => Z_to_bv 64 (V j0)) (fun _ => [])) j;
                  eb := fun _ => [] |}).
  pose (Vin := fun j : nat => if (j =? 2)%nat then V 2%nat else if (j =? 33)%nat then V 33%nat else bv_unsigned (ev Ein j)).
  assert (Uin : forall j, bv_unsigned (ev Ein j) = Vin j).
  { intros j. unfold Vin.
    destruct (Nat.eqb_spec j 2) as [->|_]; [unfold Ein; cbn [ev Nat.eqb]; apply BG.unsigned_lit; exact Rg2|].
    destruct (Nat.eqb_spec j 33) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 33) by lia; apply BG.unsigned_lit; exact Rg33|].
    reflexivity. }
  (* the segment's three preconditions: registers, known facts, facts on the env's byte buffers *)
  assert (RK : regs_ok Ein PbrcC.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. unfold PbrcC.regs0. cbn [tl BG.slots]. repeat split. all: slotP Uin. }
  assert (KK : know_ok RSEGS Ein M PbrcC.kn0).
  { unfold know_ok, PbrcC.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    all: lazymatch goal with
      | |- kentry_ok _ _ _ (KRange (EVar ?n) _ _) =>
          apply (L5K.kentry_KRange _ _ _ _ _ _ (V n)); [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | lia]
      | |- kentry_ok _ _ _ (KAlign (EVar ?n) _) =>
          apply (L5K.kentry_KAlign _ _ _ _ _ (V n)); [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | lia | lia]
      | |- kentry_ok _ _ _ (KWr {| a_base := EVar ?n; a_off := _ |} (ELit ?k)) =>
          apply (L5K.kentry_KWr _ _ _ _ _ _ (V n) k);
            [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | reflexivity | lia | lia | lia | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
      | |- kentry_ok _ _ _ (KDisj {| a_base := ?b1; a_off := _ |} (ELit ?k1) {| a_base := ?b2; a_off := _ |} (ELit ?k2)) =>
          let a1 := (let b := b1 in lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in let a2 := (let b := b2 in lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in
          apply (L5K.kentry_KDisj _ _ _ _ _ _ _ _ _ a1 k1 a2 k2);
            [first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])] | reflexivity | first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])] | reflexivity | lia]
      | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | assumption]
      | |- kentry_ok _ _ _ (KWord {| a_base := EVar ?n; a_off := _ |} 8 _) =>
          (eapply (L5K.kentry_KWord8 _ _ _ _ _ _ (V n));
             [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | idtac | lia | lia | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]);
          first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])]
      | |- kentry_ok _ _ _ (KWord {| a_base := EVar ?n; a_off := _ |} 4 _) =>
          (eapply (L5K.kentry_KWord4 _ _ _ _ _ _ (V n));
             [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | idtac | lia | lia | match goal with Q : L5.u32_at _ _ _ _ |- _ => exactA Q end]);
          first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])]
      end. }
  assert (BK : SGP.bfacts_ok PbrcC.BR Ein) by (unfold SGP.bfacts_ok, PbrcC.BR; apply Forall_nil).
  (* run the segment *)
  destruct (PbrcC.seg_sound_ax fx Ein R M RK KK BK)
    as (fx' & Eout & R' & M' & k & ps & Pick & Agr & Run & Rout & X0 & Rgn & Frame & Cells & Grow).
  vm_compute in Pick. apply L5K.nth_error_single in Pick. subst ps.
  cbn [SR.ps_pc SR.ps_regs SR.ps_cells] in Run, Rout, Cells.
  exists fx', R', M'.
  split; [exact Grow|].
  (* the frame: a byte outside the written regions keeps its value *)
  match goal with |- ?Fr /\ _ => assert (KeepA : Fr) end.
  { intros x; intros. apply Frame. unfold PbrcC.F0.
    repeat lazymatch goal with
      | |- SGP.outside _ [] _ => apply L5K.outside_nil_e
      | |- SGP.outside _ ((?b, _, ELit ?len) :: _) _ =>
          let a := (lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in
          apply (L5K.outside_cons_e _ _ _ _ _ _ a len); [first [reflexivity | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ]] | reflexivity | lia | ]
      end. }
  split; [exact KeepA|].
  split; [intros i Ri; intros; apply KeepA; rewrite (BG.unsigned_lit i Ri); assumption|].
  split; [exact Run|].
  split; [intros x Hx; exact (BG.kept_regs Ein Eout R R' PbrcC.regs0 PbrcC.regs_out0 52 KS_brcC KS_brcC_ok RK Agr Rout x Hx)|].
  (* every remaining conjunct is an output register or a cell the segment wrote *)
  repeat split.
  all: lazymatch goal with
    | |- getr _ (Z_to_bv 5 (Z.of_nat ?i)) = Z_to_bv 64 _ =>
        let G := fresh "G" in
        pose proof (Rout i _ ltac:(simpl; repeat (first [left; reflexivity | right]))) as [_ G]; rewrite G; clear G;
        eapply word_of_zpoly;
          [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity]
          | cbn [L5KA.zpolyA]; unfold Vin; cbv beta iota zeta delta [Nat.eqb]; zp_norm; f_equal;
            first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia] ]
    | |- L5.u8_at _ _ (?F ?n + ?o + 1) _ =>
        (* the high byte of a two-byte cell at V n + o *)
        eapply proj2, (u8x2_of_KWord2a Eout M' (EVar n) o _ (F n) _ (F n + o));
          [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
          | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | reflexivity | reflexivity ]
    | |- L5.u8_at _ _ (?F ?n + ?o) _ =>
        first
          [ eapply (u8_of_KWord1a Eout M' (EVar n) o _ (F n));
              [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
              | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | lia ]
          | (* the low byte of a two-byte cell *)
            eapply proj1, (u8x2_of_KWord2a Eout M' (EVar n) o _ (F n) _ (F n + o));
              [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
              | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | reflexivity | reflexivity ] ]
    | |- ?G =>
        let addr := lazymatch G with
          | L5KA.zeros_at _ ?a _ => a | L5.u64_at _ _ ?a _ => a | L5.u32_at _ _ ?a _ => a | L5.u8_at _ _ ?a _ => a end in
        let av := lazymatch addr with ?x + _ => x | ?x - _ => x | _ => addr end in
        let bn := lazymatch av with _ ?n => n end in
        let off := lazymatch addr with _ + ?o => o | _ - ?o => let o' := eval vm_compute in (Z.opp o) in o' | _ => constr:(0) end in
        lazymatch G with
        | L5KA.zeros_at _ _ _ => eapply (zeros_of_KZeroa Eout M' (EVar bn) off _ av)
        | L5.u64_at _ _ _ _ => eapply (u64_of_KWord8a Eout M' (EVar bn) off _ av)
        | L5.u32_at _ _ _ _ => eapply (u32_of_KWord4a Eout M' (EVar bn) off _ av)
        | L5.u8_at _ _ _ _ => eapply (u8_of_KWord1a Eout M' (EVar bn) off _ av)
        end;
        [ apply Cells; simpl; repeat (first [left; reflexivity | right])
        | (lazymatch goal with
           | |- bv_unsigned (edenot _ (ELit _)) = _ => reflexivity
           | |- bv_unsigned _ = _ => eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ]
           | |- _ => lia end) .. ]
    end.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrcD := LibSegBs_brcD_u.
Definition KS_brcD : list nat := Eval vm_compute in (BG.kept_list 52 PbrcD.regs0 PbrcD.regs_out0).
Lemma KS_brcD_ok : BG.kept_ok 52 PbrcD.regs0 PbrcD.regs_out0 KS_brcD = true. Proof. vm_compute. reflexivity. Qed.
Lemma brcD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 552) ->
  140735332483232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 140735332483232 <= (V 33%nat) <= 140737488354624 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 33%nat) \/ (V 33%nat) + 704 <= ((V 2%nat) - 192)) -> L5.writable RSEGS M (V 33%nat) 416 -> 140735332483232 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 34%nat) + 24 <= (V 33%nat) \/ (V 33%nat) + 704 <= (V 34%nat)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) 222304 -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 34%nat) ->
  L5.u64_at RSEGS M (V 34%nat) 726624 -> L5.u32_at RSEGS M ((V 34%nat) + 16) 1024 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 16) -> ~ (((V 2%nat) - 168) <= bv_unsigned a < ((V 2%nat) - 168) + 24) -> ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 68) -> ~ (((V 33%nat) + 280) <= bv_unsigned a < ((V 33%nat) + 280) + 8) -> ~ (((V 33%nat) + 296) <= bv_unsigned a < ((V 33%nat) + 296) + 8) -> ~ (((V 33%nat) + 312) <= bv_unsigned a < ((V 33%nat) + 312) + 4) -> ~ (((V 33%nat) + 320) <= bv_unsigned a < ((V 33%nat) + 320) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 16) -> ~ (((V 2%nat) - 168) <= i < ((V 2%nat) - 168) + 24) -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 68) -> ~ (((V 33%nat) + 280) <= i < ((V 33%nat) + 280) + 8) -> ~ (((V 33%nat) + 296) <= i < ((V 33%nat) + 296) + 8) -> ~ (((V 33%nat) + 312) <= i < ((V 33%nat) + 312) + 4) -> ~ (((V 33%nat) + 320) <= i < ((V 33%nat) + 320) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x365d8 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_brcD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223860
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 1
        /\ getr R' (reg 9) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 40
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 461168601842738791
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 56)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 223148
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 33%nat) + 320)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 222412
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 56) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 408) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 400) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 392) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 384) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 376) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 368) 0
        /\ L5KA.zeros_at M' ((V 33%nat) + 320) 48
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 312) 1024
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 296) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 280) (V 35%nat)).
Proof.
  intros Rg2 Rg33 Rg34 Rg35 Rr2 Rr8 Rr9 Rr10 Rr18 Bd2 Al2 Wr Bd33 Al33 Sp Wr2 Bd34 Al34 Sp2 Sp3 Ic Mq Mq2 Mq3 Mq4 Mq5 Md.
  unfold aligned in *.
  (* the start environment: variable 2 is the caller's V 2, the other registers come from R, variables above 31 from V *)
  pose (Ein := {| ev := fun j => if (j =? 2)%nat then Z_to_bv 64 (V 2%nat)
                                  else ev (BG.E_R R (fun j0 => Z_to_bv 64 (V j0)) (fun _ => [])) j;
                  eb := fun _ => [] |}).
  pose (Vin := fun j : nat => if (j =? 2)%nat then V 2%nat else if (j =? 33)%nat then V 33%nat else if (j =? 34)%nat then V 34%nat else if (j =? 35)%nat then V 35%nat else bv_unsigned (ev Ein j)).
  assert (Uin : forall j, bv_unsigned (ev Ein j) = Vin j).
  { intros j. unfold Vin.
    destruct (Nat.eqb_spec j 2) as [->|_]; [unfold Ein; cbn [ev Nat.eqb]; apply BG.unsigned_lit; exact Rg2|].
    destruct (Nat.eqb_spec j 33) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 33) by lia; apply BG.unsigned_lit; exact Rg33|].
    destruct (Nat.eqb_spec j 34) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 34) by lia; apply BG.unsigned_lit; exact Rg34|].
    destruct (Nat.eqb_spec j 35) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 35) by lia; apply BG.unsigned_lit; exact Rg35|].
    reflexivity. }
  (* the segment's three preconditions: registers, known facts, facts on the env's byte buffers *)
  assert (RK : regs_ok Ein PbrcD.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. unfold PbrcD.regs0. cbn [tl BG.slots]. repeat split. all: slotP Uin. }
  assert (KK : know_ok RSEGS Ein M PbrcD.kn0).
  { unfold know_ok, PbrcD.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    all: lazymatch goal with
      | |- kentry_ok _ _ _ (KRange (EVar ?n) _ _) =>
          apply (L5K.kentry_KRange _ _ _ _ _ _ (V n)); [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | lia]
      | |- kentry_ok _ _ _ (KAlign (EVar ?n) _) =>
          apply (L5K.kentry_KAlign _ _ _ _ _ (V n)); [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | lia | lia]
      | |- kentry_ok _ _ _ (KWr {| a_base := EVar ?n; a_off := _ |} (ELit ?k)) =>
          apply (L5K.kentry_KWr _ _ _ _ _ _ (V n) k);
            [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | reflexivity | lia | lia | lia | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
      | |- kentry_ok _ _ _ (KDisj {| a_base := ?b1; a_off := _ |} (ELit ?k1) {| a_base := ?b2; a_off := _ |} (ELit ?k2)) =>
          let a1 := (let b := b1 in lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in let a2 := (let b := b2 in lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in
          apply (L5K.kentry_KDisj _ _ _ _ _ _ _ _ _ a1 k1 a2 k2);
            [first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])] | reflexivity | first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])] | reflexivity | lia]
      | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | assumption]
      | |- kentry_ok _ _ _ (KWord {| a_base := EVar ?n; a_off := _ |} 8 _) =>
          (eapply (L5K.kentry_KWord8 _ _ _ _ _ _ (V n));
             [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | idtac | lia | lia | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]);
          first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])]
      | |- kentry_ok _ _ _ (KWord {| a_base := EVar ?n; a_off := _ |} 4 _) =>
          (eapply (L5K.kentry_KWord4 _ _ _ _ _ _ (V n));
             [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | idtac | lia | lia | match goal with Q : L5.u32_at _ _ _ _ |- _ => exactA Q end]);
          first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])]
      end. }
  assert (BK : SGP.bfacts_ok PbrcD.BR Ein) by (unfold SGP.bfacts_ok, PbrcD.BR; apply Forall_nil).
  (* run the segment *)
  destruct (PbrcD.seg_sound_ax fx Ein R M RK KK BK)
    as (fx' & Eout & R' & M' & k & ps & Pick & Agr & Run & Rout & X0 & Rgn & Frame & Cells & Grow).
  vm_compute in Pick. apply L5K.nth_error_single in Pick. subst ps.
  cbn [SR.ps_pc SR.ps_regs SR.ps_cells] in Run, Rout, Cells.
  exists fx', R', M'.
  split; [exact Grow|].
  (* the frame: a byte outside the written regions keeps its value *)
  match goal with |- ?Fr /\ _ => assert (KeepA : Fr) end.
  { intros x; intros. apply Frame. unfold PbrcD.F0.
    repeat lazymatch goal with
      | |- SGP.outside _ [] _ => apply L5K.outside_nil_e
      | |- SGP.outside _ ((?b, _, ELit ?len) :: _) _ =>
          let a := (lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in
          apply (L5K.outside_cons_e _ _ _ _ _ _ a len); [first [reflexivity | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ]] | reflexivity | lia | ]
      end. }
  split; [exact KeepA|].
  split; [intros i Ri; intros; apply KeepA; rewrite (BG.unsigned_lit i Ri); assumption|].
  split; [exact Run|].
  split; [intros x Hx; exact (BG.kept_regs Ein Eout R R' PbrcD.regs0 PbrcD.regs_out0 52 KS_brcD KS_brcD_ok RK Agr Rout x Hx)|].
  (* every remaining conjunct is an output register or a cell the segment wrote *)
  repeat split.
  all: lazymatch goal with
    | |- getr _ (Z_to_bv 5 (Z.of_nat ?i)) = Z_to_bv 64 _ =>
        let G := fresh "G" in
        pose proof (Rout i _ ltac:(simpl; repeat (first [left; reflexivity | right]))) as [_ G]; rewrite G; clear G;
        eapply word_of_zpoly;
          [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity]
          | cbn [L5KA.zpolyA]; unfold Vin; cbv beta iota zeta delta [Nat.eqb]; zp_norm; f_equal;
            first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia] ]
    | |- L5.u8_at _ _ (?F ?n + ?o + 1) _ =>
        (* the high byte of a two-byte cell at V n + o *)
        eapply proj2, (u8x2_of_KWord2a Eout M' (EVar n) o _ (F n) _ (F n + o));
          [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
          | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | reflexivity | reflexivity ]
    | |- L5.u8_at _ _ (?F ?n + ?o) _ =>
        first
          [ eapply (u8_of_KWord1a Eout M' (EVar n) o _ (F n));
              [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
              | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | lia ]
          | (* the low byte of a two-byte cell *)
            eapply proj1, (u8x2_of_KWord2a Eout M' (EVar n) o _ (F n) _ (F n + o));
              [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
              | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | reflexivity | reflexivity ] ]
    | |- ?G =>
        let addr := lazymatch G with
          | L5KA.zeros_at _ ?a _ => a | L5.u64_at _ _ ?a _ => a | L5.u32_at _ _ ?a _ => a | L5.u8_at _ _ ?a _ => a end in
        let av := lazymatch addr with ?x + _ => x | ?x - _ => x | _ => addr end in
        let bn := lazymatch av with _ ?n => n end in
        let off := lazymatch addr with _ + ?o => o | _ - ?o => let o' := eval vm_compute in (Z.opp o) in o' | _ => constr:(0) end in
        lazymatch G with
        | L5KA.zeros_at _ _ _ => eapply (zeros_of_KZeroa Eout M' (EVar bn) off _ av)
        | L5.u64_at _ _ _ _ => eapply (u64_of_KWord8a Eout M' (EVar bn) off _ av)
        | L5.u32_at _ _ _ _ => eapply (u32_of_KWord4a Eout M' (EVar bn) off _ av)
        | L5.u8_at _ _ _ _ => eapply (u8_of_KWord1a Eout M' (EVar bn) off _ av)
        end;
        [ apply Cells; simpl; repeat (first [left; reflexivity | right])
        | (lazymatch goal with
           | |- bv_unsigned (edenot _ (ELit _)) = _ => reflexivity
           | |- bv_unsigned _ = _ => eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ]
           | |- _ => lia end) .. ]
    end.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrcE := LibSegBs_brcE_u.
Definition KS_brcE : list nat := Eval vm_compute in (BG.kept_list 52 PbrcE.regs0 PbrcE.regs_out0).
Lemma KS_brcE_ok : BG.kept_ok 52 PbrcE.regs0 PbrcE.regs_out0 KS_brcE = true. Proof. vm_compute. reflexivity. Qed.
Lemma brcE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 1 -> getr R (reg 9) = Z_to_bv 64 0 -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 60) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 56) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 392) ->
  140735332483232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 140735332483232 <= (V 33%nat) <= 140737488354624 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 33%nat) \/ (V 33%nat) + 704 <= ((V 2%nat) - 192)) -> L5.writable RSEGS M (V 33%nat) 416 -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u32_at RSEGS M ((V 2%nat) - 56) 0 -> L5.u32_at RSEGS M ((V 2%nat) - 60) 0 ->
  L5.u32_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) 222412 -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 33%nat) + 16) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 33%nat) + 320) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 392) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 152) 223148 ->
  L5.u64_at RSEGS M ((V 2%nat) - 160) ((V 33%nat) + 392) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 2%nat) - 64) -> L5.u64_at RSEGS M ((V 2%nat) - 184) 223340 -> L5.u64_at RSEGS M ((V 2%nat) - 192) ((V 2%nat) - 144) ->
  L5.u64_at RSEGS M ((V 33%nat) + 392) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 400) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 408) 0 -> 4096 <= (V 36%nat) <= 140737488355288 ->
  aligned (V 36%nat) 16 -> L5.writable RSEGS M (V 36%nat) 40 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 40 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 40 <= (V 33%nat) \/ (V 33%nat) + 704 <= (V 36%nat)) ->
  ((V 36%nat) + 40 <= 65536 \/ 65536 + 689136 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 64) -> ~ (((V 33%nat) + 392) <= bv_unsigned a < ((V 33%nat) + 392) + 24) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 64) -> ~ (((V 33%nat) + 392) <= i < ((V 33%nat) + 392) + 24) -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36a74 M) (st fx' R' 0x36504 M')
        /\ (forall x, In x KS_brcE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 40
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 400) ((V 36%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 408) ((V 36%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 392) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 32) 0
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.u32_at RSEGS M' (V 36%nat) 0).
Proof.
  intros Rg2 Rg33 Rg36 Rg43 Rg44 Rg45 Rg46 Rg47 Rg48 Rr2 Rr8 Rr9 Rr10 Rr18 Rr19 Rr20 Bd2 Al2 Wr Bd33 Al33 Sp Wr2 Ic Mq Mq2 Mq3 Mq4 Mq5 Mq6 Md Md2 Md3 Mq7 Mq8 Mq9 Mq10 Mq11 Mq12 Mq13 Mq14 Mq15 Mq16 Mq17 Mq18 Mq19 Mq20 Bd36 Al36 Wr3 Sp2 Sp3 Sp4.
  unfold aligned in *.
  (* the start environment: variable 2 is the caller's V 2, the other registers come from R, variables above 31 from V *)
  pose (Ein := {| ev := fun j => if (j =? 2)%nat then Z_to_bv 64 (V 2%nat)
                                  else ev (BG.E_R R (fun j0 => Z_to_bv 64 (V j0)) (fun _ => [])) j;
                  eb := fun _ => [] |}).
  pose (Vin := fun j : nat => if (j =? 2)%nat then V 2%nat else if (j =? 33)%nat then V 33%nat else if (j =? 36)%nat then V 36%nat else if (j =? 43)%nat then V 43%nat else if (j =? 44)%nat then V 44%nat else if (j =? 45)%nat then V 45%nat else if (j =? 46)%nat then V 46%nat else if (j =? 47)%nat then V 47%nat else if (j =? 48)%nat then V 48%nat else bv_unsigned (ev Ein j)).
  assert (Uin : forall j, bv_unsigned (ev Ein j) = Vin j).
  { intros j. unfold Vin.
    destruct (Nat.eqb_spec j 2) as [->|_]; [unfold Ein; cbn [ev Nat.eqb]; apply BG.unsigned_lit; exact Rg2|].
    destruct (Nat.eqb_spec j 33) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 33) by lia; apply BG.unsigned_lit; exact Rg33|].
    destruct (Nat.eqb_spec j 36) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 36) by lia; apply BG.unsigned_lit; exact Rg36|].
    destruct (Nat.eqb_spec j 43) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 43) by lia; apply BG.unsigned_lit; exact Rg43|].
    destruct (Nat.eqb_spec j 44) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 44) by lia; apply BG.unsigned_lit; exact Rg44|].
    destruct (Nat.eqb_spec j 45) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 45) by lia; apply BG.unsigned_lit; exact Rg45|].
    destruct (Nat.eqb_spec j 46) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 46) by lia; apply BG.unsigned_lit; exact Rg46|].
    destruct (Nat.eqb_spec j 47) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 47) by lia; apply BG.unsigned_lit; exact Rg47|].
    destruct (Nat.eqb_spec j 48) as [->|_];
      [unfold Ein; cbn [ev Nat.eqb]; rewrite (BG.E_R_rest _ _ _ 48) by lia; apply BG.unsigned_lit; exact Rg48|].
    reflexivity. }
  (* the segment's three preconditions: registers, known facts, facts on the env's byte buffers *)
  assert (RK : regs_ok Ein PbrcE.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. unfold PbrcE.regs0. cbn [tl BG.slots]. repeat split. all: slotP Uin. }
  assert (KK : know_ok RSEGS Ein M PbrcE.kn0).
  { unfold know_ok, PbrcE.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    all: lazymatch goal with
      | |- kentry_ok _ _ _ (KRange (EVar ?n) _ _) =>
          apply (L5K.kentry_KRange _ _ _ _ _ _ (V n)); [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | lia]
      | |- kentry_ok _ _ _ (KAlign (EVar ?n) _) =>
          apply (L5K.kentry_KAlign _ _ _ _ _ (V n)); [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | lia | lia]
      | |- kentry_ok _ _ _ (KWr {| a_base := EVar ?n; a_off := _ |} (ELit ?k)) =>
          apply (L5K.kentry_KWr _ _ _ _ _ _ (V n) k);
            [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | reflexivity | lia | lia | lia | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
      | |- kentry_ok _ _ _ (KDisj {| a_base := ?b1; a_off := _ |} (ELit ?k1) {| a_base := ?b2; a_off := _ |} (ELit ?k2)) =>
          let a1 := (let b := b1 in lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in let a2 := (let b := b2 in lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in
          apply (L5K.kentry_KDisj _ _ _ _ _ _ _ _ _ a1 k1 a2 k2);
            [first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])] | reflexivity | first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])] | reflexivity | lia]
      | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | assumption]
      | |- kentry_ok _ _ _ (KWord {| a_base := EVar ?n; a_off := _ |} 8 _) =>
          (eapply (L5K.kentry_KWord8 _ _ _ _ _ _ (V n));
             [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | idtac | lia | lia | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]);
          first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])]
      | |- kentry_ok _ _ _ (KWord {| a_base := EVar ?n; a_off := _ |} 4 _) =>
          (eapply (L5K.kentry_KWord4 _ _ _ _ _ _ (V n));
             [evalEk Uin (cbv beta iota zeta delta [Nat.eqb]) | idtac | lia | lia | match goal with Q : L5.u32_at _ _ _ _ |- _ => exactA Q end]);
          first [reflexivity | evalEk Uin (cbv beta iota zeta delta [Nat.eqb])]
      end. }
  assert (BK : SGP.bfacts_ok PbrcE.BR Ein) by (unfold SGP.bfacts_ok, PbrcE.BR; apply Forall_nil).
  (* run the segment *)
  destruct (PbrcE.seg_sound_ax fx Ein R M RK KK BK)
    as (fx' & Eout & R' & M' & k & ps & Pick & Agr & Run & Rout & X0 & Rgn & Frame & Cells & Grow).
  vm_compute in Pick. apply L5K.nth_error_single in Pick. subst ps.
  cbn [SR.ps_pc SR.ps_regs SR.ps_cells] in Run, Rout, Cells.
  exists fx', R', M'.
  split; [exact Grow|].
  (* the frame: a byte outside the written regions keeps its value *)
  match goal with |- ?Fr /\ _ => assert (KeepA : Fr) end.
  { intros x; intros. apply Frame. unfold PbrcE.F0.
    repeat lazymatch goal with
      | |- SGP.outside _ [] _ => apply L5K.outside_nil_e
      | |- SGP.outside _ ((?b, _, ELit ?len) :: _) _ =>
          let a := (lazymatch b with EVar ?n => constr:(V n) | ELit ?z => z end) in
          apply (L5K.outside_cons_e _ _ _ _ _ _ a len); [first [reflexivity | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ]] | reflexivity | lia | ]
      end. }
  split; [exact KeepA|].
  split; [intros i Ri; intros; apply KeepA; rewrite (BG.unsigned_lit i Ri); assumption|].
  split; [exact Run|].
  split; [intros x Hx; exact (BG.kept_regs Ein Eout R R' PbrcE.regs0 PbrcE.regs_out0 52 KS_brcE KS_brcE_ok RK Agr Rout x Hx)|].
  (* every remaining conjunct is an output register or a cell the segment wrote *)
  repeat split.
  all: lazymatch goal with
    | |- getr _ (Z_to_bv 5 (Z.of_nat ?i)) = Z_to_bv 64 _ =>
        let G := fresh "G" in
        pose proof (Rout i _ ltac:(simpl; repeat (first [left; reflexivity | right]))) as [_ G]; rewrite G; clear G;
        eapply word_of_zpoly;
          [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity]
          | cbn [L5KA.zpolyA]; unfold Vin; cbv beta iota zeta delta [Nat.eqb]; zp_norm; f_equal;
            first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia] ]
    | |- L5.u8_at _ _ (?F ?n + ?o + 1) _ =>
        (* the high byte of a two-byte cell at V n + o *)
        eapply proj2, (u8x2_of_KWord2a Eout M' (EVar n) o _ (F n) _ (F n + o));
          [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
          | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | reflexivity | reflexivity ]
    | |- L5.u8_at _ _ (?F ?n + ?o) _ =>
        first
          [ eapply (u8_of_KWord1a Eout M' (EVar n) o _ (F n));
              [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
              | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | lia ]
          | (* the low byte of a two-byte cell *)
            eapply proj1, (u8x2_of_KWord2a Eout M' (EVar n) o _ (F n) _ (F n + o));
              [ apply Cells; solve [simpl; repeat (first [left; reflexivity | right])]
              | eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ] | reflexivity | lia | reflexivity | reflexivity ] ]
    | |- ?G =>
        let addr := lazymatch G with
          | L5KA.zeros_at _ ?a _ => a | L5.u64_at _ _ ?a _ => a | L5.u32_at _ _ ?a _ => a | L5.u8_at _ _ ?a _ => a end in
        let av := lazymatch addr with ?x + _ => x | ?x - _ => x | _ => addr end in
        let bn := lazymatch av with _ ?n => n end in
        let off := lazymatch addr with _ + ?o => o | _ - ?o => let o' := eval vm_compute in (Z.opp o) in o' | _ => constr:(0) end in
        lazymatch G with
        | L5KA.zeros_at _ _ _ => eapply (zeros_of_KZeroa Eout M' (EVar bn) off _ av)
        | L5.u64_at _ _ _ _ => eapply (u64_of_KWord8a Eout M' (EVar bn) off _ av)
        | L5.u32_at _ _ _ _ => eapply (u32_of_KWord4a Eout M' (EVar bn) off _ av)
        | L5.u8_at _ _ _ _ => eapply (u8_of_KWord1a Eout M' (EVar bn) off _ av)
        end;
        [ apply Cells; simpl; repeat (first [left; reflexivity | right])
        | (lazymatch goal with
           | |- bv_unsigned (edenot _ (ELit _)) = _ => reflexivity
           | |- bv_unsigned _ = _ => eapply L5KA.zpolyA_val; [ eapply (L5K.zagree_lt _ _ _ _ _ Agr); [apply (L5K.zagree_all _ _ _ Uin) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | unfold Vin; cbv beta iota zeta delta [Nat.eqb]; unfold BL.MM; zp_norm;
              lazymatch goal with
              | |- bv_unsigned ?w0 mod _ = bv_unsigned _ =>
                  pose proof (bv_unsigned_in_range 64 w0) as BR; change (bv_modulus 64) with 18446744073709551616 in BR;
                  rewrite Z.mod_small by lia; reflexivity
              | |- _ => first [reflexivity | (rewrite Z.mod_small by lia; lia) | lia]
              end ]
           | |- _ => lia end) .. ]
    end.
Qed.
(* [comment removed for export] *)

End PNSRCP.
