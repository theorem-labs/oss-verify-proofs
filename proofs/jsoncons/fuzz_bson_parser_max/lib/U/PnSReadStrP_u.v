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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_bstA_u LibSegBs_bstRp_u LibSegBs_bstRe_u LibSegBs_bstRz_u LibSegBs_bstRn_u LibSegBs_bstS_u LibSegBs_bstT1_u LibSegBs_bstT0_u LibSegBs_bstE_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRSP.
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
Module PbstA := LibSegBs_bstA_u.
Definition KS_bstA : list nat := Eval vm_compute in (BG.kept_list 52 PbstA.regs0 PbstA.regs_out0).
Lemma KS_bstA_ok : BG.kept_ok 52 PbstA.regs0 PbstA.regs_out0 KS_bstA = true. Proof. vm_compute. reflexivity. Qed.
Lemma bstA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3871c M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_bstA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 231264
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 4
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 68)
        /\ getr R' (reg 12) = Z_to_bv 64 4
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 pvzI4 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PbstA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstA.kn0).
  { unfold know_ok, PbstA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstA.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 64) <= bv_unsigned a < (vz_2 - 64) + 64) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbstA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstA.ps0) with 0x370d0 in Hms. change (SR.ps_regs PbstA.ps0) with (map (fun i => (i, nth i PbstA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstA.ps0) with PbstA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstA.regs0 PbstA.regs_out0 52 KS_bstA KS_bstA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbstRp := LibSegBs_bstRp_u.
Definition KS_bstRp : list nat := Eval vm_compute in (BG.kept_list 52 PbstRp.regs0 PbstRp.regs_out0).
Lemma KS_bstRp_ok : BG.kept_ok 52 PbstRp.regs0 PbstRp.regs_out0 KS_bstRp = true. Proof. vm_compute. reflexivity. Qed.
Lemma bstRp_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 4 -> getr R (reg 10) = Z_to_bv 64 4 -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 16) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 80)) -> L5.u32_at RSEGS M ((V 2%nat) - 68) (V 46%nat) -> 1 <= (V 46%nat) <= 2147483647 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38760 M) (st fx' R' 0x39290 M')
        /\ (forall x, In x KS_bstRp -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 231296
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 46%nat) - 1)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 46%nat) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 368)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G19 G20 pvzI5 K1 K2 pvzI6 K4 K5 K6 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV46l; move HV46l before pvzI4; pose proof (proj2 pvzI4) as HV46r; move HV46r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_46 := V 46%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 46%nat => Z_to_bv 64 vz_46 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 46%nat => vz_46 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 47%nat. }
  assert (HR: regs_ok E PbstRp.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstRp.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstRp.kn0).
  { unfold know_ok, PbstRp.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV46l HV46r K7l K7r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstRp.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstRp.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbstRp.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstRp.ps0) with 0x39290 in Hms. change (SR.ps_regs PbstRp.ps0) with (map (fun i => (i, nth i PbstRp.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstRp.ps0) with PbstRp.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstRp.regs0 PbstRp.regs_out0 52 KS_bstRp KS_bstRp_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstRp.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstRp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstRp.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstRp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstRp.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstRp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstRp.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstRp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstRp.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstRp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbstRp.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbstRp.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbstRe := LibSegBs_bstRe_u.
Definition KS_bstRe : list nat := Eval vm_compute in (BG.kept_list 52 PbstRe.regs0 PbstRe.regs_out0).
Lemma KS_bstRe_ok : BG.kept_ok 52 PbstRe.regs0 PbstRe.regs_out0 KS_bstRe = true. Proof. vm_compute. reflexivity. Qed.
Lemma bstRe_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 4 -> getr R (reg 10) = Z_to_bv 64 (V 44%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 16) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 0 <= (V 44%nat) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38760 M) (st fx' R' 0x36ee4 M')
        /\ (forall x, In x KS_bstRe -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 231440
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G19 G20 pvzI5 K1 K2 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV44l; move HV44l before pvzI4; pose proof (proj2 pvzI4) as HV44r; move HV44r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_44 := V 44%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 44%nat => Z_to_bv 64 vz_44 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 44%nat => vz_44 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E PbstRe.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstRe.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstRe.kn0).
  { unfold know_ok, PbstRe.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstRe.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstRe.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbstRe.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstRe.ps0) with 0x36ee4 in Hms. change (SR.ps_regs PbstRe.ps0) with (map (fun i => (i, nth i PbstRe.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstRe.ps0) with PbstRe.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstRe.regs0 PbstRe.regs_out0 52 KS_bstRe KS_bstRe_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstRe.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstRe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstRe.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstRe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbstRe.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstRe.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbstRz := LibSegBs_bstRz_u.
Definition KS_bstRz : list nat := Eval vm_compute in (BG.kept_list 52 PbstRz.regs0 PbstRz.regs_out0).
Lemma KS_bstRz_ok : BG.kept_ok 52 PbstRz.regs0 PbstRz.regs_out0 KS_bstRz = true. Proof. vm_compute. reflexivity. Qed.
Lemma bstRz_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 4 -> getr R (reg 10) = Z_to_bv 64 4 -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 16) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u32_at RSEGS M ((V 2%nat) - 68) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38760 M) (st fx' R' 0x36ee4 M')
        /\ (forall x, In x KS_bstRz -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 231440
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ getr R' (reg 21) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 G10 G19 G20 pvzI4 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PbstRz.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstRz.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstRz.kn0).
  { unfold know_ok, PbstRz.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstRz.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstRz.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbstRz.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstRz.ps0) with 0x36ee4 in Hms. change (SR.ps_regs PbstRz.ps0) with (map (fun i => (i, nth i PbstRz.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstRz.ps0) with PbstRz.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstRz.regs0 PbstRz.regs_out0 52 KS_bstRz KS_bstRz_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstRz.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstRz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstRz.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstRz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstRz.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstRz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbstRz.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbstRz.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbstRn := LibSegBs_bstRn_u.
Definition KS_bstRn : list nat := Eval vm_compute in (BG.kept_list 52 PbstRn.regs0 PbstRn.regs_out0).
Lemma KS_bstRn_ok : BG.kept_ok 52 PbstRn.regs0 PbstRn.regs_out0 KS_bstRn = true. Proof. vm_compute. reflexivity. Qed.
Lemma bstRn_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 4 -> getr R (reg 10) = Z_to_bv 64 4 -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 16) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u32_at RSEGS M ((V 2%nat) - 68) (V 46%nat) ->
  2147483648 <= (V 46%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38760 M) (st fx' R' 0x36ee4 M')
        /\ (forall x, In x KS_bstRn -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 231440
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G19 G20 pvzI5 K1 K2 K3 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV46l; move HV46l before pvzI4; pose proof (proj2 pvzI4) as HV46r; move HV46r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_46 := V 46%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 46%nat => Z_to_bv 64 vz_46 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 46%nat => vz_46 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 47%nat. }
  assert (HR: regs_ok E PbstRn.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstRn.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstRn.kn0).
  { unfold know_ok, PbstRn.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r K4l K4r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstRn.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstRn.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbstRn.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstRn.ps0) with 0x36ee4 in Hms. change (SR.ps_regs PbstRn.ps0) with (map (fun i => (i, nth i PbstRn.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstRn.ps0) with PbstRn.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstRn.regs0 PbstRn.regs_out0 52 KS_bstRn KS_bstRn_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstRn.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstRn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstRn.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstRn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbstRn.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstRn.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbstS := LibSegBs_bstS_u.
Definition KS_bstS_0 : list nat := Eval vm_compute in (BG.kept_list 52 PbstS.regs0 PbstS.regs_out0).
Lemma KS_bstS_0_ok : BG.kept_ok 52 PbstS.regs0 PbstS.regs_out0 KS_bstS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bstS_1 : list nat := Eval vm_compute in (BG.kept_list 52 PbstS.regs0 PbstS.regs_out1).
Lemma KS_bstS_1_ok : BG.kept_ok 52 PbstS.regs0 PbstS.regs_out1 KS_bstS_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bstS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 46%nat) - 1) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 48%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 21) = Z_to_bv 64 (V 46%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 1 <= (V 46%nat) <= 2147483647 ->
  0 <= (V 48%nat) <= 2147483647 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38780 M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_bstS_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 231324
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 69)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 1
        /\ (((V 48%nat) - (((V 46%nat) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38780 M) (st fx' R' 0x36ee4 M')
        /\ (forall x, In x KS_bstS_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 231440
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ 1 <= (((V 48%nat) - (((V 46%nat) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G11 G19 G20 G21 pvzI7 K1 K2 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV46l; move HV46l before pvzI4; pose proof (proj2 pvzI4) as HV46r; move HV46r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbstS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstS.kn0).
  { unfold know_ok, PbstS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstS.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbstS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PbstS.ps0) with 0x370d0 in Hms. change (SR.ps_regs PbstS.ps0) with (map (fun i => (i, nth i PbstS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbstS.ps0) with PbstS.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstS.regs0 PbstS.regs_out0 52 KS_bstS_0 KS_bstS_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbstS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbstS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbstS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbstS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbstS.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbstS.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbstS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PbstS.ps1) with 0x36ee4 in Hms. change (SR.ps_regs PbstS.ps1) with (map (fun i => (i, nth i PbstS.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbstS.ps1) with PbstS.cells1 in Hcells. unfold PbstS.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstS.regs0 PbstS.regs_out1 52 KS_bstS_1 KS_bstS_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbstS.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbstS.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbstS.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbstT1 := LibSegBs_bstT1_u.
Definition KS_bstT1 : list nat := Eval vm_compute in (BG.kept_list 52 PbstT1.regs0 PbstT1.regs_out0).
Lemma KS_bstT1_ok : BG.kept_ok 52 PbstT1.regs0 PbstT1.regs_out0 KS_bstT1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bstT1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 46%nat) - 1) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 21) = Z_to_bv 64 (V 46%nat) -> getr R (reg 22) = Z_to_bv 64 1 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 43%nat) -> 140735332483152 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 80)) -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> 4136 <= (V 45%nat) <= 140737488355328 ->
  aligned (V 45%nat) 8 -> L5.u64_at RSEGS M ((V 45%nat) - 24) (V 49%nat) -> L5.writable RSEGS M ((V 45%nat) - 24) 8 -> (((V 2%nat) - 80) + 80 <= ((V 45%nat) - 40) \/ ((V 45%nat) - 40) + 40 <= ((V 2%nat) - 80)) ->
  (((V 45%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 45%nat) - 40)) -> 1 <= (V 46%nat) <= 2147483647 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 45%nat) - 24) <= bv_unsigned a < ((V 45%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 45%nat) - 24) <= i < ((V 45%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3879c M) (st fx' R' 0x387f8 M')
        /\ (forall x, In x KS_bstT1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 46%nat) - 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 43%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 pvzI17 K12 K13 K14 pvzI18 K16 K17 K18 K19 K20 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV41l; move HV41l before pvzI9; pose proof (proj2 pvzI9) as HV41r; move HV41r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV42l; move HV42l before pvzI10; pose proof (proj2 pvzI10) as HV42r; move HV42r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV43l; move HV43l before pvzI11; pose proof (proj2 pvzI11) as HV43r; move HV43r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV45l; move HV45l before pvzI12; pose proof (proj2 pvzI12) as HV45r; move HV45r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV46l; move HV46l before pvzI13; pose proof (proj2 pvzI13) as HV46r; move HV46r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV47l; move HV47l before pvzI14; pose proof (proj2 pvzI14) as HV47r; move HV47r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV49l; move HV49l before pvzI15; pose proof (proj2 pvzI15) as HV49r; move HV49r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K11l; move K11l before pvzI17; pose proof (proj2 pvzI17) as K11r; move K11r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K15l; move K15l before pvzI18; pose proof (proj2 pvzI18) as K15r; move K15r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K21l; move K21l before pvzI19; pose proof (proj2 pvzI19) as K21r; move K21r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PbstT1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstT1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstT1.kn0).
  { unfold know_ok, PbstT1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K19) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K19) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K19) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K19; lia | clear - HV2l HV2r K0l K0r K13 K19; lia | clear - HV2l HV2r K0l K0r K13 K19; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K19) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K13 K19; lia | clear - HV2l HV2r K0l K0r K13 K19; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K19) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K13 K19; lia | clear - HV2l HV2r K0l K0r K13 K19; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K19) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K13 K19; lia | clear - HV2l HV2r K0l K0r K13 K19; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K19) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K13 K19; lia | clear - HV2l HV2r K0l K0r K13 K19; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K19) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K13 K19; lia | clear - HV2l HV2r K0l K0r K13 K19; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K19) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K13 K19; lia | clear - HV2l HV2r K0l K0r K13 K19; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K19) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K13 K19; lia | clear - HV2l HV2r K0l K0r K13 K19; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K19) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K13 K19; lia | clear - HV2l HV2r K0l K0r K13 K19; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13 K20) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13 K20) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13 K20) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13 K20) | evalEk ZA ltac:(clear - HV45l HV45r K15l K15r K19 K20) | clear - HV33l HV33r K11l K11r K13 K20; lia | clear - HV33l HV33r K11l K11r K13 K20; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K15l K15r K19 K20) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K15l K15r K19 K20) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K15l K15r K19 K20) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV45l HV45r K15l K15r K19 K20; lia | clear - HV45l HV45r K15l K15r K19 K20; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K15l K15r K19 K20) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K15l K15r K19 K20; lia | clear - HV45l HV45r K15l K15r K19 K20; lia | clear - HV45l HV45r K15l K15r K19 K20; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K15l K15r K19 K20) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K15l K15r K19 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstT1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstT1.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_45 - 24) <= bv_unsigned a < (vz_45 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbstT1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K15l K15r K19 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K15l K15r K19 K20 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstT1.ps0) with 0x387f8 in Hms. change (SR.ps_regs PbstT1.ps0) with (map (fun i => (i, nth i PbstT1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstT1.ps0) with PbstT1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstT1.regs0 PbstT1.regs_out0 52 KS_bstT1 KS_bstT1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstT1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstT1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstT1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstT1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstT1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstT1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstT1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstT1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstT1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstT1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbstT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbstT1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbstT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbstT0 := LibSegBs_bstT0_u.
Definition KS_bstT0 : list nat := Eval vm_compute in (BG.kept_list 52 PbstT0.regs0 PbstT0.regs_out0).
Lemma KS_bstT0_ok : BG.kept_ok 52 PbstT0.regs0 PbstT0.regs_out0 KS_bstT0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bstT0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 46%nat) - 1) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 21) = Z_to_bv 64 (V 46%nat) -> getr R (reg 22) = Z_to_bv 64 1 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3879c M) (st fx' R' 0x36ee4 M')
        /\ (forall x, In x KS_bstT0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 231440
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI6 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV46l; move HV46l before pvzI4; pose proof (proj2 pvzI4) as HV46r; move HV46r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 46%nat => vz_46 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PbstT0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstT0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstT0.kn0).
  { unfold know_ok, PbstT0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstT0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstT0.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbstT0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstT0.ps0) with 0x36ee4 in Hms. change (SR.ps_regs PbstT0.ps0) with (map (fun i => (i, nth i PbstT0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstT0.ps0) with PbstT0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstT0.regs0 PbstT0.regs_out0 52 KS_bstT0 KS_bstT0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstT0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstT0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbstT0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbstE := LibSegBs_bstE_u.
Definition KS_bstE : list nat := Eval vm_compute in (BG.kept_list 52 PbstE.regs0 PbstE.regs_out0).
Lemma KS_bstE_ok : BG.kept_ok 52 PbstE.regs0 PbstE.regs_out0 KS_bstE = true. Proof. vm_compute. reflexivity. Qed.
Lemma bstE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 16) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 43%nat) -> 140735332483152 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 80)) -> L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38810 M) (st fx' R' 0x387f8 M')
        /\ (forall x, In x KS_bstE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 43%nat)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G19 G20 pvzI12 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 pvzI13 K12 K13 K14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV41l; move HV41l before pvzI9; pose proof (proj2 pvzI9) as HV41r; move HV41r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV42l; move HV42l before pvzI10; pose proof (proj2 pvzI10) as HV42r; move HV42r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV43l; move HV43l before pvzI11; pose proof (proj2 pvzI11) as HV43r; move HV43r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K11l; move K11l before pvzI13; pose proof (proj2 pvzI13) as K11r; move K11r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PbstE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstE.kn0).
  { unfold know_ok, PbstE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | exactA K14]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstE.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbstE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K11l K11r K13 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstE.ps0) with 0x387f8 in Hms. change (SR.ps_regs PbstE.ps0) with (map (fun i => (i, nth i PbstE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstE.ps0) with PbstE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstE.regs0 PbstE.regs_out0 52 KS_bstE KS_bstE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstE.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstE.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstE.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbstE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstE.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbstE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNSRSP.
