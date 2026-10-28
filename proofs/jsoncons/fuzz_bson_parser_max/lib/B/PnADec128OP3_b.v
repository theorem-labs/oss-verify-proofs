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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_adoXA_b LibSegBa_adoXP_b LibSegBa_adoXL1_b LibSegBa_adoXD_b LibSegBa_adoXN0_b LibSegBa_adoXN_b LibSegBa_adoXNL_b LibSegBa_adoXM_b LibSegBa_adoXL2_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADOP3.
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
Module PadoXA := LibSegBa_adoXA_b.
Definition KS_adoXA : list nat := Eval vm_compute in (BG.kept_list 100 PadoXA.regs0 PadoXA.regs_out0).
Lemma KS_adoXA_ok : BG.kept_ok 100 PadoXA.regs0 PadoXA.regs_out0 KS_adoXA = true. Proof. vm_compute. reflexivity. Qed.
Lemma adoXA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 13) = Z_to_bv 64 (V 75%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 73%nat) - 6176) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 1 <= (V 75%nat) <= 36 ->
  0 <= (V 73%nat) <= 16383 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb44ac M) (st fx' R' 0xb44b0 M')
        /\ (forall x, In x KS_adoXA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = getr R (reg 12)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 73%nat) + (V 75%nat)) - 6176)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G13 G14 G19 G20 pvzI5 K1 K2 pvzI6 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV73l; move HV73l before pvzI3; pose proof (proj2 pvzI3) as HV73r; move HV73r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV75l; move HV75l before pvzI4; pose proof (proj2 pvzI4) as HV75r; move HV75r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 73%nat => Z_to_bv 64 vz_73 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 73%nat => vz_73 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PadoXA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadoXA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadoXA.kn0).
  { unfold know_ok, PadoXA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadoXA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadoXA.NX0 with 100%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadoXA.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadoXA.ps0) with 0xb44b0 in Hms. change (SR.ps_regs PadoXA.ps0) with (map (fun i => (i, nth i PadoXA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadoXA.ps0) with PadoXA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXA.regs0 PadoXA.regs_out0 100 KS_adoXA KS_adoXA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadoXA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoXA.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  rewrite (BG.out_reg PadoXA.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PadoXA.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadoXP := LibSegBa_adoXP_b.
Definition KS_adoXP : list nat := Eval vm_compute in (BG.kept_list 100 PadoXP.regs0 PadoXP.regs_out0).
Lemma KS_adoXP_ok : BG.kept_ok 100 PadoXP.regs0 PadoXP.regs_out0 KS_adoXP = true. Proof. vm_compute. reflexivity. Qed.
Lemma adoXP_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 -> 0 <= (V 86%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 14) = Z_to_bv 64 (V 86%nat) -> getr R (reg 18) = Z_to_bv 64 (V 77%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 30) = Z_to_bv 64 ((V 33%nat) + (V 79%nat)) ->
  aligned (V 77%nat) 4 -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 42) -> 140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 ->
  L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 79%nat) <= 1 -> 1 <= (V 86%nat) <= 35 ->
  4096 <= (V 77%nat) <= 140737488355320 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb44b0 M) (st fx' R' 0xb44d4 M')
        /\ (forall x, In x KS_adoXP -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 2
        /\ getr R' (reg 10) = Z_to_bv 64 (V 77%nat)
        /\ getr R' (reg 11) = getr R (reg 11)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 79%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 86%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 18446744073709551611).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G14 G18 G19 G20 G30 K0 K1 pvzI6 K3 K4 pvzI7 pvzI8 pvzI9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV77l; move HV77l before pvzI3; pose proof (proj2 pvzI3) as HV77r; move HV77r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV79l; move HV79l before pvzI4; pose proof (proj2 pvzI4) as HV79r; move HV79r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV86l; move HV86l before pvzI5; pose proof (proj2 pvzI5) as HV86r; move HV86r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K2l; move K2l before pvzI6; pose proof (proj2 pvzI6) as K2r; move K2r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K5l; move K5l before pvzI7; pose proof (proj2 pvzI7) as K5r; move K5r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_77 := V 77%nat) in *. set (vz_79 := V 79%nat) in *. set (vz_86 := V 86%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 77%nat => Z_to_bv 64 vz_77 | 79%nat => Z_to_bv 64 vz_79 | 86%nat => Z_to_bv 64 vz_86 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 77%nat => vz_77 | 79%nat => vz_79 | 86%nat => vz_86 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 87%nat. }
  assert (HR: regs_ok E PadoXP.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadoXP.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadoXP.kn0).
  { unfold know_ok, PadoXP.kn0.
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV77l HV77r K8l K8r) | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r) | clear - HV2l HV2r K2l K2r; lia | clear - HV2l HV2r K2l K2r; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K2l K2r; lia | clear - HV2l HV2r K2l K2r; lia | clear - HV2l HV2r K2l K2r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV86l HV86r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadoXP.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadoXP.NX0 with 100%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadoXP.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadoXP.ps0) with 0xb44d4 in Hms. change (SR.ps_regs PadoXP.ps0) with (map (fun i => (i, nth i PadoXP.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadoXP.ps0) with PadoXP.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXP.regs0 PadoXP.regs_out0 100 KS_adoXP KS_adoXP_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadoXP.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PadoXP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXP.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoXP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXP.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoXP.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadoXP.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoXP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXP.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PadoXP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXP.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoXP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXP.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PadoXP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PadoXP.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PadoXP.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadoXL1 := LibSegBa_adoXL1_b.
Definition KS_adoXL1_0 : list nat := Eval vm_compute in (BG.kept_list 100 PadoXL1.regs0 PadoXL1.regs_out0).
Lemma KS_adoXL1_0_ok : BG.kept_ok 100 PadoXL1.regs0 PadoXL1.regs_out0 KS_adoXL1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adoXL1_1 : list nat := Eval vm_compute in (BG.kept_list 100 PadoXL1.regs0 PadoXL1.regs_out1).
Lemma KS_adoXL1_1_ok : BG.kept_ok 100 PadoXL1.regs0 PadoXL1.regs_out1 KS_adoXL1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adoXL1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 -> 0 <= (V 80%nat) < 2 ^ 64 -> 0 <= (V 86%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 2 -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 77%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 79%nat)) -> getr R (reg 14) = Z_to_bv 64 (V 86%nat) -> getr R (reg 15) = Z_to_bv 64 0 -> getr R (reg 16) = Z_to_bv 64 (V 76%nat) -> getr R (reg 17) = Z_to_bv 64 18446744073709551611 -> getr R (reg 18) = Z_to_bv 64 (V 77%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 30) = Z_to_bv 64 ((V 33%nat) + (V 79%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 42) -> 140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 ->
  4096 <= (V 77%nat) <= 140737488355320 -> aligned (V 77%nat) 4 -> L5KA.zeros_at M (((V 77%nat) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M (V 77%nat) (V 80%nat) ->
  0 <= (V 80%nat) <= 9 -> (2147446784 + 17592186048512 <= (V 77%nat) \/ (V 77%nat) + 4 <= 2147446784) -> 4096 <= ((V 33%nat) + (V 79%nat)) <= 140737488355321 -> L5KA.zeros_at M ((((V 33%nat) + (V 79%nat)) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M ((V 33%nat) + (V 79%nat)) 1 -> (2147446784 + 17592186048512 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= 65536) ->
  (((V 33%nat) + (V 79%nat)) + 1 <= (V 77%nat) \/ (V 77%nat) + 4 <= ((V 33%nat) + (V 79%nat))) -> 4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 79%nat) <= 35 -> 1 <= (V 86%nat) <= 35 ->
  1 <= (V 76%nat) <= 35 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (V 79%nat)) + 0) <= bv_unsigned a < (((V 33%nat) + (V 79%nat)) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (V 79%nat)) + 0) <= i < (((V 33%nat) + (V 79%nat)) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb44d4 M) (st fx' R' 0xb44d4 M')
        /\ (forall x, In x KS_adoXL1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 6) = Z_to_bv 64 ((V 33%nat) + 42)
        /\ getr R' (reg 7) = Z_to_bv 64 (V 80%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 77%nat) + 4)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) + 1)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 86%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 76%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 77%nat) + 4)
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 22) = getr R (reg 22)
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ getr R' (reg 30) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) + 1)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 80%nat => Z_to_bv 64 (V 80%nat) | 86%nat => Z_to_bv 64 (V 86%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EVar 76) (EVar 86))) <= 1
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 79%nat)) ((V 80%nat) + 48))
      \/ (msteps RSEGS (st fx R 0xb44d4 M) (st fx' R' 0xb484c M')
        /\ (forall x, In x KS_adoXL1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 6) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) + 1)
        /\ getr R' (reg 7) = Z_to_bv 64 (V 80%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 77%nat) + 4)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 80%nat) + 48)
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (V 76%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 77%nat) + 4)
        /\ getr R' (reg 22) = getr R (reg 22)
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 80%nat => Z_to_bv 64 (V 80%nat) | 86%nat => Z_to_bv 64 (V 86%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EVar 76) (EVar 86))) <= 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 79%nat)) ((V 80%nat) + 48))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G5 G8 G9 G10 G12 G14 G15 G16 G17 G18 G19 G20 G30 K0 pvzI8 K2 K3 pvzI9 K5 K6 K7 pvzI10 K9 pvzI11 K11 K12 K13 K14 K15 K16 pvzI12 pvzI13 pvzI14 pvzI15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV76l; move HV76l before pvzI3; pose proof (proj2 pvzI3) as HV76r; move HV76r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV77l; move HV77l before pvzI4; pose proof (proj2 pvzI4) as HV77r; move HV77r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV79l; move HV79l before pvzI5; pose proof (proj2 pvzI5) as HV79r; move HV79r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV80l; move HV80l before pvzI6; pose proof (proj2 pvzI6) as HV80r; move HV80r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV86l; move HV86l before pvzI7; pose proof (proj2 pvzI7) as HV86r; move HV86r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K1l; move K1l before pvzI8; pose proof (proj2 pvzI8) as K1r; move K1r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K10l; move K10l before pvzI11; pose proof (proj2 pvzI11) as K10r; move K10r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K17l; move K17l before pvzI12; pose proof (proj2 pvzI12) as K17r; move K17r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K18l; move K18l before pvzI13; pose proof (proj2 pvzI13) as K18r; move K18r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K19l; move K19l before pvzI14; pose proof (proj2 pvzI14) as K19r; move K19r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K20l; move K20l before pvzI15; pose proof (proj2 pvzI15) as K20r; move K20r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_76 := V 76%nat) in *. set (vz_77 := V 77%nat) in *. set (vz_79 := V 79%nat) in *. set (vz_80 := V 80%nat) in *. set (vz_86 := V 86%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 76%nat => Z_to_bv 64 vz_76 | 77%nat => Z_to_bv 64 vz_77 | 79%nat => Z_to_bv 64 vz_79 | 80%nat => Z_to_bv 64 vz_80 | 86%nat => Z_to_bv 64 vz_86 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 76%nat => vz_76 | 77%nat => vz_77 | 79%nat => vz_79 | 80%nat => vz_80 | 86%nat => vz_86 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 87%nat. }
  assert (HR: regs_ok E PadoXL1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadoXL1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadoXL1.kn0).
  { unfold know_ok, PadoXL1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K14) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16) | clear - HV2l HV2r K1l K1r K14; lia | clear - HV2l HV2r K1l K1r K14; lia | exactA K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K14) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K14) | clear; lia | exact K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K1l K1r K14; lia | clear - HV2l HV2r K1l K1r K14; lia | clear - HV2l HV2r K1l K1r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K4l K4r K9 K16) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV77l HV77r K4l K4r K9 K16) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV77l HV77r K4l K4r K9 K16) | evalEk ZA ltac:(clear) | clear - HV77l HV77r K4l K4r K9 K16; lia | clear - HV77l HV77r K4l K4r K9 K16; lia | clear - HV77l HV77r K4l K4r K9 K16; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV77l HV77r K4l K4r K9 K16) | evalEk ZA ltac:(clear - HV80l HV80r K8l K8r) | clear - HV77l HV77r K4l K4r K9 K16; lia | clear - HV77l HV77r K4l K4r K9 K16; lia | byte_tac ltac:(clear - HV80l HV80r K8l K8r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV80l HV80r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV77l HV77r K4l K4r K9 K16) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV77l HV77r K4l K4r K9 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K10l K10r K18l K18r K13 K14 K15 K16) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV86l HV86r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadoXL1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadoXL1.NX0 with 100%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_33 + vz_79) + 0) <= bv_unsigned a < ((vz_33 + vz_79) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadoXL1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadoXL1.ps0) with 0xb44d4 in Hms. change (SR.ps_regs PadoXL1.ps0) with (map (fun i => (i, nth i PadoXL1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoXL1.ps0) with PadoXL1.cells0 in Hcells. unfold PadoXL1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXL1.regs0 PadoXL1.regs_out0 100 KS_adoXL1_0 KS_adoXL1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoXL1.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out0 E' R' 7 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out0 E' R' 30 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk' ZA Hag ltac:(clear - HV80l HV80r K8l K8r) | byte_tac ltac:(clear - HV80l HV80r K8l K8r) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right.
    change (SR.ps_pc PadoXL1.ps1) with 0xb484c in Hms. change (SR.ps_regs PadoXL1.ps1) with (map (fun i => (i, nth i PadoXL1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoXL1.ps1) with PadoXL1.cells1 in Hcells. unfold PadoXL1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXL1.regs0 PadoXL1.regs_out1 100 KS_adoXL1_1 KS_adoXL1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoXL1.regs_out1 E' R' 6 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out1 E' R' 7 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out1]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadoXL1.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PadoXL1.regs_out1]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk' ZA Hag ltac:(clear - HV80l HV80r K8l K8r) | byte_tac ltac:(clear - HV80l HV80r K8l K8r) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadoXD := LibSegBa_adoXD_b.
Definition KS_adoXD_0 : list nat := Eval vm_compute in (BG.kept_list 100 PadoXD.regs0 PadoXD.regs_out0).
Lemma KS_adoXD_0_ok : BG.kept_ok 100 PadoXD.regs0 PadoXD.regs_out0 KS_adoXD_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adoXD_1 : list nat := Eval vm_compute in (BG.kept_list 100 PadoXD.regs0 PadoXD.regs_out1).
Lemma KS_adoXD_1_ok : BG.kept_ok 100 PadoXD.regs0 PadoXD.regs_out1 KS_adoXD_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adoXD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 -> 0 <= (V 86%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 6) = Z_to_bv 64 ((V 33%nat) + (V 79%nat)) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 77%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 33%nat) + (V 79%nat)) -> getr R (reg 13) = Z_to_bv 64 (V 75%nat) -> getr R (reg 14) = Z_to_bv 64 (V 86%nat) -> getr R (reg 18) = Z_to_bv 64 (V 77%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) ->
  aligned (V 77%nat) 4 -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 42) -> 140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 ->
  L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= ((V 33%nat) + (V 79%nat)) <= 140737488355321 -> L5KA.zeros_at M ((((V 33%nat) + (V 79%nat)) / 8) + 2147450880) 1 -> L5.writable RSEGS M ((V 33%nat) + (V 79%nat)) 1 ->
  (2147446784 + 17592186048512 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= 65536) -> 4096 <= (V 33%nat) <= 140737488355280 ->
  1 <= (V 79%nat) <= 36 -> 0 <= (V 86%nat) <= 35 -> 1 <= (V 75%nat) <= 36 -> 4096 <= (V 77%nat) <= 140737488355320 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (V 79%nat)) + 0) <= bv_unsigned a < (((V 33%nat) + (V 79%nat)) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (V 79%nat)) + 0) <= i < (((V 33%nat) + (V 79%nat)) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb484c M) (st fx' R' 0xb46b0 M')
        /\ (forall x, In x KS_adoXD_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 ((V 86%nat) + 1)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 77%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) + 1)
        /\ getr R' (reg 15) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 86%nat => Z_to_bv 64 (V 86%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_SLT (ELit 0) (EVar 86))) (EVar 86))
        /\ getr R' (reg 16) = Z_to_bv 64 48
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 86%nat) + 1)
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) + 1)
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 86%nat => Z_to_bv 64 (V 86%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EVar 75) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_SLT (ELit 0) (EVar 86))) (EVar 86))) (ELit 1))) <= 1
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 79%nat)) 46)
      \/ (msteps RSEGS (st fx R 0xb484c M) (st fx' R' 0xb4910 M')
        /\ (forall x, In x KS_adoXD_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 ((V 86%nat) + 1)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 77%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) + 1)
        /\ bv_unsigned (getr R' (reg 12)) = (((((V 33%nat) + (V 79%nat)) mod 2 ^ 64) + 1) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 86%nat => Z_to_bv 64 (V 86%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4294967296) (EVar 75)) (EMd Instr.M_MUL (ELit (-4294967296)) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_SLT (ELit 0) (EVar 86))) (EVar 86)))) (ELit 32))
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551611
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 86%nat) + 1)
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 24) = getr R (reg 24)
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 86%nat => Z_to_bv 64 (V 86%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EVar 75) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_SLT (ELit 0) (EVar 86))) (EVar 86))) (ELit 1))) <= 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 79%nat)) 46)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G6 G8 G9 G10 G11 G13 G14 G18 G19 G20 K0 K1 pvzI7 K3 K4 pvzI8 K6 K7 K8 K9 K10 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV75l; move HV75l before pvzI3; pose proof (proj2 pvzI3) as HV75r; move HV75r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV77l; move HV77l before pvzI4; pose proof (proj2 pvzI4) as HV77r; move HV77r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV79l; move HV79l before pvzI5; pose proof (proj2 pvzI5) as HV79r; move HV79r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV86l; move HV86l before pvzI6; pose proof (proj2 pvzI6) as HV86r; move HV86r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K11l; move K11l before pvzI9; pose proof (proj2 pvzI9) as K11r; move K11r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K12l; move K12l before pvzI10; pose proof (proj2 pvzI10) as K12r; move K12r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K15l; move K15l before pvzI13; pose proof (proj2 pvzI13) as K15r; move K15r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_75 := V 75%nat) in *. set (vz_77 := V 77%nat) in *. set (vz_79 := V 79%nat) in *. set (vz_86 := V 86%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 75%nat => Z_to_bv 64 vz_75 | 77%nat => Z_to_bv 64 vz_77 | 79%nat => Z_to_bv 64 vz_79 | 86%nat => Z_to_bv 64 vz_86 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 75%nat => vz_75 | 77%nat => vz_77 | 79%nat => vz_79 | 86%nat => vz_86 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 87%nat. }
  assert (HR: regs_ok E PadoXD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadoXD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadoXD.kn0).
  { unfold know_ok, PadoXD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV77l HV77r K15l K15r) | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r K9) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10) | clear - HV2l HV2r K2l K2r K9; lia | clear - HV2l HV2r K2l K2r K9; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r K9) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r K9) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K2l K2r K9; lia | clear - HV2l HV2r K2l K2r K9; lia | clear - HV2l HV2r K2l K2r K9; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r; lia | clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r; lia | clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r; lia | clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r; lia | clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K5l K5r K12l K12r K8 K9 K10) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV86l HV86r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadoXD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadoXD.NX0 with 100%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_33 + vz_79) + 0) <= bv_unsigned a < ((vz_33 + vz_79) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadoXD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadoXD.ps0) with 0xb46b0 in Hms. change (SR.ps_regs PadoXD.ps0) with (map (fun i => (i, nth i PadoXD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoXD.ps0) with PadoXD.cells0 in Hcells. unfold PadoXD.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXD.regs0 PadoXD.regs_out0 100 KS_adoXD_0 KS_adoXD_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoXD.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out0]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoXD.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadoXD.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right.
    change (SR.ps_pc PadoXD.ps1) with 0xb4910 in Hms. change (SR.ps_regs PadoXD.ps1) with (map (fun i => (i, nth i PadoXD.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoXD.ps1) with PadoXD.cells1 in Hcells. unfold PadoXD.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXD.regs0 PadoXD.regs_out1 100 KS_adoXD_1 KS_adoXD_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoXD.regs_out1 E' R' 5 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadoXD.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out1]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoXD.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out1 E' R' 17 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXD.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out1]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadoXD.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out1]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadoXD.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PadoXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K11l K11r K8 K9 K10 HV79l HV79r K12l K12r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadoXN0 := LibSegBa_adoXN0_b.
Definition KS_adoXN0 : list nat := Eval vm_compute in (BG.kept_list 100 PadoXN0.regs0 PadoXN0.regs_out0).
Lemma KS_adoXN0_ok : BG.kept_ok 100 PadoXN0.regs0 PadoXN0.regs_out0 KS_adoXN0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adoXN0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 13) = Z_to_bv 64 (V 75%nat) -> getr R (reg 14) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 77%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 30) = Z_to_bv 64 ((V 33%nat) + (V 79%nat)) ->
  aligned (V 77%nat) 4 -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 42) -> 140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 ->
  L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= ((V 33%nat) + (V 79%nat)) <= 140737488355321 -> L5KA.zeros_at M ((((V 33%nat) + (V 79%nat)) / 8) + 2147450880) 1 -> L5.writable RSEGS M ((V 33%nat) + (V 79%nat)) 1 ->
  (2147446784 + 17592186048512 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= 65536) -> 4096 <= (((V 33%nat) + (V 79%nat)) + 1) <= 140737488355321 ->
  L5KA.zeros_at M (((((V 33%nat) + (V 79%nat)) + 1) / 8) + 2147450880) 1 -> L5.writable RSEGS M (((V 33%nat) + (V 79%nat)) + 1) 1 -> (2147446784 + 17592186048512 <= (((V 33%nat) + (V 79%nat)) + 1) \/ (((V 33%nat) + (V 79%nat)) + 1) + 1 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= (((V 33%nat) + (V 79%nat)) + 1) \/ (((V 33%nat) + (V 79%nat)) + 1) + 1 <= ((V 2%nat) - 256)) ->
  (65536 + 6840320 <= (((V 33%nat) + (V 79%nat)) + 1) \/ (((V 33%nat) + (V 79%nat)) + 1) + 1 <= 65536) -> 4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 79%nat) <= 1 -> 1 <= (V 75%nat) <= 36 ->
  4096 <= (V 77%nat) <= 140737488355320 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (V 79%nat)) + 0) <= bv_unsigned a < (((V 33%nat) + (V 79%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (V 79%nat)) + 0) <= i < (((V 33%nat) + (V 79%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb44b0 M) (st fx' R' 0xb4910 M')
        /\ (forall x, In x KS_adoXN0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 1
        /\ getr R' (reg 10) = Z_to_bv 64 (V 77%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) + 2)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) + 2)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551611
        /\ getr R' (reg 17) = Z_to_bv 64 1
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 22) = getr R (reg 22)
        /\ getr R' (reg 24) = getr R (reg 24)
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 79%nat)) + 1) 46
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 79%nat)) 48).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G13 G14 G18 G19 G20 G30 K0 K1 pvzI6 K3 K4 pvzI7 K6 K7 K8 K9 K10 pvzI8 K12 K13 K14 K15 K16 pvzI9 pvzI10 pvzI11 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV75l; move HV75l before pvzI3; pose proof (proj2 pvzI3) as HV75r; move HV75r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV77l; move HV77l before pvzI4; pose proof (proj2 pvzI4) as HV77r; move HV77r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV79l; move HV79l before pvzI5; pose proof (proj2 pvzI5) as HV79r; move HV79r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K2l; move K2l before pvzI6; pose proof (proj2 pvzI6) as K2r; move K2r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K5l; move K5l before pvzI7; pose proof (proj2 pvzI7) as K5r; move K5r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K11l; move K11l before pvzI8; pose proof (proj2 pvzI8) as K11r; move K11r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K17l; move K17l before pvzI9; pose proof (proj2 pvzI9) as K17r; move K17r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K18l; move K18l before pvzI10; pose proof (proj2 pvzI10) as K18r; move K18r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K19l; move K19l before pvzI11; pose proof (proj2 pvzI11) as K19r; move K19r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K20l; move K20l before pvzI12; pose proof (proj2 pvzI12) as K20r; move K20r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_75 := V 75%nat) in *. set (vz_77 := V 77%nat) in *. set (vz_79 := V 79%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 75%nat => Z_to_bv 64 vz_75 | 77%nat => Z_to_bv 64 vz_77 | 79%nat => Z_to_bv 64 vz_79 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 75%nat => vz_75 | 77%nat => vz_77 | 79%nat => vz_79 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E PadoXN0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadoXN0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadoXN0.kn0).
  { unfold know_ok, PadoXN0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV77l HV77r K20l K20r) | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r K9 K15) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16) | clear - HV2l HV2r K2l K2r K9 K15; lia | clear - HV2l HV2r K2l K2r K9 K15; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r K9 K15) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r K9 K15) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r K9 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K2l K2r K9 K15; lia | clear - HV2l HV2r K2l K2r K9 K15; lia | clear - HV2l HV2r K2l K2r K9 K15; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r K9 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r K9 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K5l K5r K11l K11r K18l K18r K8 K9 K10 K14 K15 K16) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadoXN0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadoXN0.NX0 with 100%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_33 + vz_79) + 0) <= bv_unsigned a < ((vz_33 + vz_79) + 0) + 2) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadoXN0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadoXN0.ps0) with 0xb4910 in Hms. change (SR.ps_regs PadoXN0.ps0) with (map (fun i => (i, nth i PadoXN0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadoXN0.ps0) with PadoXN0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXN0.regs0 PadoXN0.regs_out0 100 KS_adoXN0 KS_adoXN0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadoXN0.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PadoXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PadoXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN0.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PadoXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN0.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PadoXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadoXN0.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadoXN0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PadoXN0.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadoXN0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoXN0.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadoXN0.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PadoXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K11l K11r K17l K17r K8 K9 K10 K14 K15 K16 HV79l HV79r K18l K18r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadoXN := LibSegBa_adoXN_b.
Definition KS_adoXN : list nat := Eval vm_compute in (BG.kept_list 100 PadoXN.regs0 PadoXN.regs_out0).
Lemma KS_adoXN_ok : BG.kept_ok 100 PadoXN.regs0 PadoXN.regs_out0 KS_adoXN = true. Proof. vm_compute. reflexivity. Qed.
Lemma adoXN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 -> 0 <= (V 87%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 13) = Z_to_bv 64 (V 75%nat) -> getr R (reg 14) = Z_to_bv 64 (18446744073709551615 - (V 87%nat)) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 30) = Z_to_bv 64 ((V 33%nat) + (V 79%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 42) -> 4096 <= (((V 33%nat) + (V 79%nat)) + 2) <= 140737488355321 -> L5.writable RSEGS M (((V 33%nat) + (V 79%nat)) + 2) 1 -> (2147446784 + 17592186048512 <= (((V 33%nat) + (V 79%nat)) + 2) \/ (((V 33%nat) + (V 79%nat)) + 2) + 1 <= 2147446784) ->
  (((V 2%nat) - 256) + 256 <= (((V 33%nat) + (V 79%nat)) + 2) \/ (((V 33%nat) + (V 79%nat)) + 2) + 1 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= (((V 33%nat) + (V 79%nat)) + 2) \/ (((V 33%nat) + (V 79%nat)) + 2) + 1 <= 65536) -> L5KA.zeros_at M (((((V 33%nat) + (V 79%nat)) + 2) / 8) + 2147450880) 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= ((V 33%nat) + (V 79%nat)) <= 140737488355321 -> L5KA.zeros_at M ((((V 33%nat) + (V 79%nat)) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M ((V 33%nat) + (V 79%nat)) 1 -> (2147446784 + 17592186048512 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= 65536) ->
  4096 <= (((V 33%nat) + (V 79%nat)) + 1) <= 140737488355321 -> L5KA.zeros_at M (((((V 33%nat) + (V 79%nat)) + 1) / 8) + 2147450880) 1 -> L5.writable RSEGS M (((V 33%nat) + (V 79%nat)) + 1) 1 -> (2147446784 + 17592186048512 <= (((V 33%nat) + (V 79%nat)) + 1) \/ (((V 33%nat) + (V 79%nat)) + 1) + 1 <= 2147446784) ->
  (((V 2%nat) - 256) + 256 <= (((V 33%nat) + (V 79%nat)) + 1) \/ (((V 33%nat) + (V 79%nat)) + 1) + 1 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= (((V 33%nat) + (V 79%nat)) + 1) \/ (((V 33%nat) + (V 79%nat)) + 1) + 1 <= 65536) -> 4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 79%nat) <= 1 ->
  1 <= (V 75%nat) <= 36 -> 0 <= (V 87%nat) <= 4 -> 18446744073709551611 <= (18446744073709551615 - (V 87%nat)) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (V 79%nat)) + 0) <= bv_unsigned a < (((V 33%nat) + (V 79%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (V 79%nat)) + 0) <= i < (((V 33%nat) + (V 79%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb44b0 M) (st fx' R' 0xb4884 M')
        /\ (forall x, In x KS_adoXN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = getr R (reg 1)
        /\ getr R' (reg 5) = Z_to_bv 64 ((-1) * (V 87%nat))
        /\ getr R' (reg 10) = getr R (reg 18)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) + 2)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) + 2)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 16) = Z_to_bv 64 48
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 22) = getr R (reg 22)
        /\ getr R' (reg 24) = getr R (reg 24)
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 79%nat)) + 1) 46
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 79%nat)) 48).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G13 G14 G19 G20 G30 K0 pvzI6 K2 K3 K4 K5 K6 pvzI7 K8 K9 pvzI8 K11 K12 K13 K14 K15 pvzI9 K17 K18 K19 K20 K21 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV75l; move HV75l before pvzI3; pose proof (proj2 pvzI3) as HV75r; move HV75r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV79l; move HV79l before pvzI4; pose proof (proj2 pvzI4) as HV79r; move HV79r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV87l; move HV87l before pvzI5; pose proof (proj2 pvzI5) as HV87r; move HV87r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K22l; move K22l before pvzI10; pose proof (proj2 pvzI10) as K22r; move K22r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K23l; move K23l before pvzI11; pose proof (proj2 pvzI11) as K23r; move K23r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K24l; move K24l before pvzI12; pose proof (proj2 pvzI12) as K24r; move K24r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K25l; move K25l before pvzI13; pose proof (proj2 pvzI13) as K25r; move K25r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K26l; move K26l before pvzI14; pose proof (proj2 pvzI14) as K26r; move K26r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_75 := V 75%nat) in *. set (vz_79 := V 79%nat) in *. set (vz_87 := V 87%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 75%nat => Z_to_bv 64 vz_75 | 79%nat => Z_to_bv 64 vz_79 | 87%nat => Z_to_bv 64 vz_87 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 75%nat => vz_75 | 79%nat => vz_79 | 87%nat => vz_87 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 88%nat. }
  assert (HR: regs_ok E PadoXN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadoXN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadoXN.kn0).
  { unfold know_ok, PadoXN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K7l K7r K4 K14 K20) | evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21) | clear - HV2l HV2r K7l K7r K4 K14 K20; lia | clear - HV2l HV2r K7l K7r K4 K14 K20; lia | exactA K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | generalize K3; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K7l K7r K4 K14 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K7l K7r K4 K14 K20) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K7l K7r K4 K14 K20) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K7l K7r K4 K14 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K7l K7r K4 K14 K20; lia | clear - HV2l HV2r K7l K7r K4 K14 K20; lia | clear - HV2l HV2r K7l K7r K4 K14 K20; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K7l K7r K4 K14 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K7l K7r K4 K14 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K1l K1r K10l K10r K16l K16r K23l K23r K3 K4 K5 K13 K14 K15 K19 K20 K21) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV87l HV87r K25l K25r K26l K26r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV87l HV87r K25l K25r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadoXN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadoXN.NX0 with 100%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_33 + vz_79) + 0) <= bv_unsigned a < ((vz_33 + vz_79) + 0) + 2) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadoXN.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadoXN.ps0) with 0xb4884 in Hms. change (SR.ps_regs PadoXN.ps0) with (map (fun i => (i, nth i PadoXN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadoXN.ps0) with PadoXN.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXN.regs0 PadoXN.regs_out0 100 KS_adoXN KS_adoXN_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadoXN.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadoXN.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadoXN.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PadoXN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoXN.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadoXN.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoXN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoXN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PadoXN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoXN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PadoXN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXN.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadoXN.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadoXN.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PadoXN.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadoXN.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoXN.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K1l K1r K10l K10r K16l K16r K22l K22r K3 K4 K5 K13 K14 K15 K19 K20 K21 HV79l HV79r K23l K23r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PadoXNL := LibSegBa_adoXNL_b.
Definition KS_adoXNL_0 : list nat := Eval vm_compute in (BG.kept_list 100 PadoXNL.regs0 PadoXNL.regs_out0).
Lemma KS_adoXNL_0_ok : BG.kept_ok 100 PadoXNL.regs0 PadoXNL.regs_out0 KS_adoXNL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adoXNL_1 : list nat := Eval vm_compute in (BG.kept_list 100 PadoXNL.regs0 PadoXNL.regs_out1).
Lemma KS_adoXNL_1_ok : BG.kept_ok 100 PadoXNL.regs0 PadoXNL.regs_out1 KS_adoXNL_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adoXNL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 -> 0 <= (V 87%nat) < 2 ^ 64 -> 0 <= (V 88%nat) < 2 ^ 64 -> 0 <= (V 89%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 ((V 89%nat) - 4) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))) -> getr R (reg 11) = Z_to_bv 64 (((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 2) -> getr R (reg 12) = Z_to_bv 64 (((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 2) -> getr R (reg 13) = Z_to_bv 64 (V 75%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 89%nat) - 5) -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 48 -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 30) = Z_to_bv 64 ((V 33%nat) + (V 79%nat)) ->
  L5.u8_at RSEGS M (((V 33%nat) + (V 79%nat)) + 1) 46 -> L5.u8_at RSEGS M ((V 33%nat) + (V 79%nat)) 48 -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 42) -> 4096 <= (((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 2) <= 140737488355321 ->
  L5.writable RSEGS M (((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 2) 1 -> (2147446784 + 17592186048512 <= (((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 2) \/ (((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 2) + 1 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= (((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 2) \/ (((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 2) + 1 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= (((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 2) \/ (((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 2) + 1 <= 65536) ->
  L5KA.zeros_at M (((((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 2) / 8) + 2147450880) 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 ->
  4096 <= ((V 33%nat) + (V 79%nat)) <= 140737488355321 -> L5KA.zeros_at M ((((V 33%nat) + (V 79%nat)) / 8) + 2147450880) 1 -> L5.writable RSEGS M ((V 33%nat) + (V 79%nat)) 1 -> (2147446784 + 17592186048512 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= 2147446784) ->
  (((V 2%nat) - 256) + 256 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= ((V 33%nat) + (V 79%nat)) \/ ((V 33%nat) + (V 79%nat)) + 1 <= 65536) -> 4096 <= (((V 33%nat) + (V 79%nat)) + 1) <= 140737488355321 -> L5KA.zeros_at M (((((V 33%nat) + (V 79%nat)) + 1) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (((V 33%nat) + (V 79%nat)) + 1) 1 -> (2147446784 + 17592186048512 <= (((V 33%nat) + (V 79%nat)) + 1) \/ (((V 33%nat) + (V 79%nat)) + 1) + 1 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= (((V 33%nat) + (V 79%nat)) + 1) \/ (((V 33%nat) + (V 79%nat)) + 1) + 1 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= (((V 33%nat) + (V 79%nat)) + 1) \/ (((V 33%nat) + (V 79%nat)) + 1) + 1 <= 65536) ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 79%nat) <= 1 -> 1 <= (V 75%nat) <= 36 -> 0 <= (V 87%nat) <= 4 ->
  18446744073709551611 <= (18446744073709551615 - (V 87%nat)) <= 18446744073709551615 -> 0 <= (V 88%nat) <= 5 -> 0 <= (V 89%nat) <= 5 -> 0 <= (((-1) * (V 88%nat)) + ((V 87%nat) + 1)) <= 134217728 ->
  4 <= (((V 89%nat) - (V 88%nat)) + (V 87%nat)) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (V 79%nat)) + 0) <= bv_unsigned a < (((V 33%nat) + (V 79%nat)) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (V 79%nat)) + 0) <= i < (((V 33%nat) + (V 79%nat)) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4884 M) (st fx' R' 0xb4884 M')
        /\ (forall x, In x KS_adoXNL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 ((V 89%nat) - 3)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 3)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 3)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 89%nat) - 4)
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 89%nat) - 4)
        /\ L5.u8_at RSEGS M' (((V 33%nat) + ((V 79%nat) + (V 88%nat))) + 2) 48
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 87%nat => Z_to_bv 64 (V 87%nat) | 88%nat => Z_to_bv 64 (V 88%nat) | 89%nat => Z_to_bv 64 (V 89%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_ADD (EVar 89) (ELit (-5))) (ELit 0))) <= 1
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 79%nat)) + 1) 46
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 79%nat)) 48)
      \/ (msteps RSEGS (st fx R 0xb4884 M) (st fx' R' 0xb48cc M')
        /\ (forall x, In x KS_adoXNL_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 89%nat) - 4)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 87%nat => Z_to_bv 64 (V 87%nat) | 88%nat => Z_to_bv 64 (V 88%nat) | 89%nat => Z_to_bv 64 (V 89%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_ADD (EVar 89) (ELit (-5))) (ELit 0))) <= 0
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 79%nat)) + 1) 46
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 79%nat)) 48)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G5 G8 G9 G10 G11 G12 G13 G14 G15 G16 G19 G20 G30 K0 K1 K2 pvzI8 K4 K5 K6 K7 K8 pvzI9 K10 K11 pvzI10 K13 K14 K15 K16 K17 pvzI11 K19 K20 K21 K22 K23 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV75l; move HV75l before pvzI3; pose proof (proj2 pvzI3) as HV75r; move HV75r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV79l; move HV79l before pvzI4; pose proof (proj2 pvzI4) as HV79r; move HV79r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV87l; move HV87l before pvzI5; pose proof (proj2 pvzI5) as HV87r; move HV87r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV88l; move HV88l before pvzI6; pose proof (proj2 pvzI6) as HV88r; move HV88r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV89l; move HV89l before pvzI7; pose proof (proj2 pvzI7) as HV89r; move HV89r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K9l; move K9l before pvzI9; pose proof (proj2 pvzI9) as K9r; move K9r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K12l; move K12l before pvzI10; pose proof (proj2 pvzI10) as K12r; move K12r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K18l; move K18l before pvzI11; pose proof (proj2 pvzI11) as K18r; move K18r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K24l; move K24l before pvzI12; pose proof (proj2 pvzI12) as K24r; move K24r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K25l; move K25l before pvzI13; pose proof (proj2 pvzI13) as K25r; move K25r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K26l; move K26l before pvzI14; pose proof (proj2 pvzI14) as K26r; move K26r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K27l; move K27l before pvzI15; pose proof (proj2 pvzI15) as K27r; move K27r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K28l; move K28l before pvzI16; pose proof (proj2 pvzI16) as K28r; move K28r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K29l; move K29l before pvzI17; pose proof (proj2 pvzI17) as K29r; move K29r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K30l; move K30l before pvzI18; pose proof (proj2 pvzI18) as K30r; move K30r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K31l; move K31l before pvzI19; pose proof (proj2 pvzI19) as K31r; move K31r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K32l; move K32l before pvzI20; pose proof (proj2 pvzI20) as K32r; move K32r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_75 := V 75%nat) in *. set (vz_79 := V 79%nat) in *. set (vz_87 := V 87%nat) in *. set (vz_88 := V 88%nat) in *. set (vz_89 := V 89%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 75%nat => Z_to_bv 64 vz_75 | 79%nat => Z_to_bv 64 vz_79 | 87%nat => Z_to_bv 64 vz_87 | 88%nat => Z_to_bv 64 vz_88 | 89%nat => Z_to_bv 64 vz_89 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 75%nat => vz_75 | 79%nat => vz_79 | 87%nat => vz_87 | 88%nat => vz_88 | 89%nat => vz_89 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 90%nat. }
  assert (HR: regs_ok E PadoXNL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadoXNL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadoXNL.kn0).
  { unfold know_ok, PadoXNL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | byte_tac ltac:(clear) | exactA K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | byte_tac ltac:(clear) | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K9l K9r K6 K16 K22) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23) | clear - HV2l HV2r K9l K9r K6 K16 K22; lia | clear - HV2l HV2r K9l K9r K6 K16 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r HV88l HV88r K29l K29r K31l K31r K32l K32r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r HV88l HV88r K29l K29r K31l K31r K32l K32r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r HV88l HV88r K29l K29r K31l K31r K32l K32r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r HV88l HV88r K29l K29r K31l K31r K32l K32r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r HV88l HV88r K29l K29r K31l K31r K32l K32r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r HV88l HV88r K29l K29r K31l K31r K32l K32r) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K9l K9r K6 K16 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r HV88l HV88r K29l K29r K31l K31r K32l K32r) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r HV88l HV88r K29l K29r K31l K31r K32l K32r) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r HV88l HV88r K29l K29r K31l K31r K32l K32r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r HV88l HV88r K29l K29r K31l K31r K32l K32r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r HV88l HV88r K29l K29r K31l K31r K32l K32r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r HV88l HV88r K29l K29r K31l K31r K32l K32r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K9l K9r K6 K16 K22) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K9l K9r K6 K16 K22) | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K9l K9r K6 K16 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K9l K9r K6 K16 K22; lia | clear - HV2l HV2r K9l K9r K6 K16 K22; lia | clear - HV2l HV2r K9l K9r K6 K16 K22; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K9l K9r K6 K16 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K9l K9r K6 K16 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K3l K3r K12l K12r K18l K18r K25l K25r K5 K6 K7 K15 K16 K17 K21 K22 K23) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV87l HV87r K27l K27r K28l K28r K31l K31r K32l K32r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV87l HV87r K27l K27r K28l K28r K31l K31r K32l K32r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV88l HV88r K3l K3r K29l K29r K31l K31r K32l K32r K5 K6 K7) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV89l HV89r K30l K30r K32l K32r) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV87l HV87r K27l K27r K28l K28r K31l K31r K32l K32r HV88l HV88r K3l K3r K29l K29r K5 K6 K7) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV87l HV87r K27l K27r K28l K28r K31l K31r K32l K32r HV88l HV88r K3l K3r K29l K29r K5 K6 K7 HV89l HV89r K30l K30r) | exact (conj K32l K32r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadoXNL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadoXNL.NX0 with 100%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_33 + vz_79) + 0) <= bv_unsigned a < ((vz_33 + vz_79) + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadoXNL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadoXNL.ps0) with 0xb4884 in Hms. change (SR.ps_regs PadoXNL.ps0) with (map (fun i => (i, nth i PadoXNL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoXNL.ps0) with PadoXNL.cells0 in Hcells. unfold PadoXNL.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXNL.regs0 PadoXNL.regs_out0 100 KS_adoXNL_0 KS_adoXNL_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoXNL.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PadoXNL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXNL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoXNL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXNL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoXNL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXNL.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PadoXNL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXNL.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PadoXNL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r HV88l HV88r K29l K29r K31l K31r K32l K32r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right.
    change (SR.ps_pc PadoXNL.ps1) with 0xb48cc in Hms. change (SR.ps_regs PadoXNL.ps1) with (map (fun i => (i, nth i PadoXNL.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoXNL.ps1) with PadoXNL.cells1 in Hcells. unfold PadoXNL.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXNL.regs0 PadoXNL.regs_out1 100 KS_adoXNL_1 KS_adoXNL_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoXNL.regs_out1 E' R' 17 Hregs) by (clear; lia). cbn [nth PadoXNL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K12l K12r K18l K18r K24l K24r K5 K6 K7 K15 K16 K17 K21 K22 K23 HV79l HV79r K25l K25r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadoXM := LibSegBa_adoXM_b.
Definition KS_adoXM : list nat := Eval vm_compute in (BG.kept_list 100 PadoXM.regs0 PadoXM.regs_out0).
Lemma KS_adoXM_ok : BG.kept_ok 100 PadoXM.regs0 PadoXM.regs_out0 KS_adoXM = true. Proof. vm_compute. reflexivity. Qed.
Lemma adoXM_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 -> 0 <= (V 87%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 1 -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 77%nat) -> getr R (reg 11) = Z_to_bv 64 (((V 33%nat) + ((V 79%nat) + (V 87%nat))) + 2) -> getr R (reg 12) = Z_to_bv 64 (((V 33%nat) + ((V 79%nat) + (V 87%nat))) + 2) -> getr R (reg 13) = Z_to_bv 64 (V 75%nat) -> getr R (reg 14) = Z_to_bv 64 0 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 77%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 30) = Z_to_bv 64 (((V 33%nat) + (V 79%nat)) - 1) ->
  aligned (V 77%nat) 4 -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 42) -> 140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 ->
  L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 33%nat) <= 140737488355280 -> 1 <= (V 79%nat) <= 2 -> 1 <= (V 75%nat) <= 36 ->
  0 <= (V 87%nat) <= 4 -> 4096 <= (V 77%nat) <= 140737488355320 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb48cc M) (st fx' R' 0xb4910 M')
        /\ (forall x, In x KS_adoXM -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 77%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 33%nat) + ((V 79%nat) + (V 87%nat))) + 2)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551611
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 24) = getr R (reg 24)
        /\ getr R' (reg 25) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G5 G8 G9 G10 G11 G12 G13 G14 G17 G18 G19 G20 G30 K0 K1 pvzI7 K3 K4 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV75l; move HV75l before pvzI3; pose proof (proj2 pvzI3) as HV75r; move HV75r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV77l; move HV77l before pvzI4; pose proof (proj2 pvzI4) as HV77r; move HV77r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV79l; move HV79l before pvzI5; pose proof (proj2 pvzI5) as HV79r; move HV79r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV87l; move HV87l before pvzI6; pose proof (proj2 pvzI6) as HV87r; move HV87r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K8l; move K8l before pvzI11; pose proof (proj2 pvzI11) as K8r; move K8r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K9l; move K9l before pvzI12; pose proof (proj2 pvzI12) as K9r; move K9r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_75 := V 75%nat) in *. set (vz_77 := V 77%nat) in *. set (vz_79 := V 79%nat) in *. set (vz_87 := V 87%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 75%nat => Z_to_bv 64 vz_75 | 77%nat => Z_to_bv 64 vz_77 | 79%nat => Z_to_bv 64 vz_79 | 87%nat => Z_to_bv 64 vz_87 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 75%nat => vz_75 | 77%nat => vz_77 | 79%nat => vz_79 | 87%nat => vz_87 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 88%nat. }
  assert (HR: regs_ok E PadoXM.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadoXM.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadoXM.kn0).
  { unfold know_ok, PadoXM.kn0.
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV77l HV77r K9l K9r) | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r) | clear - HV2l HV2r K2l K2r; lia | clear - HV2l HV2r K2l K2r; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K2l K2r; lia | clear - HV2l HV2r K2l K2r; lia | clear - HV2l HV2r K2l K2r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV87l HV87r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadoXM.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadoXM.NX0 with 100%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadoXM.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadoXM.ps0) with 0xb4910 in Hms. change (SR.ps_regs PadoXM.ps0) with (map (fun i => (i, nth i PadoXM.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadoXM.ps0) with PadoXM.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXM.regs0 PadoXM.regs_out0 100 KS_adoXM KS_adoXM_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadoXM.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoXM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXM.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoXM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXM.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PadoXM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXM.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoXM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXM.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PadoXM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoXM.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadoXM.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadoXM.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoXM.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  rewrite (BG.out_reg PadoXM.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PadoXM.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadoXL2 := LibSegBa_adoXL2_b.
Definition KS_adoXL2_0 : list nat := Eval vm_compute in (BG.kept_list 100 PadoXL2.regs0 PadoXL2.regs_out0).
Lemma KS_adoXL2_0_ok : BG.kept_ok 100 PadoXL2.regs0 PadoXL2.regs_out0 KS_adoXL2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adoXL2_1 : list nat := Eval vm_compute in (BG.kept_list 100 PadoXL2.regs0 PadoXL2.regs_out1).
Lemma KS_adoXL2_1_ok : BG.kept_ok 100 PadoXL2.regs0 PadoXL2.regs_out1 KS_adoXL2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adoXL2_2 : list nat := Eval vm_compute in (BG.kept_list 100 PadoXL2.regs0 PadoXL2.regs_out2).
Lemma KS_adoXL2_2_ok : BG.kept_ok 100 PadoXL2.regs0 PadoXL2.regs_out2 KS_adoXL2_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adoXL2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 -> 0 <= (V 80%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 77%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 33%nat) + ((V 76%nat) + (V 79%nat))) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + ((V 76%nat) + (V 79%nat))) -> getr R (reg 13) = Z_to_bv 64 ((V 76%nat) + 1) -> getr R (reg 14) = Z_to_bv 64 0 -> getr R (reg 15) = Z_to_bv 64 (V 78%nat) -> getr R (reg 16) = Z_to_bv 64 18446744073709551611 -> getr R (reg 18) = Z_to_bv 64 (V 77%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 42) -> 140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 ->
  4096 <= (V 77%nat) <= 140737488355320 -> aligned (V 77%nat) 4 -> L5KA.zeros_at M (((V 77%nat) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M (V 77%nat) (V 80%nat) ->
  0 <= (V 80%nat) <= 9 -> (2147446784 + 17592186048512 <= (V 77%nat) \/ (V 77%nat) + 4 <= 2147446784) -> 4096 <= ((V 33%nat) + ((V 76%nat) + (V 79%nat))) <= 140737488355321 -> L5KA.zeros_at M ((((V 33%nat) + ((V 76%nat) + (V 79%nat))) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M ((V 33%nat) + ((V 76%nat) + (V 79%nat))) 1 -> (2147446784 + 17592186048512 <= ((V 33%nat) + ((V 76%nat) + (V 79%nat))) \/ ((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 1 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 33%nat) + ((V 76%nat) + (V 79%nat))) \/ ((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 1 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= ((V 33%nat) + ((V 76%nat) + (V 79%nat))) \/ ((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 1 <= 65536) ->
  (((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 1 <= (V 77%nat) \/ (V 77%nat) + 4 <= ((V 33%nat) + ((V 76%nat) + (V 79%nat)))) -> 4096 <= (V 33%nat) <= 140737488355280 -> 2 <= (V 79%nat) <= 41 -> 0 <= (V 76%nat) <= 35 ->
  1 <= (V 78%nat) <= 36 -> 2 <= ((V 76%nat) + (V 79%nat)) <= 41 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 0) <= bv_unsigned a < (((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 0) <= i < (((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4910 M) (st fx' R' 0xb4910 M')
        /\ (forall x, In x KS_adoXL2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 77%nat) + 4)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 76%nat) + 2)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 (V 78%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 33%nat) + 42)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 77%nat) + 4)
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 1)
        /\ (((((V 33%nat) + (((V 76%nat) + (V 79%nat)) mod 2 ^ 64)) mod 2 ^ 64) + 1) mod 2 ^ 64) < (((V 33%nat) + 42) mod 2 ^ 64)
        /\ (((V 76%nat) + 1) mod 2 ^ 64) < (V 78%nat)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + ((V 76%nat) + (V 79%nat))) ((V 80%nat) + 48))
      \/ (msteps RSEGS (st fx R 0xb4910 M) (st fx' R' 0xb46b0 M')
        /\ (forall x, In x KS_adoXL2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + ((V 76%nat) + (V 79%nat)))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 76%nat) + 1)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 (V 78%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 80%nat) + 48)
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 1)
        /\ (V 78%nat) <= (((V 76%nat) + 1) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + ((V 76%nat) + (V 79%nat))) ((V 80%nat) + 48))
      \/ (msteps RSEGS (st fx R 0xb4910 M) (st fx' R' 0xb46b0 M')
        /\ (forall x, In x KS_adoXL2_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 77%nat) + 4)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 76%nat) + 2)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 (V 78%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 33%nat) + 42)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 77%nat) + 4)
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 33%nat) + ((V 76%nat) + (V 79%nat))) + 1)
        /\ (((V 33%nat) + 42) mod 2 ^ 64) <= (((((V 33%nat) + (((V 76%nat) + (V 79%nat)) mod 2 ^ 64)) mod 2 ^ 64) + 1) mod 2 ^ 64)
        /\ (((V 76%nat) + 1) mod 2 ^ 64) < (V 78%nat)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + ((V 76%nat) + (V 79%nat))) ((V 80%nat) + 48))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G13 G14 G15 G16 G18 G19 G20 K0 pvzI8 K2 K3 pvzI9 K5 K6 K7 pvzI10 K9 pvzI11 K11 K12 K13 K14 K15 K16 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV76l; move HV76l before pvzI3; pose proof (proj2 pvzI3) as HV76r; move HV76r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV77l; move HV77l before pvzI4; pose proof (proj2 pvzI4) as HV77r; move HV77r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV78l; move HV78l before pvzI5; pose proof (proj2 pvzI5) as HV78r; move HV78r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV79l; move HV79l before pvzI6; pose proof (proj2 pvzI6) as HV79r; move HV79r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV80l; move HV80l before pvzI7; pose proof (proj2 pvzI7) as HV80r; move HV80r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K1l; move K1l before pvzI8; pose proof (proj2 pvzI8) as K1r; move K1r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K10l; move K10l before pvzI11; pose proof (proj2 pvzI11) as K10r; move K10r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K17l; move K17l before pvzI12; pose proof (proj2 pvzI12) as K17r; move K17r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K18l; move K18l before pvzI13; pose proof (proj2 pvzI13) as K18r; move K18r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K19l; move K19l before pvzI14; pose proof (proj2 pvzI14) as K19r; move K19r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K20l; move K20l before pvzI15; pose proof (proj2 pvzI15) as K20r; move K20r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K21l; move K21l before pvzI16; pose proof (proj2 pvzI16) as K21r; move K21r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_76 := V 76%nat) in *. set (vz_77 := V 77%nat) in *. set (vz_78 := V 78%nat) in *. set (vz_79 := V 79%nat) in *. set (vz_80 := V 80%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 76%nat => Z_to_bv 64 vz_76 | 77%nat => Z_to_bv 64 vz_77 | 78%nat => Z_to_bv 64 vz_78 | 79%nat => Z_to_bv 64 vz_79 | 80%nat => Z_to_bv 64 vz_80 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 76%nat => vz_76 | 77%nat => vz_77 | 78%nat => vz_78 | 79%nat => vz_79 | 80%nat => vz_80 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 81%nat. }
  assert (HR: regs_ok E PadoXL2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadoXL2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadoXL2.kn0).
  { unfold know_ok, PadoXL2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K14) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16) | clear - HV2l HV2r K1l K1r K14; lia | clear - HV2l HV2r K1l K1r K14; lia | exactA K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K14) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K14) | clear; lia | exact K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K1l K1r K14; lia | clear - HV2l HV2r K1l K1r K14; lia | clear - HV2l HV2r K1l K1r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K4l K4r K9 K16) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV77l HV77r K4l K4r K9 K16) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV77l HV77r K4l K4r K9 K16) | evalEk ZA ltac:(clear) | clear - HV77l HV77r K4l K4r K9 K16; lia | clear - HV77l HV77r K4l K4r K9 K16; lia | clear - HV77l HV77r K4l K4r K9 K16; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV77l HV77r K4l K4r K9 K16) | evalEk ZA ltac:(clear - HV80l HV80r K8l K8r) | clear - HV77l HV77r K4l K4r K9 K16; lia | clear - HV77l HV77r K4l K4r K9 K16; lia | byte_tac ltac:(clear - HV80l HV80r K8l K8r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV80l HV80r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV77l HV77r K4l K4r K9 K16) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r; lia | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV77l HV77r K4l K4r K9 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K10l K10r K18l K18r K21l K21r K13 K14 K15 K16) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K10l K10r K19l K19r K21l K21r K13 K14 K15 K16) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K10l K10r K19l K19r K21l K21r K13 K14 K15 K16 HV79l HV79r K18l K18r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadoXL2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadoXL2.NX0 with 100%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_33 + (vz_76 + vz_79)) + 0) <= bv_unsigned a < ((vz_33 + (vz_76 + vz_79)) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadoXL2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadoXL2.ps0) with 0xb4910 in Hms. change (SR.ps_regs PadoXL2.ps0) with (map (fun i => (i, nth i PadoXL2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoXL2.ps0) with PadoXL2.cells0 in Hcells. unfold PadoXL2.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXL2.regs0 PadoXL2.regs_out0 100 KS_adoXL2_0 KS_adoXL2_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoXL2.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out0]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r) | evalEk' ZA Hag ltac:(clear - HV80l HV80r K8l K8r) | byte_tac ltac:(clear - HV80l HV80r K8l K8r) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PadoXL2.ps1) with 0xb46b0 in Hms. change (SR.ps_regs PadoXL2.ps1) with (map (fun i => (i, nth i PadoXL2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoXL2.ps1) with PadoXL2.cells1 in Hcells. unfold PadoXL2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXL2.regs0 PadoXL2.regs_out1 100 KS_adoXL2_1 KS_adoXL2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoXL2.regs_out1 E' R' 5 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out1 E' R' 17 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out1]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r) | evalEk' ZA Hag ltac:(clear - HV80l HV80r K8l K8r) | byte_tac ltac:(clear - HV80l HV80r K8l K8r) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right.
    change (SR.ps_pc PadoXL2.ps2) with 0xb46b0 in Hms. change (SR.ps_regs PadoXL2.ps2) with (map (fun i => (i, nth i PadoXL2.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoXL2.ps2) with PadoXL2.cells2 in Hcells. unfold PadoXL2.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoXL2.regs0 PadoXL2.regs_out2 100 KS_adoXL2_2 KS_adoXL2_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoXL2.regs_out2 E' R' 5 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out2 E' R' 13 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out2 E' R' 14 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out2 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out2 E' R' 17 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out2]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out2 E' R' 23 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out2]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadoXL2.regs_out2 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoXL2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K17l K17r K13 K14 K15 K16 HV76l HV76r K19l K19r K21l K21r HV79l HV79r K18l K18r) | evalEk' ZA Hag ltac:(clear - HV80l HV80r K8l K8r) | byte_tac ltac:(clear - HV80l HV80r K8l K8r) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

End PNADOP3.
