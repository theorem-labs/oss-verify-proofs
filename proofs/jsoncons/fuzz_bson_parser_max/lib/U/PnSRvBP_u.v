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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_vlBi0_u LibSegBs_vlBi1_u LibSegBs_vlBi2_u LibSegBs_vlBi3_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRVBP.
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
Module PvlBi0 := LibSegBs_vlBi0_u.
Definition KS_vlBi0 : list nat := Eval vm_compute in (BG.kept_list 72 PvlBi0.regs0 PvlBi0.regs_out0).
Lemma KS_vlBi0_ok : BG.kept_ok 72 PvlBi0.regs0 PvlBi0.regs_out0 KS_vlBi0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlBi0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x378c0 M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_vlBi0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 227540
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 12) = Z_to_bv 64 4
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 33%nat) + 16)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 pvzI5 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlBi0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlBi0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlBi0.kn0).
  { unfold know_ok, PvlBi0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlBi0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlBi0.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlBi0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlBi0.ps0) with 0x370d0 in Hms. change (SR.ps_regs PvlBi0.ps0) with (map (fun i => (i, nth i PvlBi0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlBi0.ps0) with PvlBi0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlBi0.regs0 PvlBi0.regs_out0 72 KS_vlBi0 KS_vlBi0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlBi0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlBi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlBi0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlBi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlBi0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlBi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlBi0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlBi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlBi0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PvlBi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlBi1 := LibSegBs_vlBi1_u.
Definition KS_vlBi1_0 : list nat := Eval vm_compute in (BG.kept_list 72 PvlBi1.regs0 PvlBi1.regs_out0).
Lemma KS_vlBi1_0_ok : BG.kept_ok 72 PvlBi1.regs0 PvlBi1.regs_out0 KS_vlBi1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vlBi1_1 : list nat := Eval vm_compute in (BG.kept_list 72 PvlBi1.regs0 PvlBi1.regs_out1).
Lemma KS_vlBi1_1_ok : BG.kept_ok 72 PvlBi1.regs0 PvlBi1.regs_out1 KS_vlBi1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vlBi1_2 : list nat := Eval vm_compute in (BG.kept_list 72 PvlBi1.regs0 PvlBi1.regs_out2).
Lemma KS_vlBi1_2_ok : BG.kept_ok 72 PvlBi1.regs0 PvlBi1.regs_out2 KS_vlBi1_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlBi1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 16) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 51%nat) -> 4136 <= (V 51%nat) <= 140737488355328 ->
  aligned (V 51%nat) 8 -> (((V 2%nat) - 176) + 176 <= ((V 51%nat) - 40) \/ ((V 51%nat) - 40) + 40 <= ((V 2%nat) - 176)) -> (((V 51%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 51%nat) - 40)) ->
  (((V 51%nat) - 40) + 40 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= 65536 \/ 65536 + 897024 <= ((V 51%nat) - 40)) -> L5.u64_at RSEGS M ((V 51%nat) - 24) (V 52%nat) -> L5.writable RSEGS M ((V 51%nat) - 24) 8 ->
  L5.defined M ((V 2%nat) - 80) 4 -> 0 <= (V 50%nat) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) - 24) <= bv_unsigned a < ((V 51%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) - 24) <= i < ((V 51%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x378d4 M) (st fx' R' 0x36ee4 M')
        /\ (forall x, In x KS_vlBi1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 227072
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ bv_unsigned (getr R' (reg 12)) = (((V 50%nat) + (V 52%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 4
        /\ 1 <= (((V 50%nat) - 4) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x378d4 M) (st fx' R' 0x37da8 M')
        /\ (forall x, In x KS_vlBi1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 51%nat)
        /\ bv_unsigned (getr R' (reg 12)) = (((V 50%nat) + (V 52%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 4
        /\ (((V 50%nat) - 4) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x378d4 M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_vlBi1_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 227612
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 4
        /\ (((V 50%nat) - 4) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G20 pvzI8 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV52l; move HV52l before pvzI7; pose proof (proj2 pvzI7) as HV52r; move HV52r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K17l; move K17l before pvzI11; pose proof (proj2 pvzI11) as K17r; move K17r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PvlBi1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlBi1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlBi1.kn0).
  { unfold know_ok, PvlBi1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear - HV33l HV33r K3l K3r K5 K10; lia | clear - HV33l HV33r K3l K3r K5 K10; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlBi1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlBi1.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 - 24) <= bv_unsigned a < (vz_51 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvlBi1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PvlBi1.ps0) with 0x36ee4 in Hms. change (SR.ps_regs PvlBi1.ps0) with (map (fun i => (i, nth i PvlBi1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlBi1.ps0) with PvlBi1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlBi1.regs0 PvlBi1.regs_out0 72 KS_vlBi1_0 KS_vlBi1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlBi1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlBi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlBi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlBi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlBi1.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PvlBi1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlBi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PvlBi1.ps1) with 0x37da8 in Hms. change (SR.ps_regs PvlBi1.ps1) with (map (fun i => (i, nth i PvlBi1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlBi1.ps1) with PvlBi1.cells1 in Hcells. unfold PvlBi1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlBi1.regs0 PvlBi1.regs_out1 72 KS_vlBi1_1 KS_vlBi1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlBi1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlBi1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi1.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlBi1.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PvlBi1.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlBi1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PvlBi1.ps2) with 0x370d0 in Hms. change (SR.ps_regs PvlBi1.ps2) with (map (fun i => (i, nth i PvlBi1.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlBi1.ps2) with PvlBi1.cells2 in Hcells. unfold PvlBi1.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlBi1.regs0 PvlBi1.regs_out2 72 KS_vlBi1_2 KS_vlBi1_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlBi1.regs_out2 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlBi1.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi1.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlBi1.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi1.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlBi1.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi1.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlBi1.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi1.regs_out2 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlBi1.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlBi2 := LibSegBs_vlBi2_u.
Definition KS_vlBi2_0 : list nat := Eval vm_compute in (BG.kept_list 72 PvlBi2.regs0 PvlBi2.regs_out0).
Lemma KS_vlBi2_0_ok : BG.kept_ok 72 PvlBi2.regs0 PvlBi2.regs_out0 KS_vlBi2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vlBi2_1 : list nat := Eval vm_compute in (BG.kept_list 72 PvlBi2.regs0 PvlBi2.regs_out1).
Lemma KS_vlBi2_1_ok : BG.kept_ok 72 PvlBi2.regs0 PvlBi2.regs_out1 KS_vlBi2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlBi2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 59%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 16) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 51%nat) -> 4136 <= (V 51%nat) <= 140737488355328 ->
  aligned (V 51%nat) 8 -> (((V 2%nat) - 176) + 176 <= ((V 51%nat) - 40) \/ ((V 51%nat) - 40) + 40 <= ((V 2%nat) - 176)) -> (((V 51%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 51%nat) - 40)) ->
  (((V 51%nat) - 40) + 40 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= 65536 \/ 65536 + 897024 <= ((V 51%nat) - 40)) -> L5.u64_at RSEGS M ((V 51%nat) - 24) (V 52%nat) -> L5.writable RSEGS M ((V 51%nat) - 24) 8 ->
  0 <= (V 50%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) - 24) <= bv_unsigned a < ((V 51%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) - 24) <= i < ((V 51%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3791c M) (st fx' R' 0x36ee4 M')
        /\ (forall x, In x KS_vlBi2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 227072
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ bv_unsigned (getr R' (reg 12)) = (((V 50%nat) + (V 52%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ 1 <= (((V 50%nat) - 1) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x3791c M) (st fx' R' 0x38984 M')
        /\ (forall x, In x KS_vlBi2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 227676
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 320)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ (((V 50%nat) - 1) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G18 G19 G20 pvzI9 K1 K2 pvzI10 K4 K5 K6 pvzI11 K8 K9 K10 K11 K12 K13 K14 K15 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV52l; move HV52l before pvzI7; pose proof (proj2 pvzI7) as HV52r; move HV52r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV59l; move HV59l before pvzI8; pose proof (proj2 pvzI8) as HV59r; move HV59r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K16l; move K16l before pvzI12; pose proof (proj2 pvzI12) as K16r; move K16r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_59 := V 59%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 59%nat => Z_to_bv 64 vz_59 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 59%nat => vz_59 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PvlBi2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlBi2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlBi2.kn0).
  { unfold know_ok, PvlBi2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear - HV33l HV33r K3l K3r K5 K10; lia | clear - HV33l HV33r K3l K3r K5 K10; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlBi2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlBi2.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 - 24) <= bv_unsigned a < (vz_51 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvlBi2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvlBi2.ps0) with 0x36ee4 in Hms. change (SR.ps_regs PvlBi2.ps0) with (map (fun i => (i, nth i PvlBi2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlBi2.ps0) with PvlBi2.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlBi2.regs0 PvlBi2.regs_out0 72 KS_vlBi2_0 KS_vlBi2_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlBi2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlBi2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlBi2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlBi2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlBi2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PvlBi2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlBi2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  - right.
    change (SR.ps_pc PvlBi2.ps1) with 0x38984 in Hms. change (SR.ps_regs PvlBi2.ps1) with (map (fun i => (i, nth i PvlBi2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlBi2.ps1) with PvlBi2.cells1 in Hcells. unfold PvlBi2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlBi2.regs0 PvlBi2.regs_out1 72 KS_vlBi2_1 KS_vlBi2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlBi2.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlBi2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi2.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlBi2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi2.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlBi2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi2.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlBi2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi2.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlBi2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlBi3 := LibSegBs_vlBi3_u.
Definition KS_vlBi3_0 : list nat := Eval vm_compute in (BG.kept_list 72 PvlBi3.regs0 PvlBi3.regs_out0).
Lemma KS_vlBi3_0_ok : BG.kept_ok 72 PvlBi3.regs0 PvlBi3.regs_out0 KS_vlBi3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vlBi3_1 : list nat := Eval vm_compute in (BG.kept_list 72 PvlBi3.regs0 PvlBi3.regs_out1).
Lemma KS_vlBi3_1_ok : BG.kept_ok 72 PvlBi3.regs0 PvlBi3.regs_out1 KS_vlBi3_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlBi3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 61%nat) -> getr R (reg 11) = Z_to_bv 64 (V 62%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 59%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 16) ->
  140735332483264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 51%nat) -> 4136 <= (V 51%nat) <= 140737488355328 ->
  aligned (V 51%nat) 8 -> (((V 2%nat) - 176) + 176 <= ((V 51%nat) - 40) \/ ((V 51%nat) - 40) + 40 <= ((V 2%nat) - 176)) -> (((V 51%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 51%nat) - 40)) ->
  (((V 51%nat) - 40) + 40 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= 65536 \/ 65536 + 897024 <= ((V 51%nat) - 40)) -> L5.u64_at RSEGS M ((V 51%nat) - 24) (V 52%nat) -> L5.writable RSEGS M ((V 51%nat) - 24) 8 ->
  140735332483248 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 176)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.defined M ((V 2%nat) - 96) 1 ->
  (((V 2%nat) - 112) + 16 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> (((V 2%nat) - 112) + 16 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> (((V 2%nat) - 112) + 16 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 2%nat) - 112)) -> (((V 2%nat) - 112) + 16 <= ((V 51%nat) - 40) \/ ((V 51%nat) - 40) + 40 <= ((V 2%nat) - 112)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) - 24) <= bv_unsigned a < ((V 51%nat) - 24) + 8) -> ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 16) -> ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) - 24) <= i < ((V 51%nat) - 24) + 8) -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 16) -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3795c M) (st fx' R' 0x36ee4 M')
        /\ (forall x, In x KS_vlBi3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 227072
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ 1 <= (((V 62%nat) - (V 59%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (V 52%nat))
      \/ (msteps RSEGS (st fx R 0x3795c M) (st fx' R' 0x37d74 M')
        /\ (forall x, In x KS_vlBi3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 228704
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 216356
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 228704
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 59%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 52%nat) + (V 59%nat)) mod 2 ^ 64)
        /\ (((V 62%nat) - (V 59%nat)) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G18 G19 G20 pvzI10 K1 K2 pvzI11 K4 K5 K6 pvzI12 K8 K9 K10 K11 K12 K13 K14 K15 pvzI13 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV52l; move HV52l before pvzI6; pose proof (proj2 pvzI6) as HV52r; move HV52r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV59l; move HV59l before pvzI7; pose proof (proj2 pvzI7) as HV59r; move HV59r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 59%nat => Z_to_bv 64 vz_59 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 51%nat => vz_51 | 52%nat => vz_52 | 59%nat => vz_59 | 61%nat => vz_61 | 62%nat => vz_62 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E PvlBi3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlBi3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlBi3.kn0).
  { unfold know_ok, PvlBi3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27; lia | clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27; lia | clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21 K24) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21 K24) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | clear - HV33l HV33r K3l K3r K5 K10 K21 K24; lia | clear - HV33l HV33r K3l K3r K5 K10 K21 K24; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21 K24) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21 K25) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12 K26) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21 K25) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21 K25) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21 K25) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21 K25) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K11 K16l K16r K18 K21 K25; lia | clear - HV34l HV34r K11 K16l K16r K18 K21 K25; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21 K25) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21 K24) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K10 K21 K24; lia | clear - HV33l HV33r K3l K3r K5 K10 K21 K24; lia | byte_tac ltac:(clear) | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27; lia | clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27; lia | clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21 K24) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlBi3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlBi3.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 - 24) <= bv_unsigned a < (vz_51 - 24) + 8) -> ~ ((vz_2 - 64) <= bv_unsigned a < (vz_2 - 64) + 16) -> ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 16) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PvlBi3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvlBi3.ps0) with 0x36ee4 in Hms. change (SR.ps_regs PvlBi3.ps0) with (map (fun i => (i, nth i PvlBi3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlBi3.ps0) with PvlBi3.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlBi3.regs0 PvlBi3.regs_out0 72 KS_vlBi3_0 KS_vlBi3_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlBi3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlBi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlBi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlBi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. 
  - right.
    change (SR.ps_pc PvlBi3.ps1) with 0x37d74 in Hms. change (SR.ps_regs PvlBi3.ps1) with (map (fun i => (i, nth i PvlBi3.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlBi3.ps1) with PvlBi3.cells1 in Hcells. unfold PvlBi3.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlBi3.regs0 PvlBi3.regs_out1 72 KS_vlBi3_1 KS_vlBi3_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlBi3.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlBi3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi3.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlBi3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi3.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlBi3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi3.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlBi3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi3.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlBi3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi3.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PvlBi3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlBi3.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PvlBi3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk' ZA Hag ltac:(clear - HV59l HV59r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18 K24 K25 K26 K27) | evalEk' ZA Hag ltac:(clear - HV61l HV61r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 K27) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

End PNSRVBP.
