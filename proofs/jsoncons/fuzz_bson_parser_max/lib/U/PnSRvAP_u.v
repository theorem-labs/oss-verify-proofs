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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_vlA1_u LibSegBs_vlB1_u LibSegBs_vlA9_u LibSegBs_vlB9_u LibSegBs_vlA16_u LibSegBs_vlB16_u LibSegBs_vlA17_u LibSegBs_vlB17_u LibSegBs_vlA18_u LibSegBs_vlB18_u LibSegBs_vlA8_u LibSegBs_vlB8_u LibSegBs_vlN6_u LibSegBs_vlN10_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRVAP.
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
Module PvlA1 := LibSegBs_vlA1_u.
Definition KS_vlA1 : list nat := Eval vm_compute in (BG.kept_list 72 PvlA1.regs0 PvlA1.regs_out0).
Lemma KS_vlA1_ok : BG.kept_ok 72 PvlA1.regs0 PvlA1.regs_out0 KS_vlA1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlA1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3763c M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_vlA1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 226892
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 12) = Z_to_bv 64 8).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 pvzI5 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlA1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlA1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlA1.kn0).
  { unfold know_ok, PvlA1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlA1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlA1.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlA1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlA1.ps0) with 0x370d0 in Hms. change (SR.ps_regs PvlA1.ps0) with (map (fun i => (i, nth i PvlA1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlA1.ps0) with PvlA1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlA1.regs0 PvlA1.regs_out0 72 KS_vlA1 KS_vlA1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlA1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlA1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlA1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlA1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlB1 := LibSegBs_vlB1_u.
Definition KS_vlB1_0 : list nat := Eval vm_compute in (BG.kept_list 72 PvlB1.regs0 PvlB1.regs_out0).
Lemma KS_vlB1_0_ok : BG.kept_ok 72 PvlB1.regs0 PvlB1.regs_out0 KS_vlB1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vlB1_1 : list nat := Eval vm_compute in (BG.kept_list 72 PvlB1.regs0 PvlB1.regs_out1).
Lemma KS_vlB1_1_ok : BG.kept_ok 72 PvlB1.regs0 PvlB1.regs_out1 KS_vlB1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlB1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 51%nat) -> 4136 <= (V 51%nat) <= 140737488355328 ->
  aligned (V 51%nat) 8 -> (((V 2%nat) - 176) + 176 <= ((V 51%nat) - 40) \/ ((V 51%nat) - 40) + 40 <= ((V 2%nat) - 176)) -> (((V 51%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 51%nat) - 40)) ->
  (((V 51%nat) - 40) + 40 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= 65536 \/ 65536 + 897024 <= ((V 51%nat) - 40)) -> L5.u64_at RSEGS M ((V 51%nat) - 24) (V 52%nat) -> L5.writable RSEGS M ((V 51%nat) - 24) 8 ->
  140735332483248 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 176)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.defined M ((V 2%nat) - 64) 8 ->
  0 <= (V 50%nat) <= 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) - 24) <= bv_unsigned a < ((V 51%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) - 24) <= i < ((V 51%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3764c M) (st fx' R' 0x37d98 M')
        /\ (forall x, In x KS_vlB1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 51%nat)
        /\ bv_unsigned (getr R' (reg 12)) = (((V 50%nat) + (V 52%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 8
        /\ 1 <= (((V 50%nat) - 8) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x3764c M) (st fx' R' 0x37d74 M')
        /\ (forall x, In x KS_vlB1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 226972
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 216240
        /\ (((V 50%nat) - 8) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 pvzI8 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 K13 K14 K15 pvzI11 K17 K18 K19 K20 K21 K22 K23 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV52l; move HV52l before pvzI7; pose proof (proj2 pvzI7) as HV52r; move HV52r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K24l; move K24l before pvzI12; pose proof (proj2 pvzI12) as K24r; move K24r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PvlB1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlB1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlB1.kn0).
  { unfold know_ok, PvlB1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K11 K16l K16r K18 K21; lia | clear - HV34l HV34r K11 K16l K16r K18 K21; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | byte_tac ltac:(clear) | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlB1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlB1.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 - 24) <= bv_unsigned a < (vz_51 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvlB1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvlB1.ps0) with 0x37d98 in Hms. change (SR.ps_regs PvlB1.ps0) with (map (fun i => (i, nth i PvlB1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlB1.ps0) with PvlB1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlB1.regs0 PvlB1.regs_out0 72 KS_vlB1_0 KS_vlB1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlB1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlB1.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PvlB1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  - right.
    change (SR.ps_pc PvlB1.ps1) with 0x37d74 in Hms. change (SR.ps_regs PvlB1.ps1) with (map (fun i => (i, nth i PvlB1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlB1.ps1) with PvlB1.cells1 in Hcells. unfold PvlB1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlB1.regs0 PvlB1.regs_out1 72 KS_vlB1_1 KS_vlB1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlB1.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlB1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB1.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlB1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlB1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB1.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlB1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB1.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlB1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB1.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PvlB1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlA9 := LibSegBs_vlA9_u.
Definition KS_vlA9 : list nat := Eval vm_compute in (BG.kept_list 72 PvlA9.regs0 PvlA9.regs_out0).
Lemma KS_vlA9_ok : BG.kept_ok 72 PvlA9.regs0 PvlA9.regs_out0 KS_vlA9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlA9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x37804 M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_vlA9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 227348
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 12) = Z_to_bv 64 8).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 pvzI5 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlA9.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlA9.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlA9.kn0).
  { unfold know_ok, PvlA9.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlA9.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlA9.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlA9.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlA9.ps0) with 0x370d0 in Hms. change (SR.ps_regs PvlA9.ps0) with (map (fun i => (i, nth i PvlA9.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlA9.ps0) with PvlA9.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlA9.regs0 PvlA9.regs_out0 72 KS_vlA9 KS_vlA9_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlA9.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlA9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlA9.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlA9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlA9.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlA9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlA9.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlA9.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlB9 := LibSegBs_vlB9_u.
Definition KS_vlB9_0 : list nat := Eval vm_compute in (BG.kept_list 72 PvlB9.regs0 PvlB9.regs_out0).
Lemma KS_vlB9_0_ok : BG.kept_ok 72 PvlB9.regs0 PvlB9.regs_out0 KS_vlB9_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vlB9_1 : list nat := Eval vm_compute in (BG.kept_list 72 PvlB9.regs0 PvlB9.regs_out1).
Lemma KS_vlB9_1_ok : BG.kept_ok 72 PvlB9.regs0 PvlB9.regs_out1 KS_vlB9_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlB9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 51%nat) -> 4136 <= (V 51%nat) <= 140737488355328 ->
  aligned (V 51%nat) 8 -> (((V 2%nat) - 176) + 176 <= ((V 51%nat) - 40) \/ ((V 51%nat) - 40) + 40 <= ((V 2%nat) - 176)) -> (((V 51%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 51%nat) - 40)) ->
  (((V 51%nat) - 40) + 40 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= 65536 \/ 65536 + 897024 <= ((V 51%nat) - 40)) -> L5.u64_at RSEGS M ((V 51%nat) - 24) (V 52%nat) -> L5.writable RSEGS M ((V 51%nat) - 24) 8 ->
  140735332483248 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 176)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.defined M ((V 2%nat) - 64) 8 ->
  0 <= (V 50%nat) <= 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) - 24) <= bv_unsigned a < ((V 51%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) - 24) <= i < ((V 51%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x37814 M) (st fx' R' 0x37d98 M')
        /\ (forall x, In x KS_vlB9_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 51%nat)
        /\ bv_unsigned (getr R' (reg 12)) = (((V 50%nat) + (V 52%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 8
        /\ 1 <= (((V 50%nat) - 8) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x37814 M) (st fx' R' 0x37d74 M')
        /\ (forall x, In x KS_vlB9_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 228704
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 6
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 216232
        /\ (((V 50%nat) - 8) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 pvzI8 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 K13 K14 K15 pvzI11 K17 K18 K19 K20 K21 K22 K23 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV52l; move HV52l before pvzI7; pose proof (proj2 pvzI7) as HV52r; move HV52r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K24l; move K24l before pvzI12; pose proof (proj2 pvzI12) as K24r; move K24r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PvlB9.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlB9.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlB9.kn0).
  { unfold know_ok, PvlB9.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K11 K16l K16r K18 K21; lia | clear - HV34l HV34r K11 K16l K16r K18 K21; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | byte_tac ltac:(clear) | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlB9.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlB9.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 - 24) <= bv_unsigned a < (vz_51 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvlB9.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvlB9.ps0) with 0x37d98 in Hms. change (SR.ps_regs PvlB9.ps0) with (map (fun i => (i, nth i PvlB9.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlB9.ps0) with PvlB9.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlB9.regs0 PvlB9.regs_out0 72 KS_vlB9_0 KS_vlB9_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlB9.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlB9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB9.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlB9.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PvlB9.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlB9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  - right.
    change (SR.ps_pc PvlB9.ps1) with 0x37d74 in Hms. change (SR.ps_regs PvlB9.ps1) with (map (fun i => (i, nth i PvlB9.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlB9.ps1) with PvlB9.cells1 in Hcells. unfold PvlB9.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlB9.regs0 PvlB9.regs_out1 72 KS_vlB9_1 KS_vlB9_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlB9.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlB9.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB9.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlB9.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB9.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlB9.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB9.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlB9.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB9.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlB9.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB9.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PvlB9.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB9.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PvlB9.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlA16 := LibSegBs_vlA16_u.
Definition KS_vlA16 : list nat := Eval vm_compute in (BG.kept_list 72 PvlA16.regs0 PvlA16.regs_out0).
Lemma KS_vlA16_ok : BG.kept_ok 72 PvlA16.regs0 PvlA16.regs_out0 KS_vlA16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlA16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x37b34 M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_vlA16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 228164
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 12) = Z_to_bv 64 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 pvzI5 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlA16.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlA16.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlA16.kn0).
  { unfold know_ok, PvlA16.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlA16.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlA16.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlA16.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlA16.ps0) with 0x370d0 in Hms. change (SR.ps_regs PvlA16.ps0) with (map (fun i => (i, nth i PvlA16.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlA16.ps0) with PvlA16.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlA16.regs0 PvlA16.regs_out0 72 KS_vlA16 KS_vlA16_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlA16.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlA16.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlA16.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlA16.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlB16 := LibSegBs_vlB16_u.
Definition KS_vlB16_0 : list nat := Eval vm_compute in (BG.kept_list 72 PvlB16.regs0 PvlB16.regs_out0).
Lemma KS_vlB16_0_ok : BG.kept_ok 72 PvlB16.regs0 PvlB16.regs_out0 KS_vlB16_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vlB16_1 : list nat := Eval vm_compute in (BG.kept_list 72 PvlB16.regs0 PvlB16.regs_out1).
Lemma KS_vlB16_1_ok : BG.kept_ok 72 PvlB16.regs0 PvlB16.regs_out1 KS_vlB16_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlB16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 51%nat) -> 4136 <= (V 51%nat) <= 140737488355328 ->
  aligned (V 51%nat) 8 -> (((V 2%nat) - 176) + 176 <= ((V 51%nat) - 40) \/ ((V 51%nat) - 40) + 40 <= ((V 2%nat) - 176)) -> (((V 51%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 51%nat) - 40)) ->
  (((V 51%nat) - 40) + 40 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= 65536 \/ 65536 + 897024 <= ((V 51%nat) - 40)) -> L5.u64_at RSEGS M ((V 51%nat) - 24) (V 52%nat) -> L5.writable RSEGS M ((V 51%nat) - 24) 8 ->
  140735332483248 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 176)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.defined M ((V 2%nat) - 64) 4 ->
  0 <= (V 50%nat) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) - 24) <= bv_unsigned a < ((V 51%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) - 24) <= i < ((V 51%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x37b44 M) (st fx' R' 0x37d98 M')
        /\ (forall x, In x KS_vlB16_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 51%nat)
        /\ bv_unsigned (getr R' (reg 12)) = (((V 50%nat) + (V 52%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 4
        /\ 1 <= (((V 50%nat) - 4) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x37b44 M) (st fx' R' 0x37d74 M')
        /\ (forall x, In x KS_vlB16_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 228704
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 216232
        /\ (((V 50%nat) - 4) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 pvzI8 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 K13 K14 K15 pvzI11 K17 K18 K19 K20 K21 K22 K23 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV52l; move HV52l before pvzI7; pose proof (proj2 pvzI7) as HV52r; move HV52r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K24l; move K24l before pvzI12; pose proof (proj2 pvzI12) as K24r; move K24r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PvlB16.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlB16.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlB16.kn0).
  { unfold know_ok, PvlB16.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K11 K16l K16r K18 K21; lia | clear - HV34l HV34r K11 K16l K16r K18 K21; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | byte_tac ltac:(clear) | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlB16.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlB16.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 - 24) <= bv_unsigned a < (vz_51 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvlB16.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvlB16.ps0) with 0x37d98 in Hms. change (SR.ps_regs PvlB16.ps0) with (map (fun i => (i, nth i PvlB16.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlB16.ps0) with PvlB16.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlB16.regs0 PvlB16.regs_out0 72 KS_vlB16_0 KS_vlB16_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlB16.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlB16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB16.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlB16.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PvlB16.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlB16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  - right.
    change (SR.ps_pc PvlB16.ps1) with 0x37d74 in Hms. change (SR.ps_regs PvlB16.ps1) with (map (fun i => (i, nth i PvlB16.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlB16.ps1) with PvlB16.cells1 in Hcells. unfold PvlB16.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlB16.regs0 PvlB16.regs_out1 72 KS_vlB16_1 KS_vlB16_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlB16.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlB16.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB16.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlB16.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB16.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlB16.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB16.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlB16.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB16.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlB16.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB16.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PvlB16.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB16.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PvlB16.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlA17 := LibSegBs_vlA17_u.
Definition KS_vlA17 : list nat := Eval vm_compute in (BG.kept_list 72 PvlA17.regs0 PvlA17.regs_out0).
Lemma KS_vlA17_ok : BG.kept_ok 72 PvlA17.regs0 PvlA17.regs_out0 KS_vlA17 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlA17_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x37b84 M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_vlA17 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 228244
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 12) = Z_to_bv 64 8).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 pvzI5 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlA17.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlA17.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlA17.kn0).
  { unfold know_ok, PvlA17.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlA17.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlA17.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlA17.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlA17.ps0) with 0x370d0 in Hms. change (SR.ps_regs PvlA17.ps0) with (map (fun i => (i, nth i PvlA17.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlA17.ps0) with PvlA17.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlA17.regs0 PvlA17.regs_out0 72 KS_vlA17 KS_vlA17_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlA17.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlA17.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlA17.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlA17.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlA17.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlA17.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlA17.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlA17.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlB17 := LibSegBs_vlB17_u.
Definition KS_vlB17_0 : list nat := Eval vm_compute in (BG.kept_list 72 PvlB17.regs0 PvlB17.regs_out0).
Lemma KS_vlB17_0_ok : BG.kept_ok 72 PvlB17.regs0 PvlB17.regs_out0 KS_vlB17_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vlB17_1 : list nat := Eval vm_compute in (BG.kept_list 72 PvlB17.regs0 PvlB17.regs_out1).
Lemma KS_vlB17_1_ok : BG.kept_ok 72 PvlB17.regs0 PvlB17.regs_out1 KS_vlB17_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlB17_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 51%nat) -> 4136 <= (V 51%nat) <= 140737488355328 ->
  aligned (V 51%nat) 8 -> (((V 2%nat) - 176) + 176 <= ((V 51%nat) - 40) \/ ((V 51%nat) - 40) + 40 <= ((V 2%nat) - 176)) -> (((V 51%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 51%nat) - 40)) ->
  (((V 51%nat) - 40) + 40 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= 65536 \/ 65536 + 897024 <= ((V 51%nat) - 40)) -> L5.u64_at RSEGS M ((V 51%nat) - 24) (V 52%nat) -> L5.writable RSEGS M ((V 51%nat) - 24) 8 ->
  140735332483248 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 176)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.defined M ((V 2%nat) - 64) 8 ->
  0 <= (V 50%nat) <= 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) - 24) <= bv_unsigned a < ((V 51%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) - 24) <= i < ((V 51%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x37b94 M) (st fx' R' 0x37d98 M')
        /\ (forall x, In x KS_vlB17_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 51%nat)
        /\ bv_unsigned (getr R' (reg 12)) = (((V 50%nat) + (V 52%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 8
        /\ 1 <= (((V 50%nat) - 8) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x37b94 M) (st fx' R' 0x37d74 M')
        /\ (forall x, In x KS_vlB17_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 228704
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 216224
        /\ (((V 50%nat) - 8) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 pvzI8 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 K13 K14 K15 pvzI11 K17 K18 K19 K20 K21 K22 K23 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV52l; move HV52l before pvzI7; pose proof (proj2 pvzI7) as HV52r; move HV52r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K24l; move K24l before pvzI12; pose proof (proj2 pvzI12) as K24r; move K24r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PvlB17.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlB17.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlB17.kn0).
  { unfold know_ok, PvlB17.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K11 K16l K16r K18 K21; lia | clear - HV34l HV34r K11 K16l K16r K18 K21; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | byte_tac ltac:(clear) | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlB17.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlB17.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 - 24) <= bv_unsigned a < (vz_51 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvlB17.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvlB17.ps0) with 0x37d98 in Hms. change (SR.ps_regs PvlB17.ps0) with (map (fun i => (i, nth i PvlB17.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlB17.ps0) with PvlB17.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlB17.regs0 PvlB17.regs_out0 72 KS_vlB17_0 KS_vlB17_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlB17.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlB17.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB17.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlB17.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PvlB17.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlB17.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  - right.
    change (SR.ps_pc PvlB17.ps1) with 0x37d74 in Hms. change (SR.ps_regs PvlB17.ps1) with (map (fun i => (i, nth i PvlB17.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlB17.ps1) with PvlB17.cells1 in Hcells. unfold PvlB17.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlB17.regs0 PvlB17.regs_out1 72 KS_vlB17_1 KS_vlB17_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlB17.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlB17.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB17.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlB17.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB17.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlB17.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB17.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlB17.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB17.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlB17.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB17.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PvlB17.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB17.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PvlB17.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlA18 := LibSegBs_vlA18_u.
Definition KS_vlA18 : list nat := Eval vm_compute in (BG.kept_list 72 PvlA18.regs0 PvlA18.regs_out0).
Lemma KS_vlA18_ok : BG.kept_ok 72 PvlA18.regs0 PvlA18.regs_out0 KS_vlA18 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlA18_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x37708 M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_vlA18 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 227096
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 12) = Z_to_bv 64 8).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 pvzI5 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlA18.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlA18.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlA18.kn0).
  { unfold know_ok, PvlA18.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlA18.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlA18.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlA18.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlA18.ps0) with 0x370d0 in Hms. change (SR.ps_regs PvlA18.ps0) with (map (fun i => (i, nth i PvlA18.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlA18.ps0) with PvlA18.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlA18.regs0 PvlA18.regs_out0 72 KS_vlA18 KS_vlA18_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlA18.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlA18.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlA18.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlA18.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlA18.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlA18.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlA18.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlA18.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlB18 := LibSegBs_vlB18_u.
Definition KS_vlB18_0 : list nat := Eval vm_compute in (BG.kept_list 72 PvlB18.regs0 PvlB18.regs_out0).
Lemma KS_vlB18_0_ok : BG.kept_ok 72 PvlB18.regs0 PvlB18.regs_out0 KS_vlB18_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vlB18_1 : list nat := Eval vm_compute in (BG.kept_list 72 PvlB18.regs0 PvlB18.regs_out1).
Lemma KS_vlB18_1_ok : BG.kept_ok 72 PvlB18.regs0 PvlB18.regs_out1 KS_vlB18_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlB18_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 51%nat) -> 4136 <= (V 51%nat) <= 140737488355328 ->
  aligned (V 51%nat) 8 -> (((V 2%nat) - 176) + 176 <= ((V 51%nat) - 40) \/ ((V 51%nat) - 40) + 40 <= ((V 2%nat) - 176)) -> (((V 51%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 51%nat) - 40)) ->
  (((V 51%nat) - 40) + 40 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= 65536 \/ 65536 + 897024 <= ((V 51%nat) - 40)) -> L5.u64_at RSEGS M ((V 51%nat) - 24) (V 52%nat) -> L5.writable RSEGS M ((V 51%nat) - 24) 8 ->
  140735332483248 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 176)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.defined M ((V 2%nat) - 64) 8 ->
  0 <= (V 50%nat) <= 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) - 24) <= bv_unsigned a < ((V 51%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) - 24) <= i < ((V 51%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x37718 M) (st fx' R' 0x37d98 M')
        /\ (forall x, In x KS_vlB18_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 51%nat)
        /\ bv_unsigned (getr R' (reg 12)) = (((V 50%nat) + (V 52%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 8
        /\ 1 <= (((V 50%nat) - 8) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x37718 M) (st fx' R' 0x37d74 M')
        /\ (forall x, In x KS_vlB18_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 228704
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 216232
        /\ (((V 50%nat) - 8) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 pvzI8 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 K13 K14 K15 pvzI11 K17 K18 K19 K20 K21 K22 K23 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV52l; move HV52l before pvzI7; pose proof (proj2 pvzI7) as HV52r; move HV52r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K24l; move K24l before pvzI12; pose proof (proj2 pvzI12) as K24r; move K24r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PvlB18.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlB18.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlB18.kn0).
  { unfold know_ok, PvlB18.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K11 K16l K16r K18 K21; lia | clear - HV34l HV34r K11 K16l K16r K18 K21; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | byte_tac ltac:(clear) | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlB18.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlB18.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 - 24) <= bv_unsigned a < (vz_51 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvlB18.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvlB18.ps0) with 0x37d98 in Hms. change (SR.ps_regs PvlB18.ps0) with (map (fun i => (i, nth i PvlB18.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlB18.ps0) with PvlB18.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlB18.regs0 PvlB18.regs_out0 72 KS_vlB18_0 KS_vlB18_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlB18.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlB18.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB18.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlB18.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PvlB18.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlB18.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  - right.
    change (SR.ps_pc PvlB18.ps1) with 0x37d74 in Hms. change (SR.ps_regs PvlB18.ps1) with (map (fun i => (i, nth i PvlB18.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlB18.ps1) with PvlB18.cells1 in Hcells. unfold PvlB18.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlB18.regs0 PvlB18.regs_out1 72 KS_vlB18_1 KS_vlB18_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlB18.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlB18.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB18.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlB18.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB18.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlB18.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB18.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlB18.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB18.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlB18.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB18.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PvlB18.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB18.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PvlB18.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlA8 := LibSegBs_vlA8_u.
Definition KS_vlA8 : list nat := Eval vm_compute in (BG.kept_list 72 PvlA8.regs0 PvlA8.regs_out0).
Lemma KS_vlA8_ok : BG.kept_ok 72 PvlA8.regs0 PvlA8.regs_out0 KS_vlA8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlA8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x37aa4 M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_vlA8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 228020
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 12) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 pvzI5 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlA8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlA8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlA8.kn0).
  { unfold know_ok, PvlA8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlA8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlA8.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlA8.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlA8.ps0) with 0x370d0 in Hms. change (SR.ps_regs PvlA8.ps0) with (map (fun i => (i, nth i PvlA8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlA8.ps0) with PvlA8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlA8.regs0 PvlA8.regs_out0 72 KS_vlA8 KS_vlA8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlA8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlA8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlA8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlA8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlA8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlA8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlA8.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlA8.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlB8 := LibSegBs_vlB8_u.
Definition KS_vlB8_0 : list nat := Eval vm_compute in (BG.kept_list 72 PvlB8.regs0 PvlB8.regs_out0).
Lemma KS_vlB8_0_ok : BG.kept_ok 72 PvlB8.regs0 PvlB8.regs_out0 KS_vlB8_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vlB8_1 : list nat := Eval vm_compute in (BG.kept_list 72 PvlB8.regs0 PvlB8.regs_out1).
Lemma KS_vlB8_1_ok : BG.kept_ok 72 PvlB8.regs0 PvlB8.regs_out1 KS_vlB8_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlB8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 51%nat) -> 4136 <= (V 51%nat) <= 140737488355328 ->
  aligned (V 51%nat) 8 -> (((V 2%nat) - 176) + 176 <= ((V 51%nat) - 40) \/ ((V 51%nat) - 40) + 40 <= ((V 2%nat) - 176)) -> (((V 51%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 51%nat) - 40)) ->
  (((V 51%nat) - 40) + 40 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= 65536 \/ 65536 + 897024 <= ((V 51%nat) - 40)) -> L5.u64_at RSEGS M ((V 51%nat) - 24) (V 52%nat) -> L5.writable RSEGS M ((V 51%nat) - 24) 8 ->
  140735332483248 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 176)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.defined M ((V 2%nat) - 64) 1 ->
  0 <= (V 50%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) - 24) <= bv_unsigned a < ((V 51%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) - 24) <= i < ((V 51%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x37ab4 M) (st fx' R' 0x37d98 M')
        /\ (forall x, In x KS_vlB8_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 51%nat)
        /\ bv_unsigned (getr R' (reg 12)) = (((V 50%nat) + (V 52%nat)) mod 2 ^ 64)
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ 1 <= (((V 50%nat) - 1) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x37ab4 M) (st fx' R' 0x37d74 M')
        /\ (forall x, In x KS_vlB8_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 228104
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 216340
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ (((V 50%nat) - 1) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 pvzI8 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 K13 K14 K15 pvzI11 K17 K18 K19 K20 K21 K22 K23 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV52l; move HV52l before pvzI7; pose proof (proj2 pvzI7) as HV52r; move HV52r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K24l; move K24l before pvzI12; pose proof (proj2 pvzI12) as K24r; move K24r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PvlB8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlB8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlB8.kn0).
  { unfold know_ok, PvlB8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K11 K16l K16r K18 K21; lia | clear - HV34l HV34r K11 K16l K16r K18 K21; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11 K16l K16r K18 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | clear - HV33l HV33r K3l K3r K5 K10 K21; lia | byte_tac ltac:(clear) | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | clear - HV2l HV2r K0l K0r K5 K9 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlB8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlB8.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 - 24) <= bv_unsigned a < (vz_51 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvlB8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvlB8.ps0) with 0x37d98 in Hms. change (SR.ps_regs PvlB8.ps0) with (map (fun i => (i, nth i PvlB8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlB8.ps0) with PvlB8.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlB8.regs0 PvlB8.regs_out0 72 KS_vlB8_0 KS_vlB8_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlB8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlB8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB8.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlB8.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PvlB8.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvlB8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  - right.
    change (SR.ps_pc PvlB8.ps1) with 0x37d74 in Hms. change (SR.ps_regs PvlB8.ps1) with (map (fun i => (i, nth i PvlB8.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlB8.ps1) with PvlB8.cells1 in Hcells. unfold PvlB8.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlB8.regs0 PvlB8.regs_out1 72 KS_vlB8_1 KS_vlB8_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlB8.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlB8.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB8.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlB8.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB8.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlB8.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB8.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlB8.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB8.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PvlB8.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB8.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PvlB8.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlB8.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PvlB8.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlN6 := LibSegBs_vlN6_u.
Definition KS_vlN6 : list nat := Eval vm_compute in (BG.kept_list 72 PvlN6.regs0 PvlN6.regs_out0).
Lemma KS_vlN6_ok : BG.kept_ok 72 PvlN6.regs0 PvlN6.regs_out0 KS_vlN6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlN6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> 140735332483248 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 176) + 176 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 176)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u8_at RSEGS M ((V 33%nat) + 10) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x37a90 M) (st fx' R' 0x37d74 M')
        /\ (forall x, In x KS_vlN6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 228144
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 216332).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 pvzI5 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlN6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlN6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlN6.kn0).
  { unfold know_ok, PvlN6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8; lia | clear - HV2l HV2r K0l K0r K5 K8; lia | clear - HV2l HV2r K0l K0r K5 K8; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11; lia | clear - HV34l HV34r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11; lia | clear - HV33l HV33r K3l K3r K5 K11; lia | byte_tac ltac:(clear) | exactA K12]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlN6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlN6.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlN6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlN6.ps0) with 0x37d74 in Hms. change (SR.ps_regs PvlN6.ps0) with (map (fun i => (i, nth i PvlN6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlN6.ps0) with PvlN6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlN6.regs0 PvlN6.regs_out0 72 KS_vlN6 KS_vlN6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlN6.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlN6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlN6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlN6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlN6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlN6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlN6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlN6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlN6.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlN6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlN6.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvlN6.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlN10 := LibSegBs_vlN10_u.
Definition KS_vlN10 : list nat := Eval vm_compute in (BG.kept_list 72 PvlN10.regs0 PvlN10.regs_out0).
Lemma KS_vlN10_ok : BG.kept_ok 72 PvlN10.regs0 PvlN10.regs_out0 KS_vlN10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlN10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> 140735332483248 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 176) + 176 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 176)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u8_at RSEGS M ((V 33%nat) + 10) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x37b14 M) (st fx' R' 0x37d74 M')
        /\ (forall x, In x KS_vlN10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 228144
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 216332).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 pvzI5 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlN10.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlN10.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlN10.kn0).
  { unfold know_ok, PvlN10.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8; lia | clear - HV2l HV2r K0l K0r K5 K8; lia | clear - HV2l HV2r K0l K0r K5 K8; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11; lia | clear - HV34l HV34r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11; lia | clear - HV33l HV33r K3l K3r K5 K11; lia | byte_tac ltac:(clear) | exactA K12]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlN10.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlN10.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlN10.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlN10.ps0) with 0x37d74 in Hms. change (SR.ps_regs PvlN10.ps0) with (map (fun i => (i, nth i PvlN10.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlN10.ps0) with PvlN10.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlN10.regs0 PvlN10.regs_out0 72 KS_vlN10 KS_vlN10_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlN10.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlN10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlN10.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlN10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlN10.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlN10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlN10.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlN10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlN10.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlN10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlN10.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvlN10.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End PNSRVAP.
