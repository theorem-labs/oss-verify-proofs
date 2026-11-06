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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_075S9 BndP_Eb_079S9 BndP_Eb_082S9 BndP_Eb_081S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PECVALBRP1.
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

Module PbvrE00 := BndP_Eb_075S9.LibSegEb_bvrE00.
Definition KS_bvrE00 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrE00.regs0 PbvrE00.regs_out0).
Lemma KS_bvrE00_ok : BG.kept_ok 60 PbvrE00.regs0 PbvrE00.regs_out0 KS_bvrE00 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrE00_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 0 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487280 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 0 <= (V 33%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 104) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 104) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9cb4 M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrE00 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 G2 G10 G11 K0 K1 K2 pvzI3 K4 K5 pvzI4.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K3l; move K3l before pvzI3; pose proof (proj2 pvzI3) as K3r; move K3r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K6l; move K6l before pvzI4; pose proof (proj2 pvzI4) as K6r; move K6r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 34%nat. }
  assert (HR: regs_ok E PbvrE00.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrE00.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrE00.kn0).
  { unfold know_ok, PbvrE00.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrE00.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrE00.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 104) <= bv_unsigned a < (vz_2 - 104) + 104) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbvrE00.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrE00.ps0) with 0xba060 in Hms. change (SR.ps_regs PbvrE00.ps0) with (map (fun i => (i, nth i PbvrE00.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrE00.ps0) with PbvrE00.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrE00.regs0 PbvrE00.regs_out0 60 KS_bvrE00 KS_bvrE00_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrE00.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbvrE00.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrE00.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrE00.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrE00.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbvrE00.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrE00.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbvrE00.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbvrE01 := BndP_Eb_075S9.LibSegEb_bvrE01.
Definition KS_bvrE01 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrE01.regs0 PbvrE01.regs_out0).
Lemma KS_bvrE01_ok : BG.kept_ok 60 PbvrE01.regs0 PbvrE01.regs_out0 KS_bvrE01 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrE01_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 0 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487280 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 1 <= (V 33%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 104) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 104) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9cb4 M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrE01 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 G2 G10 G11 K0 K1 K2 pvzI3 K4 K5 pvzI4.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K3l; move K3l before pvzI3; pose proof (proj2 pvzI3) as K3r; move K3r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K6l; move K6l before pvzI4; pose proof (proj2 pvzI4) as K6r; move K6r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 34%nat. }
  assert (HR: regs_ok E PbvrE01.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrE01.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrE01.kn0).
  { unfold know_ok, PbvrE01.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrE01.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrE01.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 104) <= bv_unsigned a < (vz_2 - 104) + 104) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbvrE01.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrE01.ps0) with 0xba060 in Hms. change (SR.ps_regs PbvrE01.ps0) with (map (fun i => (i, nth i PbvrE01.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrE01.ps0) with PbvrE01.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrE01.regs0 PbvrE01.regs_out0 60 KS_bvrE01 KS_bvrE01_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrE01.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbvrE01.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrE01.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrE01.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrE01.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbvrE01.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrE01.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbvrE01.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbvrEn := BndP_Eb_075S9.LibSegEb_bvrEn.
Definition KS_bvrEn : list nat := Eval vm_compute in (BG.kept_list 60 PbvrEn.regs0 PbvrEn.regs_out0).
Lemma KS_bvrEn_ok : BG.kept_ok 60 PbvrEn.regs0 PbvrEn.regs_out0 KS_bvrEn = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrEn_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487280 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108863 ->
  1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 104) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 104) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9cb4 M) (st fx' R' 0xb9d64 M')
        /\ (forall x, In x KS_bvrEn -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 5) = Z_to_bv 64 245
        /\ getr R' (reg 6) = Z_to_bv 64 2
        /\ getr R' (reg 7) = Z_to_bv 64 18446744073709551551
        /\ getr R' (reg 8) = Z_to_bv 64 159
        /\ getr R' (reg 9) = Z_to_bv 64 240
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 146708
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 8
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 18446744073709551554
        /\ getr R' (reg 18) = Z_to_bv 64 146077
        /\ getr R' (reg 19) = Z_to_bv 64 18446744073709405538
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 144
        /\ getr R' (reg 22) = Z_to_bv 64 244
        /\ getr R' (reg 23) = Z_to_bv 64 143
        /\ getr R' (reg 24) = Z_to_bv 64 3
        /\ getr R' (reg 28) = Z_to_bv 64 239
        /\ getr R' (reg 29) = Z_to_bv 64 224
        /\ getr R' (reg 30) = Z_to_bv 64 160
        /\ getr R' (reg 31) = Z_to_bv 64 237
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 K0 K1 K2 pvzI4 K4 K5 pvzI5 pvzI6 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K6l; move K6l before pvzI5; pose proof (proj2 pvzI5) as K6r; move K6r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K7l; move K7l before pvzI6; pose proof (proj2 pvzI6) as K7r; move K7r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K8l; move K8l before pvzI7; pose proof (proj2 pvzI7) as K8r; move K8r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PbvrEn.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrEn.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrEn.kn0).
  { unfold know_ok, PbvrEn.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8l K8r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K8l K8r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8l K8r HV35l HV35r K7l K7r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrEn.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrEn.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 104) <= bv_unsigned a < (vz_2 - 104) + 104) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbvrEn.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrEn.ps0) with 0xb9d64 in Hms. change (SR.ps_regs PbvrEn.ps0) with (map (fun i => (i, nth i PbvrEn.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrEn.ps0) with PbvrEn.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrEn.regs0 PbvrEn.regs_out0 60 KS_bvrEn KS_bvrEn_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 7 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 30 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrEn.regs_out0 E' R' 31 Hregs) by (clear; lia). cbn [nth PbvrEn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbvrHf := BndP_Eb_079S9.LibSegEb_bvrHf.
Definition KS_bvrHf_0 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrHf.regs0 PbvrHf.regs_out0).
Lemma KS_bvrHf_0_ok : BG.kept_ok 60 PbvrHf.regs0 PbvrHf.regs_out0 KS_bvrHf_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrHf_1 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrHf.regs0 PbvrHf.regs_out1).
Lemma KS_bvrHf_1_ok : BG.kept_ok 60 PbvrHf.regs0 PbvrHf.regs_out1 KS_bvrHf_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrHf_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb9d64 M) (st fx' R' 0xb9e78 M')
        /\ (forall x, In x KS_bvrHf_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb9d64 M) (st fx' R' 0xb9d8c M')
        /\ (forall x, In x KS_bvrHf_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PbvrHf.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrHf.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrHf.kn0).
  { unfold know_ok, PbvrHf.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrHf.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrHf.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrHf.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PbvrHf.ps0) with 0xb9e78 in Hms. change (SR.ps_regs PbvrHf.ps0) with (map (fun i => (i, nth i PbvrHf.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrHf.ps0) with PbvrHf.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrHf.regs0 PbvrHf.regs_out0 60 KS_bvrHf_0 KS_bvrHf_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrHf.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrHf.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PbvrHf.ps1) with 0xb9d8c in Hms. change (SR.ps_regs PbvrHf.ps1) with (map (fun i => (i, nth i PbvrHf.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrHf.ps1) with PbvrHf.cells1 in Hcells. unfold PbvrHf.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrHf.regs0 PbvrHf.regs_out1 60 KS_bvrHf_1 KS_bvrHf_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrHf.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrHf.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PbvrHs := BndP_Eb_079S9.LibSegEb_bvrHs.
Definition KS_bvrHs : list nat := Eval vm_compute in (BG.kept_list 60 PbvrHs.regs0 PbvrHs.regs_out0).
Lemma KS_bvrHs_ok : BG.kept_ok 60 PbvrHs.regs0 PbvrHs.regs_out0 KS_bvrHs = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrHs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9d64 M) (st fx' R' 0xb9e78 M')
        /\ (forall x, In x KS_bvrHs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI4 pvzI5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K1l; move K1l before pvzI5; pose proof (proj2 pvzI5) as K1r; move K1r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K2l; move K2l before pvzI6; pose proof (proj2 pvzI6) as K2r; move K2r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PbvrHs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrHs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrHs.kn0).
  { unfold know_ok, PbvrHs.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrHs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrHs.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrHs.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrHs.ps0) with 0xb9e78 in Hms. change (SR.ps_regs PbvrHs.ps0) with (map (fun i => (i, nth i PbvrHs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrHs.ps0) with PbvrHs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrHs.regs0 PbvrHs.regs_out0 60 KS_bvrHs KS_bvrHs_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PbvrHs.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrHs.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrSZ := BndP_Eb_082S9.LibSegEb_bvrSZ.
Definition KS_bvrSZ : list nat := Eval vm_compute in (BG.kept_list 60 PbvrSZ.regs0 PbvrSZ.regs_out0).
Lemma KS_bvrSZ_ok : BG.kept_ok 60 PbvrSZ.regs0 PbvrSZ.regs_out0 KS_bvrSZ = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrSZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 1 -> L5KA.zeros_at M 2147469139 33 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9e78 M) (st fx' R' 0xb9ea8 M')
        /\ (forall x, In x KS_bvrSZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) + 146077)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrSZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrSZ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrSZ.kn0).
  { unfold know_ok, PbvrSZ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrSZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrSZ.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrSZ.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrSZ.ps0) with 0xb9ea8 in Hms. change (SR.ps_regs PbvrSZ.ps0) with (map (fun i => (i, nth i PbvrSZ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrSZ.ps0) with PbvrSZ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrSZ.regs0 PbvrSZ.regs_out0 60 KS_bvrSZ KS_bvrSZ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrSZ.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrSZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrSZ.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrSZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvrSZ.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvrSZ.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrSP1 := BndP_Eb_081S9.LibSegEb_bvrSP1.
Definition KS_bvrSP1 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrSP1.regs0 PbvrSP1.regs_out0).
Lemma KS_bvrSP1_ok : BG.kept_ok 60 PbvrSP1.regs0 PbvrSP1.regs_out0 KS_bvrSP1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrSP1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 1 -> 0 <= Z.land (V 33%nat) 7 <= 0 -> L5KA.zeros_at M 2147469139 33 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9e78 M) (st fx' R' 0xb9ea8 M')
        /\ (forall x, In x KS_bvrSP1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) + 146077)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrSP1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrSP1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrSP1.kn0).
  { unfold know_ok, PbvrSP1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrSP1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrSP1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrSP1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrSP1.ps0) with 0xb9ea8 in Hms. change (SR.ps_regs PbvrSP1.ps0) with (map (fun i => (i, nth i PbvrSP1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrSP1.ps0) with PbvrSP1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrSP1.regs0 PbvrSP1.regs_out0 60 KS_bvrSP1 KS_bvrSP1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrSP1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrSP1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrSP1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrSP1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvrSP1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvrSP1.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrSP2 := BndP_Eb_081S9.LibSegEb_bvrSP2.
Definition KS_bvrSP2 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrSP2.regs0 PbvrSP2.regs_out0).
Lemma KS_bvrSP2_ok : BG.kept_ok 60 PbvrSP2.regs0 PbvrSP2.regs_out0 KS_bvrSP2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrSP2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 2 -> 0 <= Z.land (V 33%nat) 7 <= 1 -> L5KA.zeros_at M 2147469139 33 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9e78 M) (st fx' R' 0xb9ea8 M')
        /\ (forall x, In x KS_bvrSP2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) + 146077)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrSP2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrSP2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrSP2.kn0).
  { unfold know_ok, PbvrSP2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrSP2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrSP2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrSP2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrSP2.ps0) with 0xb9ea8 in Hms. change (SR.ps_regs PbvrSP2.ps0) with (map (fun i => (i, nth i PbvrSP2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrSP2.ps0) with PbvrSP2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrSP2.regs0 PbvrSP2.regs_out0 60 KS_bvrSP2 KS_bvrSP2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrSP2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrSP2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrSP2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrSP2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvrSP2.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvrSP2.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrSP3 := BndP_Eb_081S9.LibSegEb_bvrSP3.
Definition KS_bvrSP3 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrSP3.regs0 PbvrSP3.regs_out0).
Lemma KS_bvrSP3_ok : BG.kept_ok 60 PbvrSP3.regs0 PbvrSP3.regs_out0 KS_bvrSP3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrSP3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 3 -> 0 <= Z.land (V 33%nat) 7 <= 2 -> L5KA.zeros_at M 2147469139 33 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9e78 M) (st fx' R' 0xb9ea8 M')
        /\ (forall x, In x KS_bvrSP3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) + 146077)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrSP3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrSP3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrSP3.kn0).
  { unfold know_ok, PbvrSP3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrSP3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrSP3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrSP3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrSP3.ps0) with 0xb9ea8 in Hms. change (SR.ps_regs PbvrSP3.ps0) with (map (fun i => (i, nth i PbvrSP3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrSP3.ps0) with PbvrSP3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrSP3.regs0 PbvrSP3.regs_out0 60 KS_bvrSP3 KS_bvrSP3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrSP3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrSP3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrSP3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrSP3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvrSP3.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvrSP3.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrSP4 := BndP_Eb_081S9.LibSegEb_bvrSP4.
Definition KS_bvrSP4 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrSP4.regs0 PbvrSP4.regs_out0).
Lemma KS_bvrSP4_ok : BG.kept_ok 60 PbvrSP4.regs0 PbvrSP4.regs_out0 KS_bvrSP4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrSP4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 4 -> 0 <= Z.land (V 33%nat) 7 <= 3 -> L5KA.zeros_at M 2147469139 33 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9e78 M) (st fx' R' 0xb9ea8 M')
        /\ (forall x, In x KS_bvrSP4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) + 146077)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrSP4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrSP4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrSP4.kn0).
  { unfold know_ok, PbvrSP4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrSP4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrSP4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrSP4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrSP4.ps0) with 0xb9ea8 in Hms. change (SR.ps_regs PbvrSP4.ps0) with (map (fun i => (i, nth i PbvrSP4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrSP4.ps0) with PbvrSP4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrSP4.regs0 PbvrSP4.regs_out0 60 KS_bvrSP4 KS_bvrSP4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrSP4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrSP4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrSP4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrSP4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvrSP4.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvrSP4.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrSP5 := BndP_Eb_081S9.LibSegEb_bvrSP5.
Definition KS_bvrSP5 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrSP5.regs0 PbvrSP5.regs_out0).
Lemma KS_bvrSP5_ok : BG.kept_ok 60 PbvrSP5.regs0 PbvrSP5.regs_out0 KS_bvrSP5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrSP5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 5 -> 0 <= Z.land (V 33%nat) 7 <= 4 -> L5KA.zeros_at M 2147469139 33 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9e78 M) (st fx' R' 0xb9ea8 M')
        /\ (forall x, In x KS_bvrSP5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) + 146077)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrSP5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrSP5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrSP5.kn0).
  { unfold know_ok, PbvrSP5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrSP5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrSP5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrSP5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrSP5.ps0) with 0xb9ea8 in Hms. change (SR.ps_regs PbvrSP5.ps0) with (map (fun i => (i, nth i PbvrSP5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrSP5.ps0) with PbvrSP5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrSP5.regs0 PbvrSP5.regs_out0 60 KS_bvrSP5 KS_bvrSP5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrSP5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrSP5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrSP5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrSP5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvrSP5.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvrSP5.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrSP6 := BndP_Eb_081S9.LibSegEb_bvrSP6.
Definition KS_bvrSP6 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrSP6.regs0 PbvrSP6.regs_out0).
Lemma KS_bvrSP6_ok : BG.kept_ok 60 PbvrSP6.regs0 PbvrSP6.regs_out0 KS_bvrSP6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrSP6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 6 -> 0 <= Z.land (V 33%nat) 7 <= 5 -> L5KA.zeros_at M 2147469139 33 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9e78 M) (st fx' R' 0xb9ea8 M')
        /\ (forall x, In x KS_bvrSP6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) + 146077)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrSP6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrSP6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrSP6.kn0).
  { unfold know_ok, PbvrSP6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrSP6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrSP6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrSP6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrSP6.ps0) with 0xb9ea8 in Hms. change (SR.ps_regs PbvrSP6.ps0) with (map (fun i => (i, nth i PbvrSP6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrSP6.ps0) with PbvrSP6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrSP6.regs0 PbvrSP6.regs_out0 60 KS_bvrSP6 KS_bvrSP6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrSP6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrSP6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrSP6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrSP6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvrSP6.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvrSP6.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrSP7 := BndP_Eb_081S9.LibSegEb_bvrSP7.
Definition KS_bvrSP7 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrSP7.regs0 PbvrSP7.regs_out0).
Lemma KS_bvrSP7_ok : BG.kept_ok 60 PbvrSP7.regs0 PbvrSP7.regs_out0 KS_bvrSP7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrSP7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 7 -> 0 <= Z.land (V 33%nat) 7 <= 6 -> L5KA.zeros_at M 2147469139 33 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9e78 M) (st fx' R' 0xb9ea8 M')
        /\ (forall x, In x KS_bvrSP7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) + 146077)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrSP7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrSP7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrSP7.kn0).
  { unfold know_ok, PbvrSP7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrSP7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrSP7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrSP7.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrSP7.ps0) with 0xb9ea8 in Hms. change (SR.ps_regs PbvrSP7.ps0) with (map (fun i => (i, nth i PbvrSP7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrSP7.ps0) with PbvrSP7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrSP7.regs0 PbvrSP7.regs_out0 60 KS_bvrSP7 KS_bvrSP7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrSP7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrSP7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrSP7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrSP7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvrSP7.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvrSP7.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrT0 := BndP_Eb_082S9.LibSegEb_bvrT0.
Definition KS_bvrT0_0 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrT0.regs0 PbvrT0.regs_out0).
Lemma KS_bvrT0_0_ok : BG.kept_ok 60 PbvrT0.regs0 PbvrT0.regs_out0 KS_bvrT0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrT0_1 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrT0.regs0 PbvrT0.regs_out1).
Lemma KS_bvrT0_1_ok : BG.kept_ok 60 PbvrT0.regs0 PbvrT0.regs_out1 KS_bvrT0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrT0_2 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrT0.regs0 PbvrT0.regs_out2).
Lemma KS_bvrT0_2_ok : BG.kept_ok 60 PbvrT0.regs0 PbvrT0.regs_out2 KS_bvrT0_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrT0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 0 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb9eac M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrT0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56))
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56)) (ELit (-62)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb9eac M) (st fx' R' 0xb9f94 M')
        /\ (forall x, In x KS_bvrT0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56))
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ (V 37%nat) < 245
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56)) (ELit (-62)))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb9eac M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrT0_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56))
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ 245 <= (V 37%nat)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56)) (ELit (-62)))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrT0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrT0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrT0.kn0).
  { unfold know_ok, PbvrT0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrT0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrT0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrT0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PbvrT0.ps0) with 0xba060 in Hms. change (SR.ps_regs PbvrT0.ps0) with (map (fun i => (i, nth i PbvrT0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrT0.ps0) with PbvrT0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrT0.regs0 PbvrT0.regs_out0 60 KS_bvrT0_0 KS_bvrT0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrT0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbvrT0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrT0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PbvrT0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbvrT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PbvrT0.ps1) with 0xb9f94 in Hms. change (SR.ps_regs PbvrT0.ps1) with (map (fun i => (i, nth i PbvrT0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrT0.ps1) with PbvrT0.cells1 in Hcells. unfold PbvrT0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrT0.regs0 PbvrT0.regs_out1 60 KS_bvrT0_1 KS_bvrT0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrT0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrT0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbvrT0.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrT0.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PbvrT0.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PbvrT0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right.
    change (SR.ps_pc PbvrT0.ps2) with 0xba060 in Hms. change (SR.ps_regs PbvrT0.ps2) with (map (fun i => (i, nth i PbvrT0.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrT0.ps2) with PbvrT0.cells2 in Hcells. unfold PbvrT0.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrT0.regs0 PbvrT0.regs_out2 60 KS_bvrT0_2 KS_bvrT0_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrT0.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrT0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbvrT0.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrT0.regs_out2]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PbvrT0.regs_out2 E' R' 26 Hregs) by (clear; lia). cbn [nth PbvrT0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module PbvrT1a := BndP_Eb_082S9.LibSegEb_bvrT1a.
Definition KS_bvrT1a : list nat := Eval vm_compute in (BG.kept_list 60 PbvrT1a.regs0 PbvrT1a.regs_out0).
Lemma KS_bvrT1a_ok : BG.kept_ok 60 PbvrT1a.regs0 PbvrT1a.regs_out0 KS_bvrT1a = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrT1a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 1 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9eac M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrT1a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrT1a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrT1a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrT1a.kn0).
  { unfold know_ok, PbvrT1a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrT1a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrT1a.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrT1a.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrT1a.ps0) with 0xba060 in Hms. change (SR.ps_regs PbvrT1a.ps0) with (map (fun i => (i, nth i PbvrT1a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrT1a.ps0) with PbvrT1a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrT1a.regs0 PbvrT1a.regs_out0 60 KS_bvrT1a KS_bvrT1a_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PbvrT1a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrT1a.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrT1b := BndP_Eb_082S9.LibSegEb_bvrT1b.
Definition KS_bvrT1b : list nat := Eval vm_compute in (BG.kept_list 60 PbvrT1b.regs0 PbvrT1b.regs_out0).
Lemma KS_bvrT1b_ok : BG.kept_ok 60 PbvrT1b.regs0 PbvrT1b.regs_out0 KS_bvrT1b = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrT1b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 2 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9eac M) (st fx' R' 0xb9f28 M')
        /\ (forall x, In x KS_bvrT1b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrT1b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrT1b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrT1b.kn0).
  { unfold know_ok, PbvrT1b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrT1b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrT1b.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrT1b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrT1b.ps0) with 0xb9f28 in Hms. change (SR.ps_regs PbvrT1b.ps0) with (map (fun i => (i, nth i PbvrT1b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrT1b.ps0) with PbvrT1b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrT1b.regs0 PbvrT1b.regs_out0 60 KS_bvrT1b KS_bvrT1b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrT1b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrT1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrT1b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrT1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvrT1b.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbvrT1b.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrT2a := BndP_Eb_082S9.LibSegEb_bvrT2a.
Definition KS_bvrT2a : list nat := Eval vm_compute in (BG.kept_list 60 PbvrT2a.regs0 PbvrT2a.regs_out0).
Lemma KS_bvrT2a_ok : BG.kept_ok 60 PbvrT2a.regs0 PbvrT2a.regs_out0 KS_bvrT2a = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrT2a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 2 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 2 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9eac M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrT2a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrT2a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrT2a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrT2a.kn0).
  { unfold know_ok, PbvrT2a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrT2a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrT2a.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrT2a.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrT2a.ps0) with 0xba060 in Hms. change (SR.ps_regs PbvrT2a.ps0) with (map (fun i => (i, nth i PbvrT2a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrT2a.ps0) with PbvrT2a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrT2a.regs0 PbvrT2a.regs_out0 60 KS_bvrT2a KS_bvrT2a_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PbvrT2a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrT2a.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrT2b := BndP_Eb_082S9.LibSegEb_bvrT2b.
Definition KS_bvrT2b : list nat := Eval vm_compute in (BG.kept_list 60 PbvrT2b.regs0 PbvrT2b.regs_out0).
Lemma KS_bvrT2b_ok : BG.kept_ok 60 PbvrT2b.regs0 PbvrT2b.regs_out0 KS_bvrT2b = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrT2b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 2 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 3 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9eac M) (st fx' R' 0xb9f08 M')
        /\ (forall x, In x KS_bvrT2b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrT2b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrT2b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrT2b.kn0).
  { unfold know_ok, PbvrT2b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrT2b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrT2b.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrT2b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrT2b.ps0) with 0xb9f08 in Hms. change (SR.ps_regs PbvrT2b.ps0) with (map (fun i => (i, nth i PbvrT2b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrT2b.ps0) with PbvrT2b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrT2b.regs0 PbvrT2b.regs_out0 60 KS_bvrT2b KS_bvrT2b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrT2b.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvrT2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrT2b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrT2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrT2b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrT2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvrT2b.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbvrT2b.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrT3a := BndP_Eb_082S9.LibSegEb_bvrT3a.
Definition KS_bvrT3a : list nat := Eval vm_compute in (BG.kept_list 60 PbvrT3a.regs0 PbvrT3a.regs_out0).
Lemma KS_bvrT3a_ok : BG.kept_ok 60 PbvrT3a.regs0 PbvrT3a.regs_out0 KS_bvrT3a = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrT3a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 3 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9eac M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrT3a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrT3a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrT3a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrT3a.kn0).
  { unfold know_ok, PbvrT3a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrT3a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrT3a.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrT3a.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrT3a.ps0) with 0xba060 in Hms. change (SR.ps_regs PbvrT3a.ps0) with (map (fun i => (i, nth i PbvrT3a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrT3a.ps0) with PbvrT3a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrT3a.regs0 PbvrT3a.regs_out0 60 KS_bvrT3a KS_bvrT3a_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PbvrT3a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrT3a.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrT3b := BndP_Eb_082S9.LibSegEb_bvrT3b.
Definition KS_bvrT3b : list nat := Eval vm_compute in (BG.kept_list 60 PbvrT3b.regs0 PbvrT3b.regs_out0).
Lemma KS_bvrT3b_ok : BG.kept_ok 60 PbvrT3b.regs0 PbvrT3b.regs_out0 KS_bvrT3b = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrT3b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 4 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9eac M) (st fx' R' 0xb9ee8 M')
        /\ (forall x, In x KS_bvrT3b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 4)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbvrT3b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrT3b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrT3b.kn0).
  { unfold know_ok, PbvrT3b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrT3b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrT3b.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrT3b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrT3b.ps0) with 0xb9ee8 in Hms. change (SR.ps_regs PbvrT3b.ps0) with (map (fun i => (i, nth i PbvrT3b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrT3b.ps0) with PbvrT3b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrT3b.regs0 PbvrT3b.regs_out0 60 KS_bvrT3b KS_bvrT3b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrT3b.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvrT3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrT3b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrT3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrT3b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrT3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvrT3b.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbvrT3b.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvrTbig := BndP_Eb_082S9.LibSegEb_bvrTbig.
Definition KS_bvrTbig_0 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrTbig.regs0 PbvrTbig.regs_out0).
Lemma KS_bvrTbig_0_ok : BG.kept_ok 60 PbvrTbig.regs0 PbvrTbig.regs_out0 KS_bvrTbig_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrTbig_1 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrTbig.regs0 PbvrTbig.regs_out1).
Lemma KS_bvrTbig_1_ok : BG.kept_ok 60 PbvrTbig.regs0 PbvrTbig.regs_out1 KS_bvrTbig_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrTbig_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 (V 38%nat) -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  4 <= (V 38%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb9eac M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrTbig_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 38%nat))
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 1)
        /\ (V 38%nat) < (V 35%nat))
      \/ (msteps RSEGS (st fx R 0xb9eac M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrTbig_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ (V 35%nat) <= (V 38%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K4l; move K4l before pvzI10; pose proof (proj2 pvzI10) as K4r; move K4r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PbvrTbig.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrTbig.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrTbig.kn0).
  { unfold know_ok, PbvrTbig.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrTbig.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrTbig.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrTbig.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PbvrTbig.ps0) with 0xba060 in Hms. change (SR.ps_regs PbvrTbig.ps0) with (map (fun i => (i, nth i PbvrTbig.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrTbig.ps0) with PbvrTbig.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrTbig.regs0 PbvrTbig.regs_out0 60 KS_bvrTbig_0 KS_bvrTbig_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrTbig.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvrTbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbvrTbig.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrTbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbvrTbig.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrTbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbvrTbig.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbvrTbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  - right.
    change (SR.ps_pc PbvrTbig.ps1) with 0xba060 in Hms. change (SR.ps_regs PbvrTbig.ps1) with (map (fun i => (i, nth i PbvrTbig.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrTbig.ps1) with PbvrTbig.cells1 in Hcells. unfold PbvrTbig.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrTbig.regs0 PbvrTbig.regs_out1 60 KS_bvrTbig_1 KS_bvrTbig_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrTbig.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrTbig.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
Qed.

Module PbvrL := BndP_Eb_079S9.LibSegEb_bvrL.
Definition KS_bvrL_0 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out0).
Lemma KS_bvrL_0_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out0 KS_bvrL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrL_1 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out1).
Lemma KS_bvrL_1_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out1 KS_bvrL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrL_2 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out2).
Lemma KS_bvrL_2_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out2 KS_bvrL_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrL_3 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out3).
Lemma KS_bvrL_3_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out3 KS_bvrL_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrL_4 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out4).
Lemma KS_bvrL_4_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out4 KS_bvrL_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrL_5 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out5).
Lemma KS_bvrL_5_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out5 KS_bvrL_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrL_6 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out6).
Lemma KS_bvrL_6_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out6 KS_bvrL_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrL_7 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out7).
Lemma KS_bvrL_7_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out7 KS_bvrL_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrL_8 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out8).
Lemma KS_bvrL_8_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out8 KS_bvrL_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrL_9 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out9).
Lemma KS_bvrL_9_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out9 KS_bvrL_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrL_10 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out10).
Lemma KS_bvrL_10_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out10 KS_bvrL_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrL_11 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out11).
Lemma KS_bvrL_11_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out11 KS_bvrL_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrL_12 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out12).
Lemma KS_bvrL_12_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out12 KS_bvrL_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrL_13 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrL.regs0 PbvrL.regs_out13).
Lemma KS_bvrL_13_ok : BG.kept_ok 60 PbvrL.regs0 PbvrL.regs_out13 KS_bvrL_13 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 39%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 (V 34%nat) -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ (Z.land (V 39%nat) 255) < 144
        /\ (((V 37%nat) - 240) mod 2 ^ 64) < 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xb9f94 M')
        /\ (forall x, In x KS_bvrL_1 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 39%nat) 255)
        /\ 144 <= (Z.land (V 39%nat) 255)
        /\ (((V 37%nat) - 240) mod 2 ^ 64) < 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrL_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ 143 < (Z.land (V 39%nat) 255)
        /\ (((V 37%nat) - 244) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xb9f94 M')
        /\ (forall x, In x KS_bvrL_3 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 39%nat) 255)
        /\ (Z.land (V 39%nat) 255) <= 143
        /\ (((V 37%nat) - 244) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrL_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56)) (ELit (-62)))) <= 1
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xb9f94 M')
        /\ (forall x, In x KS_bvrL_5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56))
        /\ (V 37%nat) < 245
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56)) (ELit (-62)))) <= 0
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrL_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56))
        /\ 245 <= (V 37%nat)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56)) (ELit (-62)))) <= 0
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrL_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ (Z.land (V 39%nat) 255) < 160
        /\ (((V 37%nat) - 224) mod 2 ^ 64) < 1
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xb9f94 M')
        /\ (forall x, In x KS_bvrL_8 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 39%nat) 255)
        /\ 160 <= (Z.land (V 39%nat) 255)
        /\ (((V 37%nat) - 224) mod 2 ^ 64) < 1
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrL_9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ 159 < (Z.land (V 39%nat) 255)
        /\ (((V 37%nat) - 237) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xb9f94 M')
        /\ (forall x, In x KS_bvrL_10 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 39%nat) 255)
        /\ (Z.land (V 39%nat) 255) <= 159
        /\ (((V 37%nat) - 237) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrL_11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56)) (ELit (-62)))) <= 1
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xb9f94 M')
        /\ (forall x, In x KS_bvrL_12 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56))
        /\ (V 37%nat) < 245
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56)) (ELit (-62)))) <= 0
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb9f48 M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrL_13 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56))
        /\ 245 <= (V 37%nat)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 37)) (ELit 56)) (ELit (-62)))) <= 0
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G5 G6 G7 G8 G9 G10 G11 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G28 G29 G30 G31 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K1l; move K1l before pvzI8; pose proof (proj2 pvzI8) as K1r; move K1r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K2l; move K2l before pvzI9; pose proof (proj2 pvzI9) as K2r; move K2r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K4l; move K4l before pvzI11; pose proof (proj2 pvzI11) as K4r; move K4r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 37%nat => vz_37 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PbvrL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrL.kn0).
  { unfold know_ok, PbvrL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PbvrL.ps0) with 0xba060 in Hms. change (SR.ps_regs PbvrL.ps0) with (map (fun i => (i, nth i PbvrL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps0) with PbvrL.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out0 60 KS_bvrL_0 KS_bvrL_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PbvrL.ps1) with 0xb9f94 in Hms. change (SR.ps_regs PbvrL.ps1) with (map (fun i => (i, nth i PbvrL.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps1) with PbvrL.cells1 in Hcells. unfold PbvrL.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out1 60 KS_bvrL_1 KS_bvrL_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc PbvrL.ps2) with 0xba060 in Hms. change (SR.ps_regs PbvrL.ps2) with (map (fun i => (i, nth i PbvrL.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps2) with PbvrL.cells2 in Hcells. unfold PbvrL.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out2 60 KS_bvrL_2 KS_bvrL_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc PbvrL.ps3) with 0xb9f94 in Hms. change (SR.ps_regs PbvrL.ps3) with (map (fun i => (i, nth i PbvrL.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps3) with PbvrL.cells3 in Hcells. unfold PbvrL.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out3 60 KS_bvrL_3 KS_bvrL_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out3 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc PbvrL.ps4) with 0xba060 in Hms. change (SR.ps_regs PbvrL.ps4) with (map (fun i => (i, nth i PbvrL.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps4) with PbvrL.cells4 in Hcells. unfold PbvrL.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out4 60 KS_bvrL_4 KS_bvrL_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out4 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbvrL.regs_out4 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out4]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc PbvrL.ps5) with 0xb9f94 in Hms. change (SR.ps_regs PbvrL.ps5) with (map (fun i => (i, nth i PbvrL.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps5) with PbvrL.cells5 in Hcells. unfold PbvrL.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out5 60 KS_bvrL_5 KS_bvrL_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out5 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbvrL.regs_out5 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out5]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc PbvrL.ps6) with 0xba060 in Hms. change (SR.ps_regs PbvrL.ps6) with (map (fun i => (i, nth i PbvrL.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps6) with PbvrL.cells6 in Hcells. unfold PbvrL.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out6 60 KS_bvrL_6 KS_bvrL_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out6 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbvrL.regs_out6 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out6]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PbvrL.ps7) with 0xba060 in Hms. change (SR.ps_regs PbvrL.ps7) with (map (fun i => (i, nth i PbvrL.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps7) with PbvrL.cells7 in Hcells. unfold PbvrL.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out7 60 KS_bvrL_7 KS_bvrL_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PbvrL.ps8) with 0xb9f94 in Hms. change (SR.ps_regs PbvrL.ps8) with (map (fun i => (i, nth i PbvrL.regs_out8 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps8) with PbvrL.cells8 in Hcells. unfold PbvrL.cells8 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out8 60 KS_bvrL_8 KS_bvrL_8_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out8 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out8]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PbvrL.ps9) with 0xba060 in Hms. change (SR.ps_regs PbvrL.ps9) with (map (fun i => (i, nth i PbvrL.regs_out9 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps9) with PbvrL.cells9 in Hcells. unfold PbvrL.cells9 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out9 60 KS_bvrL_9 KS_bvrL_9_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out9 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PbvrL.ps10) with 0xb9f94 in Hms. change (SR.ps_regs PbvrL.ps10) with (map (fun i => (i, nth i PbvrL.regs_out10 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps10) with PbvrL.cells10 in Hcells. unfold PbvrL.cells10 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out10 60 KS_bvrL_10 KS_bvrL_10_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out10 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out10]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PbvrL.ps11) with 0xba060 in Hms. change (SR.ps_regs PbvrL.ps11) with (map (fun i => (i, nth i PbvrL.regs_out11 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps11) with PbvrL.cells11 in Hcells. unfold PbvrL.cells11 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out11 60 KS_bvrL_11 KS_bvrL_11_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out11 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out11]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbvrL.regs_out11 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out11]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PbvrL.ps12) with 0xb9f94 in Hms. change (SR.ps_regs PbvrL.ps12) with (map (fun i => (i, nth i PbvrL.regs_out12 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps12) with PbvrL.cells12 in Hcells. unfold PbvrL.cells12 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out12 60 KS_bvrL_12 KS_bvrL_12_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out12 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbvrL.regs_out12 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out12]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. right.
    change (SR.ps_pc PbvrL.ps13) with 0xba060 in Hms. change (SR.ps_regs PbvrL.ps13) with (map (fun i => (i, nth i PbvrL.regs_out13 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrL.ps13) with PbvrL.cells13 in Hcells. unfold PbvrL.cells13 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrL.regs0 PbvrL.regs_out13 60 KS_bvrL_13 KS_bvrL_13_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrL.regs_out13 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbvrL.regs_out13 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvrL.regs_out13]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module PbvrB := BndP_Eb_075S9.LibSegEb_bvrB.
Definition KS_bvrB_0 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrB.regs0 PbvrB.regs_out0).
Lemma KS_bvrB_0_ok : BG.kept_ok 60 PbvrB.regs0 PbvrB.regs_out0 KS_bvrB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvrB_1 : list nat := Eval vm_compute in (BG.kept_list 60 PbvrB.regs0 PbvrB.regs_out1).
Lemma KS_bvrB_1_ok : BG.kept_ok 60 PbvrB.regs0 PbvrB.regs_out1 KS_bvrB_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 (-1) -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 146077 -> getr R (reg 19) = Z_to_bv 64 (-146078) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 35%nat) <= 140737488355328 -> 0 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb9f94 M) (st fx' R' 0xba060 M')
        /\ (forall x, In x KS_bvrB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ (((V 33%nat) - (((V 33%nat) + (V 35%nat)) mod 2 ^ 64)) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb9f94 M) (st fx' R' 0xb9d64 M')
        /\ (forall x, In x KS_bvrB_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ 1 <= (((V 33%nat) - (((V 33%nat) + (V 35%nat)) mod 2 ^ 64)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G8 G9 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G26 G28 G29 G30 G31 pvzI4 pvzI5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K1l; move K1l before pvzI5; pose proof (proj2 pvzI5) as K1r; move K1r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K2l; move K2l before pvzI6; pose proof (proj2 pvzI6) as K2r; move K2r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PbvrB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrB.kn0).
  { unfold know_ok, PbvrB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrB.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrB.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PbvrB.ps0) with 0xba060 in Hms. change (SR.ps_regs PbvrB.ps0) with (map (fun i => (i, nth i PbvrB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrB.ps0) with PbvrB.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrB.regs0 PbvrB.regs_out0 60 KS_bvrB_0 KS_bvrB_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbvrB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  - right.
    change (SR.ps_pc PbvrB.ps1) with 0xb9d64 in Hms. change (SR.ps_regs PbvrB.ps1) with (map (fun i => (i, nth i PbvrB.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbvrB.ps1) with PbvrB.cells1 in Hcells. unfold PbvrB.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrB.regs0 PbvrB.regs_out1 60 KS_bvrB_1 KS_bvrB_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbvrB.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvrB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
Qed.

Module PbvrX := BndP_Eb_082S9.LibSegEb_bvrX.
Definition KS_bvrX : list nat := Eval vm_compute in (BG.kept_list 60 PbvrX.regs0 PbvrX.regs_out0).
Lemma KS_bvrX_ok : BG.kept_ok 60 PbvrX.regs0 PbvrX.regs_out0 KS_bvrX = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvrX_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) ->
  140735332487280 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 52%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba060 M) (st fx' R' 0xba098 M')
        /\ (forall x, In x KS_bvrX -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 52%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 G2 pvzI15 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV42l; move HV42l before pvzI4; pose proof (proj2 pvzI4) as HV42r; move HV42r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV49l; move HV49l before pvzI11; pose proof (proj2 pvzI11) as HV49r; move HV49r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV50l; move HV50l before pvzI12; pose proof (proj2 pvzI12) as HV50r; move HV50r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV51l; move HV51l before pvzI13; pose proof (proj2 pvzI13) as HV51r; move HV51r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV52l; move HV52l before pvzI14; pose proof (proj2 pvzI14) as HV52r; move HV52r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K0l; move K0l before pvzI15; pose proof (proj2 pvzI15) as K0r; move K0r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PbvrX.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvrX.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvrX.kn0).
  { unfold know_ok, PbvrX.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K14]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvrX.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvrX.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvrX.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvrX.ps0) with 0xba098 in Hms. change (SR.ps_regs PbvrX.ps0) with (map (fun i => (i, nth i PbvrX.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvrX.ps0) with PbvrX.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvrX.regs0 PbvrX.regs_out0 60 KS_bvrX KS_bvrX_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvrX.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrX.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrX.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrX.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrX.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrX.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrX.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrX.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrX.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrX.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrX.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrX.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvrX.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvrX.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbvrX.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

End PECVALBRP1.
