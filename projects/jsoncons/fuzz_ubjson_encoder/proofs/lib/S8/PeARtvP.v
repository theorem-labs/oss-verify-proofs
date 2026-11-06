(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BigLinkZA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ea0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndP_Ea_040S8 BndP_Ea_041S8.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEARTVP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

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

Module PartA := BndP_Ea_040S8.LibSegEa_artA.
Definition KS_artA : list nat := Eval vm_compute in (BG.kept_list 80 PartA.regs0 PartA.regs_out0).
Lemma KS_artA_ok : BG.kept_ok 80 PartA.regs0 PartA.regs_out0 KS_artA = true. Proof. vm_compute. reflexivity. Qed.
Lemma artA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb34e4 M) (st fx' R' 0x5e414 M')
        /\ (forall x, In x KS_artA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 734548
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1317368
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 G11 G12 K0 K1 K2 pvzI5 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PartA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PartA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PartA.kn0).
  { unfold know_ok, PartA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PartA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PartA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PartA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PartA.ps0) with 0x5e414 in Hms. change (SR.ps_regs PartA.ps0) with (map (fun i => (i, nth i PartA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PartA.ps0) with PartA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PartA.regs0 PartA.regs_out0 80 KS_artA KS_artA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PartA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PartA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PartA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PartA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PartA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PartA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PartA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PartA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PartA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PartA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PartA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartA.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PartA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PartB0 := BndP_Ea_040S8.LibSegEa_artB0.
Definition KS_artB0 : list nat := Eval vm_compute in (BG.kept_list 80 PartB0.regs0 PartB0.regs_out0).
Lemma KS_artB0_ok : BG.kept_ok 80 PartB0.regs0 PartB0.regs_out0 KS_artB0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma artB0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 96) + 96 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 96)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 96) + 96 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 96)) -> (((V 2%nat) - 96) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 96)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) ->
  ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 45%nat) + 272 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 45%nat)) -> ((V 45%nat) + 272 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 45%nat)) ->
  ((((V 45%nat) / 8) + 2147450880) + 34 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 45%nat) / 8) + 2147450880)) -> 6914048 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 272 <= 2147446784) ->
  L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 45%nat) 272 -> (((V 2%nat) - 96) + 96 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((V 2%nat) - 96)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 45%nat) ->
  L5.u64_at RSEGS M (V 45%nat) 1273384 -> L5.u32_at RSEGS M ((V 45%nat) + 152) 0 -> ((V 36%nat) + 384 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) -> L5KA.zeros_at M 2147610050 1 ->
  ((V 45%nat) + 272 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 45%nat)) -> ((V 45%nat) + 272 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 45%nat)) -> ((((V 47%nat) / 8) + 2147450880) + 8 <= 2147610050 \/ 2147610050 + 1 <= (((V 47%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3554 M) (st fx' R' 0xb540c M')
        /\ (forall x, In x KS_artB0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 734820
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 243
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 734436
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 137238
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 40).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G19 G20 G21 G25 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI10 K18 K19 K20 K21 K22 K23 K24 pvzI11 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 pvzI12 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K17l; move K17l before pvzI10; pose proof (proj2 pvzI10) as K17r; move K17r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K25l; move K25l before pvzI11; pose proof (proj2 pvzI11) as K25r; move K25r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K37l; move K37l before pvzI12; pose proof (proj2 pvzI12) as K37r; move K37r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 45%nat => Z_to_bv 64 vz_45 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 45%nat => vz_45 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PartB0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PartB0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PartB0.kn0).
  { unfold know_ok, PartB0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K29 K30 K42; lia | clear - HV2l HV2r K3l K3r K13 K29 K30 K42; lia | clear - HV2l HV2r K3l K3r K13 K29 K30 K42; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | exactA K22]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49; lia | clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49; lia | clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PartB0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PartB0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PartB0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K29 K30 K42 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PartB0.ps0) with 0xb540c in Hms. change (SR.ps_regs PartB0.ps0) with (map (fun i => (i, nth i PartB0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PartB0.ps0) with PartB0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PartB0.regs0 PartB0.regs_out0 80 KS_artB0 KS_artB0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PartB0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PartB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PartB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PartB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PartB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PartB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PartB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PartB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PartB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PartB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PartB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PartB2 := BndP_Ea_040S8.LibSegEa_artB2.
Definition KS_artB2 : list nat := Eval vm_compute in (BG.kept_list 80 PartB2.regs0 PartB2.regs_out0).
Lemma KS_artB2_ok : BG.kept_ok 80 PartB2.regs0 PartB2.regs_out0 KS_artB2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma artB2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 96) + 96 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 96)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 96) + 96 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 96)) -> (((V 2%nat) - 96) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 96)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) ->
  ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 45%nat) + 272 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 45%nat)) -> ((V 45%nat) + 272 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 45%nat)) ->
  ((((V 45%nat) / 8) + 2147450880) + 34 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 45%nat) / 8) + 2147450880)) -> 6914048 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 272 <= 2147446784) ->
  L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 45%nat) 272 -> (((V 2%nat) - 96) + 96 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((V 2%nat) - 96)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 45%nat) ->
  L5.u64_at RSEGS M (V 45%nat) 1273384 -> L5.u32_at RSEGS M ((V 45%nat) + 152) 2 -> ((V 36%nat) + 384 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) -> L5KA.zeros_at M 2147610050 1 ->
  ((V 45%nat) + 272 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 45%nat)) -> ((V 45%nat) + 272 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 45%nat)) -> ((((V 47%nat) / 8) + 2147450880) + 8 <= 2147610050 \/ 2147610050 + 1 <= (((V 47%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3554 M) (st fx' R' 0xb540c M')
        /\ (forall x, In x KS_artB2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 734820
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 243
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 734436
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 137238
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 40).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G19 G20 G21 G25 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI10 K18 K19 K20 K21 K22 K23 K24 pvzI11 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 pvzI12 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K17l; move K17l before pvzI10; pose proof (proj2 pvzI10) as K17r; move K17r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K25l; move K25l before pvzI11; pose proof (proj2 pvzI11) as K25r; move K25r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K37l; move K37l before pvzI12; pose proof (proj2 pvzI12) as K37r; move K37r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 45%nat => Z_to_bv 64 vz_45 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 45%nat => vz_45 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PartB2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PartB2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PartB2.kn0).
  { unfold know_ok, PartB2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K29 K30 K42; lia | clear - HV2l HV2r K3l K3r K13 K29 K30 K42; lia | clear - HV2l HV2r K3l K3r K13 K29 K30 K42; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | exactA K22]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49; lia | clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49; lia | clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K13 K14 K15 K16 K31 K32 K33 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K34 K35 K36 K37l K37r K39 K42 K46 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15 K25l K25r K27 K28 K30 K32 K35 K49) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PartB2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PartB2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PartB2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K29 K30 K42 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PartB2.ps0) with 0xb540c in Hms. change (SR.ps_regs PartB2.ps0) with (map (fun i => (i, nth i PartB2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PartB2.ps0) with PartB2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PartB2.regs0 PartB2.regs_out0 80 KS_artB2 KS_artB2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PartB2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PartB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PartB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PartB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PartB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PartB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PartB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PartB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PartB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PartB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartB2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PartB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K29 K30 K42) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K14 K16 K17l K17r K21 K28 K29 K31 K33 K34 K36 K48 K50 K51) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PartC := BndP_Ea_040S8.LibSegEa_artC.
Definition KS_artC : list nat := Eval vm_compute in (BG.kept_list 80 PartC.regs0 PartC.regs_out0).
Lemma KS_artC_ok : BG.kept_ok 80 PartC.regs0 PartC.regs_out0 KS_artC = true. Proof. vm_compute. reflexivity. Qed.
Lemma artC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 (V 47%nat) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3664 M) (st fx' R' 0xb3668 M')
        /\ (forall x, In x KS_artC -> getr R' (reg x) = getr R (reg x))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PartC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PartC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PartC.kn0).
  { unfold know_ok, PartC.kn0.
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PartC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PartC.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PartC.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PartC.ps0) with 0xb3668 in Hms. change (SR.ps_regs PartC.ps0) with (map (fun i => (i, nth i PartC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PartC.ps0) with PartC.cells0 in Hcells.
  split. { exact Hms. }
  intros j Hj. apply (BG.kept_regs E E' R R' PartC.regs0 PartC.regs_out0 80 KS_artC KS_artC_ok HR Hag Hregs j Hj).
Qed.

Module PartD := BndP_Ea_041S8.LibSegEa_artD.
Definition KS_artD : list nat := Eval vm_compute in (BG.kept_list 80 PartD.regs0 PartD.regs_out0).
Lemma KS_artD_ok : BG.kept_ok 80 PartD.regs0 PartD.regs_out0 KS_artD = true. Proof. vm_compute. reflexivity. Qed.
Lemma artD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 12) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 (V 47%nat) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  0 <= (V 49%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb366c M) (st fx' R' 0xb395c M')
        /\ (forall x, In x KS_artD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 734844
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G24 G25 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV49l; move HV49l before pvzI6; pose proof (proj2 pvzI6) as HV49r; move HV49r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PartD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PartD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PartD.kn0).
  { unfold know_ok, PartD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PartD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PartD.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PartD.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PartD.ps0) with 0xb395c in Hms. change (SR.ps_regs PartD.ps0) with (map (fun i => (i, nth i PartD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PartD.ps0) with PartD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PartD.regs0 PartD.regs_out0 80 KS_artD KS_artD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PartD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PartD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PartD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PartD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PartD.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PartD.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PartE := BndP_Ea_041S8.LibSegEa_artE.
Definition KS_artE : list nat := Eval vm_compute in (BG.kept_list 80 PartE.regs0 PartE.regs_out0).
Lemma KS_artE_ok : BG.kept_ok 80 PartE.regs0 PartE.regs_out0 KS_artE = true. Proof. vm_compute. reflexivity. Qed.
Lemma artE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 (V 47%nat) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  140735332487264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 6914048 <= (V 47%nat) <= 140737488355264 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 96) + 96 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 96)) -> (((V 2%nat) - 96) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 96)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb367c M) (st fx' R' 0xb3768 M')
        /\ (forall x, In x KS_artE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.defined M' ((V 47%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI18 K1 K2 pvzI19 K4 K5 K6 K7 K8 K9 pvzI20 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV64l; move HV64l before pvzI7; pose proof (proj2 pvzI7) as HV64r; move HV64r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV65l; move HV65l before pvzI8; pose proof (proj2 pvzI8) as HV65r; move HV65r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV66l; move HV66l before pvzI9; pose proof (proj2 pvzI9) as HV66r; move HV66r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV67l; move HV67l before pvzI10; pose proof (proj2 pvzI10) as HV67r; move HV67r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV68l; move HV68l before pvzI11; pose proof (proj2 pvzI11) as HV68r; move HV68r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV69l; move HV69l before pvzI12; pose proof (proj2 pvzI12) as HV69r; move HV69r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV70l; move HV70l before pvzI13; pose proof (proj2 pvzI13) as HV70r; move HV70r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV71l; move HV71l before pvzI14; pose proof (proj2 pvzI14) as HV71r; move HV71r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV72l; move HV72l before pvzI15; pose proof (proj2 pvzI15) as HV72r; move HV72r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV73l; move HV73l before pvzI16; pose proof (proj2 pvzI16) as HV73r; move HV73r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV74l; move HV74l before pvzI17; pose proof (proj2 pvzI17) as HV74r; move HV74r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K10l; move K10l before pvzI20; pose proof (proj2 pvzI20) as K10r; move K10r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E PartE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PartE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PartE.kn0).
  { unfold know_ok, PartE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K26]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PartE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PartE.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PartE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K10l K10r K12 K13 K15 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PartE.ps0) with 0xb3768 in Hms. change (SR.ps_regs PartE.ps0) with (map (fun i => (i, nth i PartE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PartE.ps0) with PartE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PartE.regs0 PartE.regs_out0 80 KS_artE KS_artE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PartE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PartE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PartE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PartE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PartE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PartE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PartE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartE.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PartE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartE.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PartE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartE.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PartE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartE.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PartE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartE.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PartE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartE.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PartE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartE.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PartE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PartE0 := BndP_Ea_041S8.LibSegEa_artE0.
Definition KS_artE0 : list nat := Eval vm_compute in (BG.kept_list 80 PartE0.regs0 PartE0.regs_out0).
Lemma KS_artE0_ok : BG.kept_ok 80 PartE0.regs0 PartE0.regs_out0 KS_artE0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma artE0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 (V 47%nat) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3664 M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_artE0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 734900
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PartE0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PartE0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PartE0.kn0).
  { unfold know_ok, PartE0.kn0.
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PartE0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PartE0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PartE0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PartE0.ps0) with 0xae310 in Hms. change (SR.ps_regs PartE0.ps0) with (map (fun i => (i, nth i PartE0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PartE0.ps0) with PartE0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PartE0.regs0 PartE0.regs_out0 80 KS_artE0 KS_artE0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PartE0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PartE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartE0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PartE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PartE0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PartE0.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PartZ := BndP_Ea_041S8.LibSegEa_artZ.
Definition KS_artZ : list nat := Eval vm_compute in (BG.kept_list 80 PartZ.regs0 PartZ.regs_out0).
Lemma KS_artZ_ok : BG.kept_ok 80 PartZ.regs0 PartZ.regs_out0 KS_artZ = true. Proof. vm_compute. reflexivity. Qed.
Lemma artZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 (V 47%nat) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  140735332487264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 6914048 <= (V 36%nat) <= 140737488354944 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 ->
  L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 96) + 96 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 96)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) ->
  ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 96) + 96 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 96)) -> (((V 2%nat) - 96) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 96)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) ->
  ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb36b4 M) (st fx' R' 0xb3768 M')
        /\ (forall x, In x KS_artZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI18 K1 K2 pvzI19 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 pvzI20 K15 K16 K17 K18 K19 K20 pvzI21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV64l; move HV64l before pvzI7; pose proof (proj2 pvzI7) as HV64r; move HV64r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV65l; move HV65l before pvzI8; pose proof (proj2 pvzI8) as HV65r; move HV65r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV66l; move HV66l before pvzI9; pose proof (proj2 pvzI9) as HV66r; move HV66r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV67l; move HV67l before pvzI10; pose proof (proj2 pvzI10) as HV67r; move HV67r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV68l; move HV68l before pvzI11; pose proof (proj2 pvzI11) as HV68r; move HV68r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV69l; move HV69l before pvzI12; pose proof (proj2 pvzI12) as HV69r; move HV69r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV70l; move HV70l before pvzI13; pose proof (proj2 pvzI13) as HV70r; move HV70r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV71l; move HV71l before pvzI14; pose proof (proj2 pvzI14) as HV71r; move HV71r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV72l; move HV72l before pvzI15; pose proof (proj2 pvzI15) as HV72r; move HV72r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV73l; move HV73l before pvzI16; pose proof (proj2 pvzI16) as HV73r; move HV73r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV74l; move HV74l before pvzI17; pose proof (proj2 pvzI17) as HV74r; move HV74r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K14l; move K14l before pvzI20; pose proof (proj2 pvzI20) as K14r; move K14r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K21l; move K21l before pvzI21; pose proof (proj2 pvzI21) as K21r; move K21r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E PartZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PartZ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PartZ.kn0).
  { unfold know_ok, PartZ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29; lia | clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29; lia | clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29; lia | exactA K6]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29; lia | clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29; lia | clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29; lia | exactA K7]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29; lia | clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29; lia | clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29; lia | clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29; lia | clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29; lia | clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29; lia | clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29; lia | clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29; lia | clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29; lia | clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29; lia | clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28) | clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29; lia | clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28; lia | clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28; lia | clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K25 K26) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | clear - HV2l HV2r K0l K0r K10 K25 K26; lia | exactA K40]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PartZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PartZ.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PartZ.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PartZ.ps0) with 0xb3768 in Hms. change (SR.ps_regs PartZ.ps0) with (map (fun i => (i, nth i PartZ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PartZ.ps0) with PartZ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PartZ.regs0 PartZ.regs_out0 80 KS_artZ KS_artZ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PartZ.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PartZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K12 K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K11 K12 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11 K13 K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

End PEARTVP.
