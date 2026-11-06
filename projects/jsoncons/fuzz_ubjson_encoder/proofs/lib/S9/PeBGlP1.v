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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_002S9 BndP_Eb_003S9 BndP_Eb_004S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBGLP1.
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

Module PaglA := BndP_Eb_002S9.LibSegEb_aglA.
Definition KS_aglA : list nat := Eval vm_compute in (BG.kept_list 80 PaglA.regs0 PaglA.regs_out0).
Lemma KS_aglA_ok : BG.kept_ok 80 PaglA.regs0 PaglA.regs_out0 KS_aglA = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba0f8 M) (st fx' R' 0x5ef40 M')
        /\ (forall x, In x KS_aglA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762216
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 160
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 K0 K1 K2 pvzI4 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PaglA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglA.kn0).
  { unfold know_ok, PaglA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaglA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglA.ps0) with 0x5ef40 in Hms. change (SR.ps_regs PaglA.ps0) with (map (fun i => (i, nth i PaglA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglA.ps0) with PaglA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglA.regs0 PaglA.regs_out0 80 KS_aglA KS_aglA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaglA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaglA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaglA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaglA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaglA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaglA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglA.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaglA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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

Module PaglB := BndP_Eb_002S9.LibSegEb_aglB.
Definition KS_aglB : list nat := Eval vm_compute in (BG.kept_list 80 PaglB.regs0 PaglB.regs_out0).
Lemma KS_aglB_ok : BG.kept_ok 80 PaglB.regs0 PaglB.regs_out0 KS_aglB = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 47%nat) <= 140737488355072 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) ->
  (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 20) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 20) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba168 M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_aglB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762436
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551602
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450895) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450894) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450893) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 762104
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 85827
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 47%nat)
        /\ L5.defined M' ((V 47%nat) + 24) 232
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450900) 12).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G19 G20 G26 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9 K10 pvzI8 K12 K13 K14 K15 K16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K11l; move K11l before pvzI8; pose proof (proj2 pvzI8) as K11r; move K11r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PaglB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglB.kn0).
  { unfold know_ok, PaglB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K15 K16; lia | clear - HV2l HV2r K0l K0r K15 K16; lia | clear - HV2l HV2r K0l K0r K15 K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | exactA K8]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk ZA ltac:(clear - HV48l HV48r K11l K11r K13 K14 K16) | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | clear - HV47l HV47r K3l K3r K7 K14 K15; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K11l K11r K13 K14 K16) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K11l K11r K13 K14 K16) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K11l K11r K13 K14 K16; lia | clear - HV48l HV48r K11l K11r K13 K14 K16; lia | clear - HV48l HV48r K11l K11r K13 K14 K16; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K11l K11r K13 K14 K16) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K11l K11r K13 K14 K16) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K11l K11r K13 K14 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglB.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 104) <= bv_unsigned a < (vz_2 - 104) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 20) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaglB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K15 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K14 K15 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K14 K15 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglB.ps0) with 0xb9148 in Hms. change (SR.ps_regs PaglB.ps0) with (map (fun i => (i, nth i PaglB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglB.ps0) with PaglB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglB.regs0 PaglB.regs_out0 80 KS_aglB KS_aglB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaglB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaglB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PaglB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PaglB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaglB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaglB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglB.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglB.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaglB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglB.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaglB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K16) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaglB1 := BndP_Eb_002S9.LibSegEb_aglB1.
Definition KS_aglB1 : list nat := Eval vm_compute in (BG.kept_list 80 PaglB1.regs0 PaglB1.regs_out0).
Lemma KS_aglB1_ok : BG.kept_ok 80 PaglB1.regs0 PaglB1.regs_out0 KS_aglB1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglB1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba244 M) (st fx' R' 0xba248 M')
        /\ (forall x, In x KS_aglB1 -> getr R' (reg x) = getr R (reg x))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G18 G19 G20 G21 G22 G24 G25 G26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PaglB1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglB1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglB1.kn0).
  { unfold know_ok, PaglB1.kn0.
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglB1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglB1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglB1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglB1.ps0) with 0xba248 in Hms. change (SR.ps_regs PaglB1.ps0) with (map (fun i => (i, nth i PaglB1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglB1.ps0) with PaglB1.cells0 in Hcells.
  split. { exact Hms. }
  intros j Hj. apply (BG.kept_regs E E' R R' PaglB1.regs0 PaglB1.regs_out0 80 KS_aglB1 KS_aglB1_ok HR Hag Hregs j Hj).
Qed.

Module PaglE0 := BndP_Eb_003S9.LibSegEb_aglE0.
Definition KS_aglE0 : list nat := Eval vm_compute in (BG.kept_list 80 PaglE0.regs0 PaglE0.regs_out0).
Lemma KS_aglE0_ok : BG.kept_ok 80 PaglE0.regs0 PaglE0.regs_out0 KS_aglE0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglE0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba244 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglE0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762584
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G18 G19 G20 G21 G22 G24 G25 G26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PaglE0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglE0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglE0.kn0).
  { unfold know_ok, PaglE0.kn0.
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglE0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglE0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglE0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglE0.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglE0.ps0) with (map (fun i => (i, nth i PaglE0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglE0.ps0) with PaglE0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglE0.regs0 PaglE0.regs_out0 80 KS_aglE0 KS_aglE0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglE0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglE0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglE0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglE0.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglTi := BndP_Eb_004S9.LibSegEb_aglTi.
Definition KS_aglTi : list nat := Eval vm_compute in (BG.kept_list 80 PaglTi.regs0 PaglTi.regs_out0).
Lemma KS_aglTi_ok : BG.kept_ok 80 PaglTi.regs0 PaglTi.regs_out0 KS_aglTi = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglTi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 105 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  6930432 <= (V 47%nat) <= 140737488355072 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 ->
  (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) ->
  (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 6) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 6) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 6) <= i < ((((V 47%nat) / 8) + 2147450880) + 6) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba24c M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_aglTi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762504
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 48)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 22) = Z_to_bv 64 1
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 47%nat) + 48)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G24 G25 G26 pvzI6 K1 K2 K3 K4 K5 K6 pvzI7 K8 K9 K10 K11 K12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PaglTi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglTi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglTi.kn0).
  { unfold know_ok, PaglTi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglTi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglTi.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 6) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 6) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaglTi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglTi.ps0) with 0xb9148 in Hms. change (SR.ps_regs PaglTi.ps0) with (map (fun i => (i, nth i PaglTi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglTi.ps0) with PaglTi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglTi.regs0 PaglTi.regs_out0 80 KS_aglTi KS_aglTi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglTi.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglTi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglTi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglTi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTi.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaglTi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTi.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglTi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTi.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglTi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PaglTU := BndP_Eb_004S9.LibSegEb_aglTU.
Definition KS_aglTU : list nat := Eval vm_compute in (BG.kept_list 80 PaglTU.regs0 PaglTU.regs_out0).
Lemma KS_aglTU_ok : BG.kept_ok 80 PaglTU.regs0 PaglTU.regs_out0 KS_aglTU = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglTU_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 85 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  6930432 <= (V 47%nat) <= 140737488355072 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 ->
  (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) ->
  (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 8) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 8) <= i < ((((V 47%nat) / 8) + 2147450880) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba24c M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_aglTU -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762812
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 64)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 47%nat) + 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G24 G25 G26 pvzI6 K1 K2 K3 K4 K5 K6 pvzI7 K8 K9 K10 K11 K12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PaglTU.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglTU.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglTU.kn0).
  { unfold know_ok, PaglTU.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglTU.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglTU.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 8) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 8) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaglTU.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglTU.ps0) with 0xb9148 in Hms. change (SR.ps_regs PaglTU.ps0) with (map (fun i => (i, nth i PaglTU.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglTU.ps0) with PaglTU.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglTU.regs0 PaglTU.regs_out0 80 KS_aglTU KS_aglTU_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglTU.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglTU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTU.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglTU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTU.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglTU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTU.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaglTU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTU.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglTU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PaglTI := BndP_Eb_004S9.LibSegEb_aglTI.
Definition KS_aglTI : list nat := Eval vm_compute in (BG.kept_list 80 PaglTI.regs0 PaglTI.regs_out0).
Lemma KS_aglTI_ok : BG.kept_ok 80 PaglTI.regs0 PaglTI.regs_out0 KS_aglTI = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglTI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 73 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  6930432 <= (V 47%nat) <= 140737488355072 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 ->
  (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) ->
  (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 10) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 10) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 10) <= i < ((((V 47%nat) / 8) + 2147450880) + 10) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba24c M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_aglTI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762940
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 80)
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 47%nat) + 80)
        /\ getr R' (reg 23) = Z_to_bv 64 2
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 2).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G24 G25 G26 pvzI6 K1 K2 K3 K4 K5 K6 pvzI7 K8 K9 K10 K11 K12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PaglTI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglTI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglTI.kn0).
  { unfold know_ok, PaglTI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglTI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglTI.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 10) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 10) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaglTI.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglTI.ps0) with 0xb9148 in Hms. change (SR.ps_regs PaglTI.ps0) with (map (fun i => (i, nth i PaglTI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglTI.ps0) with PaglTI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglTI.regs0 PaglTI.regs_out0 80 KS_aglTI KS_aglTI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglTI.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglTI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglTI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTI.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglTI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTI.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaglTI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTI.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglTI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTI.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglTI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PaglTl := BndP_Eb_004S9.LibSegEb_aglTl.
Definition KS_aglTl : list nat := Eval vm_compute in (BG.kept_list 80 PaglTl.regs0 PaglTl.regs_out0).
Lemma KS_aglTl_ok : BG.kept_ok 80 PaglTl.regs0 PaglTl.regs_out0 KS_aglTl = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglTl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 108 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  6930432 <= (V 47%nat) <= 140737488355072 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 ->
  (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) ->
  (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 12) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 12) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 12) <= i < ((((V 47%nat) / 8) + 2147450880) + 12) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba24c M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_aglTl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762852
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 96)
        /\ getr R' (reg 12) = Z_to_bv 64 4
        /\ getr R' (reg 22) = Z_to_bv 64 4
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 47%nat) + 96)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G24 G25 G26 pvzI6 K1 K2 K3 K4 K5 K6 pvzI7 K8 K9 K10 K11 K12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PaglTl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglTl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglTl.kn0).
  { unfold know_ok, PaglTl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglTl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglTl.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 12) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 12) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaglTl.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglTl.ps0) with 0xb9148 in Hms. change (SR.ps_regs PaglTl.ps0) with (map (fun i => (i, nth i PaglTl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglTl.ps0) with PaglTl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglTl.regs0 PaglTl.regs_out0 80 KS_aglTl KS_aglTl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglTl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglTl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglTl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTl.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglTl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaglTl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTl.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglTl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTl.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglTl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PaglTL := BndP_Eb_004S9.LibSegEb_aglTL.
Definition KS_aglTL : list nat := Eval vm_compute in (BG.kept_list 80 PaglTL.regs0 PaglTL.regs_out0).
Lemma KS_aglTL_ok : BG.kept_ok 80 PaglTL.regs0 PaglTL.regs_out0 KS_aglTL = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglTL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 76 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  6930432 <= (V 47%nat) <= 140737488355072 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 ->
  (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) ->
  (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 14) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 14) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 14) <= i < ((((V 47%nat) / 8) + 2147450880) + 14) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba24c M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_aglTL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762664
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 112)
        /\ getr R' (reg 12) = Z_to_bv 64 8
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 47%nat) + 112)
        /\ getr R' (reg 23) = Z_to_bv 64 8
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450894) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G24 G25 G26 pvzI6 K1 K2 K3 K4 K5 K6 pvzI7 K8 K9 K10 K11 K12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PaglTL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglTL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglTL.kn0).
  { unfold know_ok, PaglTL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglTL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglTL.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 14) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 14) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaglTL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglTL.ps0) with 0xb9148 in Hms. change (SR.ps_regs PaglTL.ps0) with (map (fun i => (i, nth i PaglTL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglTL.ps0) with PaglTL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglTL.regs0 PaglTL.regs_out0 80 KS_aglTL KS_aglTL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglTL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaglTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTL.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTL.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PaglTd1 := BndP_Eb_004S9.LibSegEb_aglTd1.
Definition KS_aglTd1 : list nat := Eval vm_compute in (BG.kept_list 80 PaglTd1.regs0 PaglTd1.regs_out0).
Lemma KS_aglTd1_ok : BG.kept_ok 80 PaglTd1.regs0 PaglTd1.regs_out0 KS_aglTd1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglTd1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  0 <= (V 49%nat) <= 72 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba24c M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglTd1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762984
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G24 G25 G26 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PaglTd1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglTd1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglTd1.kn0).
  { unfold know_ok, PaglTd1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglTd1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglTd1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglTd1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglTd1.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglTd1.ps0) with (map (fun i => (i, nth i PaglTd1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglTd1.ps0) with PaglTd1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglTd1.regs0 PaglTd1.regs_out0 80 KS_aglTd1 KS_aglTd1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglTd1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglTd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTd1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglTd1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglTd1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglTd1.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglTd2 := BndP_Eb_004S9.LibSegEb_aglTd2.
Definition KS_aglTd2 : list nat := Eval vm_compute in (BG.kept_list 80 PaglTd2.regs0 PaglTd2.regs_out0).
Lemma KS_aglTd2_ok : BG.kept_ok 80 PaglTd2.regs0 PaglTd2.regs_out0 KS_aglTd2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglTd2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  74 <= (V 49%nat) <= 75 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba24c M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglTd2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762984
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G24 G25 G26 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PaglTd2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglTd2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglTd2.kn0).
  { unfold know_ok, PaglTd2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglTd2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglTd2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglTd2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglTd2.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglTd2.ps0) with (map (fun i => (i, nth i PaglTd2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglTd2.ps0) with PaglTd2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglTd2.regs0 PaglTd2.regs_out0 80 KS_aglTd2 KS_aglTd2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglTd2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglTd2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTd2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglTd2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglTd2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglTd2.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglTd3 := BndP_Eb_004S9.LibSegEb_aglTd3.
Definition KS_aglTd3 : list nat := Eval vm_compute in (BG.kept_list 80 PaglTd3.regs0 PaglTd3.regs_out0).
Lemma KS_aglTd3_ok : BG.kept_ok 80 PaglTd3.regs0 PaglTd3.regs_out0 KS_aglTd3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglTd3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  77 <= (V 49%nat) <= 84 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba24c M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglTd3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762984
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G24 G25 G26 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PaglTd3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglTd3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglTd3.kn0).
  { unfold know_ok, PaglTd3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglTd3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglTd3.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglTd3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglTd3.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglTd3.ps0) with (map (fun i => (i, nth i PaglTd3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglTd3.ps0) with PaglTd3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglTd3.regs0 PaglTd3.regs_out0 80 KS_aglTd3 KS_aglTd3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglTd3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglTd3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTd3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglTd3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglTd3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglTd3.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglTd4 := BndP_Eb_004S9.LibSegEb_aglTd4.
Definition KS_aglTd4 : list nat := Eval vm_compute in (BG.kept_list 80 PaglTd4.regs0 PaglTd4.regs_out0).
Lemma KS_aglTd4_ok : BG.kept_ok 80 PaglTd4.regs0 PaglTd4.regs_out0 KS_aglTd4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglTd4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  86 <= (V 49%nat) <= 104 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba24c M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglTd4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762984
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G24 G25 G26 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PaglTd4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglTd4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglTd4.kn0).
  { unfold know_ok, PaglTd4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglTd4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglTd4.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglTd4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglTd4.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglTd4.ps0) with (map (fun i => (i, nth i PaglTd4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglTd4.ps0) with PaglTd4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglTd4.regs0 PaglTd4.regs_out0 80 KS_aglTd4 KS_aglTd4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglTd4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglTd4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTd4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglTd4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglTd4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglTd4.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglTd5 := BndP_Eb_004S9.LibSegEb_aglTd5.
Definition KS_aglTd5 : list nat := Eval vm_compute in (BG.kept_list 80 PaglTd5.regs0 PaglTd5.regs_out0).
Lemma KS_aglTd5_ok : BG.kept_ok 80 PaglTd5.regs0 PaglTd5.regs_out0 KS_aglTd5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglTd5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  106 <= (V 49%nat) <= 107 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba24c M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglTd5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762984
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G24 G25 G26 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PaglTd5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglTd5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglTd5.kn0).
  { unfold know_ok, PaglTd5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglTd5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglTd5.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglTd5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglTd5.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglTd5.ps0) with (map (fun i => (i, nth i PaglTd5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglTd5.ps0) with PaglTd5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglTd5.regs0 PaglTd5.regs_out0 80 KS_aglTd5 KS_aglTd5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglTd5.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglTd5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTd5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglTd5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglTd5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglTd5.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglTd6 := BndP_Eb_004S9.LibSegEb_aglTd6.
Definition KS_aglTd6 : list nat := Eval vm_compute in (BG.kept_list 80 PaglTd6.regs0 PaglTd6.regs_out0).
Lemma KS_aglTd6_ok : BG.kept_ok 80 PaglTd6.regs0 PaglTd6.regs_out0 KS_aglTd6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglTd6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  109 <= (V 49%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba24c M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglTd6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762984
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G24 G25 G26 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PaglTd6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglTd6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglTd6.kn0).
  { unfold know_ok, PaglTd6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglTd6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglTd6.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglTd6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglTd6.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglTd6.ps0) with (map (fun i => (i, nth i PaglTd6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglTd6.ps0) with PaglTd6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglTd6.regs0 PaglTd6.regs_out0 80 KS_aglTd6 KS_aglTd6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglTd6.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglTd6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglTd6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglTd6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglTd6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglTd6.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

End PEBGLP1.
