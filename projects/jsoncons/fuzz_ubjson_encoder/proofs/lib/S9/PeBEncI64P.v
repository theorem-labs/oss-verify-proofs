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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_066S9 BndP_Eb_067S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBENCVIP.
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

Module PbviA := BndP_Eb_066S9.LibSegEb_bviA.
Definition KS_bviA : list nat := Eval vm_compute in (BG.kept_list 80 PbviA.regs0 PbviA.regs_out0).
Lemma KS_bviA_ok : BG.kept_ok 80 PbviA.regs0 PbviA.regs_out0 KS_bviA = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac3a0 M) (st fx' R' 0x5edb0 M')
        /\ (forall x, In x KS_bviA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705548
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 96
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 10)
        /\ getr R' (reg 20) = getr R (reg 11)
        /\ getr R' (reg 24) = Z_to_bv 64 2147450880
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
  intros pvzI1 G2 K0 K1 K2 pvzI2 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K3l; move K3l before pvzI2; pose proof (proj2 pvzI2) as K3r; move K3r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PbviA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviA.kn0).
  { unfold know_ok, PbviA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbviA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviA.ps0) with 0x5edb0 in Hms. change (SR.ps_regs PbviA.ps0) with (map (fun i => (i, nth i PbviA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviA.ps0) with PbviA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviA.regs0 PbviA.regs_out0 80 KS_bviA KS_bviA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbviA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbviA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbviA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbviA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbviA.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PbviA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbviA.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PbviA.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbviA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbviDp8 := BndP_Eb_066S9.LibSegEb_bviDp8.
Definition KS_bviDp8 : list nat := Eval vm_compute in (BG.kept_list 80 PbviDp8.regs0 PbviDp8.regs_out0).
Lemma KS_bviDp8_ok : BG.kept_ok 80 PbviDp8.regs0 PbviDp8.regs_out0 KS_bviDp8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviDp8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 0 <= (V 11%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac40c M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bviDp8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705932
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 89)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 47%nat) + 64)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G19 G20 G24 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 K21 K22 pvzI12 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI13 K34 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K33l; move K33l before pvzI13; pose proof (proj2 pvzI13) as K33r; move K33r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 41%nat => vz_41 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviDp8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviDp8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviDp8.kn0).
  { unfold know_ok, PbviDp8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviDp8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviDp8.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 40) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbviDp8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviDp8.ps0) with 0xb120c in Hms. change (SR.ps_regs PbviDp8.ps0) with (map (fun i => (i, nth i PbviDp8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviDp8.ps0) with PbviDp8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviDp8.regs0 PbviDp8.regs_out0 80 KS_bviDp8 KS_bviDp8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviDp8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviDp8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviDp8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviDp8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp8.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbviDp8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp8.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbviDp8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp8.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbviDp8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp8.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbviDp8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp8.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbviDp8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbviDp16 := BndP_Eb_066S9.LibSegEb_bviDp16.
Definition KS_bviDp16 : list nat := Eval vm_compute in (BG.kept_list 80 PbviDp16.regs0 PbviDp16.regs_out0).
Lemma KS_bviDp16_ok : BG.kept_ok 80 PbviDp16.regs0 PbviDp16.regs_out0 KS_bviDp16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviDp16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 256 <= (V 11%nat) <= 32767 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac40c M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bviDp16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 706140
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 89)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G19 G20 G24 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 K21 K22 pvzI12 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI13 K34 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K33l; move K33l before pvzI13; pose proof (proj2 pvzI13) as K33r; move K33r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 41%nat => vz_41 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviDp16.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviDp16.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviDp16.kn0).
  { unfold know_ok, PbviDp16.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviDp16.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviDp16.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 40) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbviDp16.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviDp16.ps0) with 0xb120c in Hms. change (SR.ps_regs PbviDp16.ps0) with (map (fun i => (i, nth i PbviDp16.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviDp16.ps0) with PbviDp16.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviDp16.regs0 PbviDp16.regs_out0 80 KS_bviDp16 KS_bviDp16_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviDp16.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviDp16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp16.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviDp16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp16.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviDp16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp16.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbviDp16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp16.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbviDp16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp16.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbviDp16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp16.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbviDp16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbviDp32 := BndP_Eb_066S9.LibSegEb_bviDp32.
Definition KS_bviDp32 : list nat := Eval vm_compute in (BG.kept_list 80 PbviDp32.regs0 PbviDp32.regs_out0).
Lemma KS_bviDp32_ok : BG.kept_ok 80 PbviDp32.regs0 PbviDp32.regs_out0 KS_bviDp32 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviDp32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 32768 <= (V 11%nat) <= 2147483647 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac40c M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bviDp32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 706176
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 89)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G19 G20 G24 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 K21 K22 pvzI12 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI13 K34 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K33l; move K33l before pvzI13; pose proof (proj2 pvzI13) as K33r; move K33r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 41%nat => vz_41 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviDp32.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviDp32.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviDp32.kn0).
  { unfold know_ok, PbviDp32.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviDp32.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviDp32.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 40) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbviDp32.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviDp32.ps0) with 0xb120c in Hms. change (SR.ps_regs PbviDp32.ps0) with (map (fun i => (i, nth i PbviDp32.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviDp32.ps0) with PbviDp32.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviDp32.regs0 PbviDp32.regs_out0 80 KS_bviDp32 KS_bviDp32_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviDp32.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviDp32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp32.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviDp32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp32.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviDp32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp32.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbviDp32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp32.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbviDp32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp32.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbviDp32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp32.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbviDp32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbviDp64 := BndP_Eb_066S9.LibSegEb_bviDp64.
Definition KS_bviDp64 : list nat := Eval vm_compute in (BG.kept_list 80 PbviDp64.regs0 PbviDp64.regs_out0).
Lemma KS_bviDp64_ok : BG.kept_ok 80 PbviDp64.regs0 PbviDp64.regs_out0 KS_bviDp64 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviDp64_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 2147483648 <= (V 11%nat) <= 9223372036854775807 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac40c M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bviDp64 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705864
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 89)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G19 G20 G24 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 K21 K22 pvzI12 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI13 K34 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K33l; move K33l before pvzI13; pose proof (proj2 pvzI13) as K33r; move K33r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 41%nat => vz_41 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviDp64.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviDp64.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviDp64.kn0).
  { unfold know_ok, PbviDp64.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviDp64.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviDp64.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 40) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbviDp64.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviDp64.ps0) with 0xb120c in Hms. change (SR.ps_regs PbviDp64.ps0) with (map (fun i => (i, nth i PbviDp64.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviDp64.ps0) with PbviDp64.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviDp64.regs0 PbviDp64.regs_out0 80 KS_bviDp64 KS_bviDp64_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviDp64.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviDp64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp64.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviDp64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp64.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviDp64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp64.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbviDp64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp64.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbviDp64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp64.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbviDp64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDp64.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbviDp64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbviDn8 := BndP_Eb_066S9.LibSegEb_bviDn8.
Definition KS_bviDn8 : list nat := Eval vm_compute in (BG.kept_list 80 PbviDn8.regs0 PbviDn8.regs_out0).
Lemma KS_bviDn8_ok : BG.kept_ok 80 PbviDn8.regs0 PbviDn8.regs_out0 KS_bviDn8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviDn8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 18446744073709551488 <= (V 11%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac40c M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bviDn8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 706020
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 89)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G19 G20 G24 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 K21 K22 pvzI12 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI13 K34 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K33l; move K33l before pvzI13; pose proof (proj2 pvzI13) as K33r; move K33r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 41%nat => vz_41 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviDn8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviDn8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviDn8.kn0).
  { unfold know_ok, PbviDn8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviDn8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviDn8.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 40) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbviDn8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviDn8.ps0) with 0xb120c in Hms. change (SR.ps_regs PbviDn8.ps0) with (map (fun i => (i, nth i PbviDn8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviDn8.ps0) with PbviDn8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviDn8.regs0 PbviDn8.regs_out0 80 KS_bviDn8 KS_bviDn8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviDn8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviDn8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviDn8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviDn8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn8.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbviDn8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn8.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbviDn8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn8.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbviDn8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn8.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbviDn8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn8.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbviDn8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbviDn16 := BndP_Eb_066S9.LibSegEb_bviDn16.
Definition KS_bviDn16 : list nat := Eval vm_compute in (BG.kept_list 80 PbviDn16.regs0 PbviDn16.regs_out0).
Lemma KS_bviDn16_ok : BG.kept_ok 80 PbviDn16.regs0 PbviDn16.regs_out0 KS_bviDn16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviDn16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 18446744073709518848 <= (V 11%nat) <= 18446744073709551487 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac40c M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bviDn16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 706140
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 89)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G19 G20 G24 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 K21 K22 pvzI12 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI13 K34 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K33l; move K33l before pvzI13; pose proof (proj2 pvzI13) as K33r; move K33r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 41%nat => vz_41 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviDn16.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviDn16.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviDn16.kn0).
  { unfold know_ok, PbviDn16.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviDn16.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviDn16.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 40) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbviDn16.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviDn16.ps0) with 0xb120c in Hms. change (SR.ps_regs PbviDn16.ps0) with (map (fun i => (i, nth i PbviDn16.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviDn16.ps0) with PbviDn16.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviDn16.regs0 PbviDn16.regs_out0 80 KS_bviDn16 KS_bviDn16_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviDn16.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviDn16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn16.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviDn16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn16.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviDn16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn16.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbviDn16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn16.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbviDn16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn16.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbviDn16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn16.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbviDn16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbviDn32 := BndP_Eb_066S9.LibSegEb_bviDn32.
Definition KS_bviDn32 : list nat := Eval vm_compute in (BG.kept_list 80 PbviDn32.regs0 PbviDn32.regs_out0).
Lemma KS_bviDn32_ok : BG.kept_ok 80 PbviDn32.regs0 PbviDn32.regs_out0 KS_bviDn32 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviDn32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 18446744071562067968 <= (V 11%nat) <= 18446744073709518847 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac40c M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bviDn32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 706176
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 89)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G19 G20 G24 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 K21 K22 pvzI12 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI13 K34 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K33l; move K33l before pvzI13; pose proof (proj2 pvzI13) as K33r; move K33r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 41%nat => vz_41 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviDn32.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviDn32.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviDn32.kn0).
  { unfold know_ok, PbviDn32.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviDn32.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviDn32.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 40) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbviDn32.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviDn32.ps0) with 0xb120c in Hms. change (SR.ps_regs PbviDn32.ps0) with (map (fun i => (i, nth i PbviDn32.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviDn32.ps0) with PbviDn32.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviDn32.regs0 PbviDn32.regs_out0 80 KS_bviDn32 KS_bviDn32_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviDn32.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviDn32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn32.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviDn32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn32.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviDn32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn32.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbviDn32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn32.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbviDn32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn32.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbviDn32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn32.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbviDn32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbviDn64 := BndP_Eb_066S9.LibSegEb_bviDn64.
Definition KS_bviDn64 : list nat := Eval vm_compute in (BG.kept_list 80 PbviDn64.regs0 PbviDn64.regs_out0).
Lemma KS_bviDn64_ok : BG.kept_ok 80 PbviDn64.regs0 PbviDn64.regs_out0 KS_bviDn64 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviDn64_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 9223372036854775808 <= (V 11%nat) <= 18446744071562067967 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac40c M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bviDn64 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705864
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 89)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G19 G20 G24 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 K21 K22 pvzI12 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI13 K34 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K33l; move K33l before pvzI13; pose proof (proj2 pvzI13) as K33r; move K33r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 41%nat => vz_41 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviDn64.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviDn64.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviDn64.kn0).
  { unfold know_ok, PbviDn64.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviDn64.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviDn64.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 40) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbviDn64.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviDn64.ps0) with 0xb120c in Hms. change (SR.ps_regs PbviDn64.ps0) with (map (fun i => (i, nth i PbviDn64.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviDn64.ps0) with PbviDn64.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviDn64.regs0 PbviDn64.regs_out0 80 KS_bviDn64 KS_bviDn64_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviDn64.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviDn64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn64.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviDn64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn64.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviDn64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn64.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbviDn64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn64.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbviDn64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn64.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbviDn64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviDn64.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbviDn64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbviPp8 := BndP_Eb_067S9.LibSegEb_bviPp8.
Definition KS_bviPp8 : list nat := Eval vm_compute in (BG.kept_list 80 PbviPp8.regs0 PbviPp8.regs_out0).
Lemma KS_bviPp8_ok : BG.kept_ok 80 PbviPp8.regs0 PbviPp8.regs_out0 KS_bviPp8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviPp8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 64) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  0 <= (V 11%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 89) <= bv_unsigned a < ((V 2%nat) - 89) + 1) -> ~ (((V 47%nat) + 64) <= bv_unsigned a < ((V 47%nat) + 64) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 8) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 89) <= i < ((V 2%nat) - 89) + 1) -> ~ (((V 47%nat) + 64) <= i < ((V 47%nat) + 64) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 8) <= i < ((((V 47%nat) / 8) + 2147450880) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac58c M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bviPp8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705956
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 64)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 89)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 64) ((V 10%nat) + 8)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G24 G25 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 K17 K18 K19 K20 K21 pvzI12 K23 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K22l; move K22l before pvzI12; pose proof (proj2 pvzI12) as K22r; move K22r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K24l; move K24l before pvzI13; pose proof (proj2 pvzI13) as K24r; move K24r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviPp8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviPp8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviPp8.kn0).
  { unfold know_ok, PbviPp8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviPp8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviPp8.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 89) <= bv_unsigned a < (vz_2 - 89) + 1) -> ~ ((vz_47 + 64) <= bv_unsigned a < (vz_47 + 64) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 8) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbviPp8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviPp8.ps0) with 0xb2794 in Hms. change (SR.ps_regs PbviPp8.ps0) with (map (fun i => (i, nth i PbviPp8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviPp8.ps0) with PbviPp8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviPp8.regs0 PbviPp8.regs_out0 80 KS_bviPp8 KS_bviPp8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviPp8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviPp8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviPp8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviPp8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviPp8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviPp8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PbviJp8 := BndP_Eb_067S9.LibSegEb_bviJp8.
Definition KS_bviJp8 : list nat := Eval vm_compute in (BG.kept_list 80 PbviJp8.regs0 PbviJp8.regs_out0).
Lemma KS_bviJp8_ok : BG.kept_ok 80 PbviJp8.regs0 PbviJp8.regs_out0 KS_bviJp8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviJp8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 8) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 8) <= i < ((((V 47%nat) / 8) + 2147450880) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac5a4 M) (st fx' R' 0xac68c M')
        /\ (forall x, In x KS_bviJp8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 K17 K18 K19 K20 K21 pvzI12 K23.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K22l; move K22l before pvzI12; pose proof (proj2 pvzI12) as K22r; move K22r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviJp8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviJp8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviJp8.kn0).
  { unfold know_ok, PbviJp8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | clear; lia | exact K23]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviJp8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviJp8.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 8) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 8) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbviJp8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviJp8.ps0) with 0xac68c in Hms. change (SR.ps_regs PbviJp8.ps0) with (map (fun i => (i, nth i PbviJp8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviJp8.ps0) with PbviJp8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviJp8.regs0 PbviJp8.regs_out0 80 KS_bviJp8 KS_bviJp8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviJp8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviJp8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbviPn8 := BndP_Eb_067S9.LibSegEb_bviPn8.
Definition KS_bviPn8 : list nat := Eval vm_compute in (BG.kept_list 80 PbviPn8.regs0 PbviPn8.regs_out0).
Lemma KS_bviPn8_ok : BG.kept_ok 80 PbviPn8.regs0 PbviPn8.regs_out0 KS_bviPn8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviPn8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  18446744073709551488 <= (V 11%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 89) <= bv_unsigned a < ((V 2%nat) - 89) + 1) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 89) <= i < ((V 2%nat) - 89) + 1) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= i < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac5e4 M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bviPn8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 706044
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 89)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) ((V 10%nat) + 8)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G24 G25 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 K17 K18 K19 K20 K21 pvzI12 K23 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K22l; move K22l before pvzI12; pose proof (proj2 pvzI12) as K22r; move K22r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K24l; move K24l before pvzI13; pose proof (proj2 pvzI13) as K24r; move K24r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviPn8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviPn8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviPn8.kn0).
  { unfold know_ok, PbviPn8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviPn8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviPn8.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 89) <= bv_unsigned a < (vz_2 - 89) + 1) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbviPn8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviPn8.ps0) with 0xb2794 in Hms. change (SR.ps_regs PbviPn8.ps0) with (map (fun i => (i, nth i PbviPn8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviPn8.ps0) with PbviPn8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviPn8.regs0 PbviPn8.regs_out0 80 KS_bviPn8 KS_bviPn8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviPn8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviPn8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviPn8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviPn8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviPn8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviPn8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PbviJn8 := BndP_Eb_067S9.LibSegEb_bviJn8.
Definition KS_bviJn8 : list nat := Eval vm_compute in (BG.kept_list 80 PbviJn8.regs0 PbviJn8.regs_out0).
Lemma KS_bviJn8_ok : BG.kept_ok 80 PbviJn8.regs0 PbviJn8.regs_out0 KS_bviJn8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviJn8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= i < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac5fc M) (st fx' R' 0xac68c M')
        /\ (forall x, In x KS_bviJn8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 K17 K18 K19 K20 K21 pvzI12 K23.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K22l; move K22l before pvzI12; pose proof (proj2 pvzI12) as K22r; move K22r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviJn8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviJn8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviJn8.kn0).
  { unfold know_ok, PbviJn8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | clear; lia | exact K23]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviJn8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviJn8.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbviJn8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviJn8.ps0) with 0xac68c in Hms. change (SR.ps_regs PbviJn8.ps0) with (map (fun i => (i, nth i PbviJn8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviJn8.ps0) with PbviJn8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviJn8.regs0 PbviJn8.regs_out0 80 KS_bviJn8 KS_bviJn8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviJn8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviJn8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbviW16 := BndP_Eb_067S9.LibSegEb_bviW16.
Definition KS_bviW16 : list nat := Eval vm_compute in (BG.kept_list 80 PbviW16.regs0 PbviW16.regs_out0).
Lemma KS_bviW16_ok : BG.kept_ok 80 PbviW16.regs0 PbviW16.regs_out0 KS_bviW16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviW16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac65c M) (st fx' R' 0xb3614 M')
        /\ (forall x, In x KS_bviW16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 706152
        /\ getr R' (reg 10) = Z_to_bv 64 (V 11%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviW16.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviW16.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviW16.kn0).
  { unfold know_ok, PbviW16.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviW16.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviW16.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbviW16.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviW16.ps0) with 0xb3614 in Hms. change (SR.ps_regs PbviW16.ps0) with (map (fun i => (i, nth i PbviW16.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviW16.ps0) with PbviW16.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviW16.regs0 PbviW16.regs_out0 80 KS_bviW16 KS_bviW16_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviW16.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviW16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviW16.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviW16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbviW16.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviW16.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbviJ16 := BndP_Eb_066S9.LibSegEb_bviJ16.
Definition KS_bviJ16 : list nat := Eval vm_compute in (BG.kept_list 80 PbviJ16.regs0 PbviJ16.regs_out0).
Lemma KS_bviJ16_ok : BG.kept_ok 80 PbviJ16.regs0 PbviJ16.regs_out0 KS_bviJ16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviJ16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac668 M) (st fx' R' 0xac68c M')
        /\ (forall x, In x KS_bviJ16 -> getr R' (reg x) = getr R (reg x))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviJ16.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviJ16.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviJ16.kn0).
  { unfold know_ok, PbviJ16.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviJ16.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviJ16.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbviJ16.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviJ16.ps0) with 0xac68c in Hms. change (SR.ps_regs PbviJ16.ps0) with (map (fun i => (i, nth i PbviJ16.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviJ16.ps0) with PbviJ16.cells0 in Hcells.
  split. { exact Hms. }
  intros j Hj. apply (BG.kept_regs E E' R R' PbviJ16.regs0 PbviJ16.regs_out0 80 KS_bviJ16 KS_bviJ16_ok HR Hag Hregs j Hj).
Qed.

Module PbviW32 := BndP_Eb_067S9.LibSegEb_bviW32.
Definition KS_bviW32 : list nat := Eval vm_compute in (BG.kept_list 80 PbviW32.regs0 PbviW32.regs_out0).
Lemma KS_bviW32_ok : BG.kept_ok 80 PbviW32.regs0 PbviW32.regs_out0 KS_bviW32 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviW32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac680 M) (st fx' R' 0xb37f8 M')
        /\ (forall x, In x KS_bviW32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 706188
        /\ getr R' (reg 10) = Z_to_bv 64 (V 11%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviW32.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviW32.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviW32.kn0).
  { unfold know_ok, PbviW32.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviW32.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviW32.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbviW32.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviW32.ps0) with 0xb37f8 in Hms. change (SR.ps_regs PbviW32.ps0) with (map (fun i => (i, nth i PbviW32.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviW32.ps0) with PbviW32.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviW32.regs0 PbviW32.regs_out0 80 KS_bviW32 KS_bviW32_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviW32.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviW32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviW32.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviW32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbviW32.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviW32.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbviW64 := BndP_Eb_067S9.LibSegEb_bviW64.
Definition KS_bviW64 : list nat := Eval vm_compute in (BG.kept_list 80 PbviW64.regs0 PbviW64.regs_out0).
Lemma KS_bviW64_ok : BG.kept_ok 80 PbviW64.regs0 PbviW64.regs_out0 KS_bviW64 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviW64_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac548 M) (st fx' R' 0xb39f8 M')
        /\ (forall x, In x KS_bviW64 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705876
        /\ getr R' (reg 10) = Z_to_bv 64 (V 11%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviW64.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviW64.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviW64.kn0).
  { unfold know_ok, PbviW64.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviW64.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviW64.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbviW64.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviW64.ps0) with 0xb39f8 in Hms. change (SR.ps_regs PbviW64.ps0) with (map (fun i => (i, nth i PbviW64.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviW64.ps0) with PbviW64.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviW64.regs0 PbviW64.regs_out0 80 KS_bviW64 KS_bviW64_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviW64.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviW64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviW64.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviW64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbviW64.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviW64.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbviJ64 := BndP_Eb_066S9.LibSegEb_bviJ64.
Definition KS_bviJ64 : list nat := Eval vm_compute in (BG.kept_list 80 PbviJ64.regs0 PbviJ64.regs_out0).
Lemma KS_bviJ64_ok : BG.kept_ok 80 PbviJ64.regs0 PbviJ64.regs_out0 KS_bviJ64 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviJ64_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac554 M) (st fx' R' 0xac68c M')
        /\ (forall x, In x KS_bviJ64 -> getr R' (reg x) = getr R (reg x))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbviJ64.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviJ64.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviJ64.kn0).
  { unfold know_ok, PbviJ64.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviJ64.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviJ64.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbviJ64.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviJ64.ps0) with 0xac68c in Hms. change (SR.ps_regs PbviJ64.ps0) with (map (fun i => (i, nth i PbviJ64.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviJ64.ps0) with PbviJ64.cells0 in Hcells.
  split. { exact Hms. }
  intros j Hj. apply (BG.kept_regs E E' R R' PbviJ64.regs0 PbviJ64.regs_out0 80 KS_bviJ64 KS_bviJ64_ok HR Hag Hregs j Hj).
Qed.

Module PbviE0 := BndP_Eb_066S9.LibSegEb_bviE0.
Definition KS_bviE0 : list nat := Eval vm_compute in (BG.kept_list 80 PbviE0.regs0 PbviE0.regs_out0).
Lemma KS_bviE0_ok : BG.kept_ok 80 PbviE0.regs0 PbviE0.regs_out0 KS_bviE0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviE0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 38%nat) -> 0 <= (V 38%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac68c M) (st fx' R' 0xac7c0 M')
        /\ (forall x, In x KS_bviE0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI21 K4 K5 pvzI22 K7 K8 K9 K10 K11 K12 pvzI23 K14 K15 K16 K17 K18 K19 K20 K21 pvzI24 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI25 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV55l; move HV55l before pvzI7; pose proof (proj2 pvzI7) as HV55r; move HV55r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV64l; move HV64l before pvzI10; pose proof (proj2 pvzI10) as HV64r; move HV64r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV65l; move HV65l before pvzI11; pose proof (proj2 pvzI11) as HV65r; move HV65r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV66l; move HV66l before pvzI12; pose proof (proj2 pvzI12) as HV66r; move HV66r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV67l; move HV67l before pvzI13; pose proof (proj2 pvzI13) as HV67r; move HV67r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV68l; move HV68l before pvzI14; pose proof (proj2 pvzI14) as HV68r; move HV68r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV69l; move HV69l before pvzI15; pose proof (proj2 pvzI15) as HV69r; move HV69r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV70l; move HV70l before pvzI16; pose proof (proj2 pvzI16) as HV70r; move HV70r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV71l; move HV71l before pvzI17; pose proof (proj2 pvzI17) as HV71r; move HV71r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV72l; move HV72l before pvzI18; pose proof (proj2 pvzI18) as HV72r; move HV72r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV73l; move HV73l before pvzI19; pose proof (proj2 pvzI19) as HV73r; move HV73r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV74l; move HV74l before pvzI20; pose proof (proj2 pvzI20) as HV74r; move HV74r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K3l; move K3l before pvzI21; pose proof (proj2 pvzI21) as K3r; move K3r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K6l; move K6l before pvzI22; pose proof (proj2 pvzI22) as K6r; move K6r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K13l; move K13l before pvzI23; pose proof (proj2 pvzI23) as K13r; move K13r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K22l; move K22l before pvzI24; pose proof (proj2 pvzI24) as K22r; move K22r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E PbviE0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviE0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviE0.kn0).
  { unfold know_ok, PbviE0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K44]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviE0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviE0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbviE0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviE0.ps0) with 0xac7c0 in Hms. change (SR.ps_regs PbviE0.ps0) with (map (fun i => (i, nth i PbviE0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviE0.ps0) with PbviE0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviE0.regs0 PbviE0.regs_out0 80 KS_bviE0 KS_bviE0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE0.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbviE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbviE1 := BndP_Eb_066S9.LibSegEb_bviE1.
Definition KS_bviE1 : list nat := Eval vm_compute in (BG.kept_list 80 PbviE1.regs0 PbviE1.regs_out0).
Lemma KS_bviE1_ok : BG.kept_ok 80 PbviE1.regs0 PbviE1.regs_out0 KS_bviE1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 8) / 8) + 2147450880) 1 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551614 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac68c M) (st fx' R' 0xac7c0 M')
        /\ (forall x, In x KS_bviE1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) ((V 42%nat) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 pvzI22 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI23 K4 K5 pvzI24 K7 K8 K9 K10 K11 K12 pvzI25 K14 K15 K16 K17 K18 K19 K20 K21 pvzI26 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI27 pvzI28 K35 pvzI29 K37 K38 K39 K40 K41 K42 K43 K44 K45 pvzI30 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV47l; move HV47l before pvzI7; pose proof (proj2 pvzI7) as HV47r; move HV47r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV55l; move HV55l before pvzI9; pose proof (proj2 pvzI9) as HV55r; move HV55r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV56l; move HV56l before pvzI10; pose proof (proj2 pvzI10) as HV56r; move HV56r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV57l; move HV57l before pvzI11; pose proof (proj2 pvzI11) as HV57r; move HV57r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV64l; move HV64l before pvzI12; pose proof (proj2 pvzI12) as HV64r; move HV64r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV65l; move HV65l before pvzI13; pose proof (proj2 pvzI13) as HV65r; move HV65r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV66l; move HV66l before pvzI14; pose proof (proj2 pvzI14) as HV66r; move HV66r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV67l; move HV67l before pvzI15; pose proof (proj2 pvzI15) as HV67r; move HV67r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV68l; move HV68l before pvzI16; pose proof (proj2 pvzI16) as HV68r; move HV68r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV69l; move HV69l before pvzI17; pose proof (proj2 pvzI17) as HV69r; move HV69r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV70l; move HV70l before pvzI18; pose proof (proj2 pvzI18) as HV70r; move HV70r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV71l; move HV71l before pvzI19; pose proof (proj2 pvzI19) as HV71r; move HV71r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV72l; move HV72l before pvzI20; pose proof (proj2 pvzI20) as HV72r; move HV72r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV73l; move HV73l before pvzI21; pose proof (proj2 pvzI21) as HV73r; move HV73r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as HV74l; move HV74l before pvzI22; pose proof (proj2 pvzI22) as HV74r; move HV74r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K3l; move K3l before pvzI23; pose proof (proj2 pvzI23) as K3r; move K3r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K6l; move K6l before pvzI24; pose proof (proj2 pvzI24) as K6r; move K6r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K13l; move K13l before pvzI25; pose proof (proj2 pvzI25) as K13r; move K13r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K22l; move K22l before pvzI26; pose proof (proj2 pvzI26) as K22r; move K22r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K33l; move K33l before pvzI27; pose proof (proj2 pvzI27) as K33r; move K33r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K34l; move K34l before pvzI28; pose proof (proj2 pvzI28) as K34r; move K34r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K36l; move K36l before pvzI29; pose proof (proj2 pvzI29) as K36r; move K36r before pvzI29; clear pvzI29. pose proof (proj1 pvzI30) as K46l; move K46l before pvzI30; pose proof (proj2 pvzI30) as K46r; move K46r before pvzI30; clear pvzI30.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 42%nat => Z_to_bv 64 vz_42 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 38%nat => vz_38 | 39%nat => vz_39 | 42%nat => vz_42 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E PbviE1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviE1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviE1.kn0).
  { unfold know_ok, PbviE1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K36l K36r) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K36l K36r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K36l K36r HV39l HV39r K34l K34r K38 K40 K41 K42 K43 K44) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear - HV42l HV42r K46l K46r) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K46l K46r) | exact (conj K46l K46r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K57]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviE1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviE1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_39 - 8) <= bv_unsigned a < (vz_39 - 8) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbviE1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviE1.ps0) with 0xac7c0 in Hms. change (SR.ps_regs PbviE1.ps0) with (map (fun i => (i, nth i PbviE1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviE1.ps0) with PbviE1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviE1.regs0 PbviE1.regs_out0 80 KS_bviE1 KS_bviE1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbviE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K46l K46r) | clear; lia].
Qed.

Module PbviE1w := BndP_Eb_066S9.LibSegEb_bviE1w.
Definition KS_bviE1w : list nat := Eval vm_compute in (BG.kept_list 80 PbviE1w.regs0 PbviE1w.regs_out0).
Lemma KS_bviE1w_ok : BG.kept_ok 80 PbviE1w.regs0 PbviE1w.regs_out0 KS_bviE1w = true. Proof. vm_compute. reflexivity. Qed.
Lemma bviE1w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 8) / 8) + 2147450880) 1 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac68c M) (st fx' R' 0xac7c0 M')
        /\ (forall x, In x KS_bviE1w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI22 K4 K5 pvzI23 K7 K8 K9 K10 K11 K12 pvzI24 K14 K15 K16 K17 K18 K19 K20 K21 pvzI25 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI26 pvzI27 K35 pvzI28 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV56l; move HV56l before pvzI9; pose proof (proj2 pvzI9) as HV56r; move HV56r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV57l; move HV57l before pvzI10; pose proof (proj2 pvzI10) as HV57r; move HV57r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV69l; move HV69l before pvzI16; pose proof (proj2 pvzI16) as HV69r; move HV69r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV70l; move HV70l before pvzI17; pose proof (proj2 pvzI17) as HV70r; move HV70r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV71l; move HV71l before pvzI18; pose proof (proj2 pvzI18) as HV71r; move HV71r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV72l; move HV72l before pvzI19; pose proof (proj2 pvzI19) as HV72r; move HV72r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV73l; move HV73l before pvzI20; pose proof (proj2 pvzI20) as HV73r; move HV73r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV74l; move HV74l before pvzI21; pose proof (proj2 pvzI21) as HV74r; move HV74r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K6l; move K6l before pvzI23; pose proof (proj2 pvzI23) as K6r; move K6r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K13l; move K13l before pvzI24; pose proof (proj2 pvzI24) as K13r; move K13r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K22l; move K22l before pvzI25; pose proof (proj2 pvzI25) as K22r; move K22r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K33l; move K33l before pvzI26; pose proof (proj2 pvzI26) as K33r; move K33r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K34l; move K34l before pvzI27; pose proof (proj2 pvzI27) as K34r; move K34r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K36l; move K36l before pvzI28; pose proof (proj2 pvzI28) as K36r; move K36r before pvzI28; clear pvzI28.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 38%nat => vz_38 | 39%nat => vz_39 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E PbviE1w.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbviE1w.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbviE1w.kn0).
  { unfold know_ok, PbviE1w.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K36l K36r) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K36l K36r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K36l K36r HV39l HV39r K34l K34r K38 K40 K41 K42 K43 K44) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K56]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbviE1w.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbviE1w.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_39 - 8) <= bv_unsigned a < (vz_39 - 8) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbviE1w.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbviE1w.ps0) with 0xac7c0 in Hms. change (SR.ps_regs PbviE1w.ps0) with (map (fun i => (i, nth i PbviE1w.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbviE1w.ps0) with PbviE1w.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbviE1w.regs0 PbviE1w.regs_out0 80 KS_bviE1w KS_bviE1w_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbviE1w.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbviE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

End PEBENCVIP.
