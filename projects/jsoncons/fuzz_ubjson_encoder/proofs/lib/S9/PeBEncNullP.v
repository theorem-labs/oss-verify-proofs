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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_074S9 BndP_Eb_075S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBENCNP.
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

Module PbvnA := BndP_Eb_074S9.LibSegEb_bvnA.
Definition KS_bvnA : list nat := Eval vm_compute in (BG.kept_list 80 PbvnA.regs0 PbvnA.regs_out0).
Lemma KS_bvnA_ok : BG.kept_ok 80 PbvnA.regs0 PbvnA.regs_out0 KS_bvnA = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvnA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad588 M) (st fx' R' 0x5ec3c M')
        /\ (forall x, In x KS_bvnA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710120
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 10)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
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
  assert (HR: regs_ok E PbvnA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvnA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvnA.kn0).
  { unfold know_ok, PbvnA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvnA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvnA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbvnA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvnA.ps0) with 0x5ec3c in Hms. change (SR.ps_regs PbvnA.ps0) with (map (fun i => (i, nth i PbvnA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvnA.ps0) with PbvnA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvnA.regs0 PbvnA.regs_out0 80 KS_bvnA KS_bvnA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvnA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbvnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbvnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbvnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbvnA.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PbvnA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbvnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbvnB := BndP_Eb_075S9.LibSegEb_bvnB.
Definition KS_bvnB : list nat := Eval vm_compute in (BG.kept_list 80 PbvnB.regs0 PbvnB.regs_out0).
Lemma KS_bvnB_ok : BG.kept_ok 80 PbvnB.regs0 PbvnB.regs_out0 KS_bvnB = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvnB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 96) + 96 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 96)) -> (((V 2%nat) - 96) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 96)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 24) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 24) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad5e8 M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bvnB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710292
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 73)
        /\ getr R' (reg 12) = Z_to_bv 64 75534
        /\ getr R' (reg 13) = Z_to_bv 64 710024
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 18446744073709551608
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) ((V 10%nat) + 8)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G11 G12 G19 G20 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 K21 K22 pvzI10 K24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV47l; move HV47l before pvzI3; pose proof (proj2 pvzI3) as HV47r; move HV47r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV48l; move HV48l before pvzI4; pose proof (proj2 pvzI4) as HV48r; move HV48r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV56l; move HV56l before pvzI5; pose proof (proj2 pvzI5) as HV56r; move HV56r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV57l; move HV57l before pvzI6; pose proof (proj2 pvzI6) as HV57r; move HV57r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K23l; move K23l before pvzI10; pose proof (proj2 pvzI10) as K23r; move K23r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbvnB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvnB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvnB.kn0).
  { unfold know_ok, PbvnB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | exactA K5]. }
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
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r) | clear; lia | exact K24]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvnB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvnB.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 24) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbvnB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvnB.ps0) with 0xb2794 in Hms. change (SR.ps_regs PbvnB.ps0) with (map (fun i => (i, nth i PbvnB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvnB.ps0) with PbvnB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvnB.regs0 PbvnB.regs_out0 80 KS_bvnB KS_bvnB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvnB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbvnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbvnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbvnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbvnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbvnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnB.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbvnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbvnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PbvnE0 := BndP_Eb_075S9.LibSegEb_bvnE0.
Definition KS_bvnE0 : list nat := Eval vm_compute in (BG.kept_list 80 PbvnE0.regs0 PbvnE0.regs_out0).
Lemma KS_bvnE0_ok : BG.kept_ok 80 PbvnE0.regs0 PbvnE0.regs_out0 KS_bvnE0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvnE0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 47%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 96) + 96 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 96)) -> (((V 2%nat) - 96) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 96)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 96)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 38%nat) -> 0 <= (V 38%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad694 M) (st fx' R' 0xad794 M')
        /\ (forall x, In x KS_bvnE0 -> getr R' (reg x) = getr R (reg x))
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
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 K0 K1 K2 pvzI18 K4 K5 pvzI19 K7 K8 K9 K10 K11 K12 pvzI20 K14 K15 K16 K17 K18 K19 K20 K21 pvzI21 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI22 K34 K35 K36 K37 K38 K39 K40 K41 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV69l; move HV69l before pvzI14; pose proof (proj2 pvzI14) as HV69r; move HV69r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV70l; move HV70l before pvzI15; pose proof (proj2 pvzI15) as HV70r; move HV70r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV71l; move HV71l before pvzI16; pose proof (proj2 pvzI16) as HV71r; move HV71r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV72l; move HV72l before pvzI17; pose proof (proj2 pvzI17) as HV72r; move HV72r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K3l; move K3l before pvzI18; pose proof (proj2 pvzI18) as K3r; move K3r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K6l; move K6l before pvzI19; pose proof (proj2 pvzI19) as K6r; move K6r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K13l; move K13l before pvzI20; pose proof (proj2 pvzI20) as K13r; move K13r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K22l; move K22l before pvzI21; pose proof (proj2 pvzI21) as K22r; move K22r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K33l; move K33l before pvzI22; pose proof (proj2 pvzI22) as K33r; move K33r before pvzI22; clear pvzI22.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PbvnE0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvnE0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvnE0.kn0).
  { unfold know_ok, PbvnE0.kn0.
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
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvnE0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvnE0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbvnE0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvnE0.ps0) with 0xad794 in Hms. change (SR.ps_regs PbvnE0.ps0) with (map (fun i => (i, nth i PbvnE0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvnE0.ps0) with PbvnE0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvnE0.regs0 PbvnE0.regs_out0 80 KS_bvnE0 KS_bvnE0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvnE0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvnE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbvnE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbvnE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbvnE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvnE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvnE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvnE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbvnE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbvnE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbvnE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbvnE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbvnE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbvnE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbvnE1 := BndP_Eb_075S9.LibSegEb_bvnE1.
Definition KS_bvnE1 : list nat := Eval vm_compute in (BG.kept_list 80 PbvnE1.regs0 PbvnE1.regs_out0).
Lemma KS_bvnE1_ok : BG.kept_ok 80 PbvnE1.regs0 PbvnE1.regs_out0 KS_bvnE1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvnE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 47%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 96) + 96 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 96)) -> (((V 2%nat) - 96) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 96)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 96)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 8) / 8) + 2147450880) 1 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551614 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad694 M) (st fx' R' 0xad794 M')
        /\ (forall x, In x KS_bvnE1 -> getr R' (reg x) = getr R (reg x))
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
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) ((V 42%nat) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 pvzI22 K14 K15 K16 K17 K18 K19 K20 K21 pvzI23 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI24 pvzI25 K35 pvzI26 K37 K38 K39 K40 K41 K42 K43 K44 K45 pvzI27 K47 K48 K49 K50 K51 K52 K53 K54 K55.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV39l; move HV39l before pvzI4; pose proof (proj2 pvzI4) as HV39r; move HV39r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV56l; move HV56l before pvzI9; pose proof (proj2 pvzI9) as HV56r; move HV56r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV57l; move HV57l before pvzI10; pose proof (proj2 pvzI10) as HV57r; move HV57r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV69l; move HV69l before pvzI16; pose proof (proj2 pvzI16) as HV69r; move HV69r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV70l; move HV70l before pvzI17; pose proof (proj2 pvzI17) as HV70r; move HV70r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV71l; move HV71l before pvzI18; pose proof (proj2 pvzI18) as HV71r; move HV71r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV72l; move HV72l before pvzI19; pose proof (proj2 pvzI19) as HV72r; move HV72r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K13l; move K13l before pvzI22; pose proof (proj2 pvzI22) as K13r; move K13r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K22l; move K22l before pvzI23; pose proof (proj2 pvzI23) as K22r; move K22r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K33l; move K33l before pvzI24; pose proof (proj2 pvzI24) as K33r; move K33r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K34l; move K34l before pvzI25; pose proof (proj2 pvzI25) as K34r; move K34r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K36l; move K36l before pvzI26; pose proof (proj2 pvzI26) as K36r; move K36r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K46l; move K46l before pvzI27; pose proof (proj2 pvzI27) as K46r; move K46r before pvzI27; clear pvzI27.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 42%nat => Z_to_bv 64 vz_42 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 38%nat => vz_38 | 39%nat => vz_39 | 42%nat => vz_42 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PbvnE1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvnE1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvnE1.kn0).
  { unfold know_ok, PbvnE1.kn0.
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
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvnE1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvnE1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_39 - 8) <= bv_unsigned a < (vz_39 - 8) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbvnE1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvnE1.ps0) with 0xad794 in Hms. change (SR.ps_regs PbvnE1.ps0) with (map (fun i => (i, nth i PbvnE1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvnE1.ps0) with PbvnE1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvnE1.regs0 PbvnE1.regs_out0 80 KS_bvnE1 KS_bvnE1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvnE1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvnE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbvnE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbvnE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbvnE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvnE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvnE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvnE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbvnE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbvnE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbvnE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbvnE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbvnE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbvnE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K46l K46r) | clear; lia].
Qed.

Module PbvnE1w := BndP_Eb_075S9.LibSegEb_bvnE1w.
Definition KS_bvnE1w : list nat := Eval vm_compute in (BG.kept_list 80 PbvnE1w.regs0 PbvnE1w.regs_out0).
Lemma KS_bvnE1w_ok : BG.kept_ok 80 PbvnE1w.regs0 PbvnE1w.regs_out0 KS_bvnE1w = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvnE1w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 47%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 96) + 96 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 96)) -> (((V 2%nat) - 96) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 96)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 96)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 8) / 8) + 2147450880) 1 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad694 M) (st fx' R' 0xad794 M')
        /\ (forall x, In x KS_bvnE1w -> getr R' (reg x) = getr R (reg x))
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
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 K0 K1 K2 pvzI19 K4 K5 pvzI20 K7 K8 K9 K10 K11 K12 pvzI21 K14 K15 K16 K17 K18 K19 K20 K21 pvzI22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI23 pvzI24 K35 pvzI25 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV39l; move HV39l before pvzI4; pose proof (proj2 pvzI4) as HV39r; move HV39r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV55l; move HV55l before pvzI7; pose proof (proj2 pvzI7) as HV55r; move HV55r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV64l; move HV64l before pvzI10; pose proof (proj2 pvzI10) as HV64r; move HV64r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV65l; move HV65l before pvzI11; pose proof (proj2 pvzI11) as HV65r; move HV65r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV66l; move HV66l before pvzI12; pose proof (proj2 pvzI12) as HV66r; move HV66r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV67l; move HV67l before pvzI13; pose proof (proj2 pvzI13) as HV67r; move HV67r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV68l; move HV68l before pvzI14; pose proof (proj2 pvzI14) as HV68r; move HV68r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV69l; move HV69l before pvzI15; pose proof (proj2 pvzI15) as HV69r; move HV69r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV70l; move HV70l before pvzI16; pose proof (proj2 pvzI16) as HV70r; move HV70r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV71l; move HV71l before pvzI17; pose proof (proj2 pvzI17) as HV71r; move HV71r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV72l; move HV72l before pvzI18; pose proof (proj2 pvzI18) as HV72r; move HV72r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K13l; move K13l before pvzI21; pose proof (proj2 pvzI21) as K13r; move K13r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K22l; move K22l before pvzI22; pose proof (proj2 pvzI22) as K22r; move K22r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K33l; move K33l before pvzI23; pose proof (proj2 pvzI23) as K33r; move K33r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K34l; move K34l before pvzI24; pose proof (proj2 pvzI24) as K34r; move K34r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K36l; move K36l before pvzI25; pose proof (proj2 pvzI25) as K36r; move K36r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 38%nat => vz_38 | 39%nat => vz_39 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PbvnE1w.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvnE1w.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvnE1w.kn0).
  { unfold know_ok, PbvnE1w.kn0.
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
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvnE1w.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvnE1w.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_39 - 8) <= bv_unsigned a < (vz_39 - 8) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbvnE1w.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvnE1w.ps0) with 0xad794 in Hms. change (SR.ps_regs PbvnE1w.ps0) with (map (fun i => (i, nth i PbvnE1w.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvnE1w.ps0) with PbvnE1w.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvnE1w.regs0 PbvnE1w.regs_out0 80 KS_bvnE1w KS_bvnE1w_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvnE1w.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvnE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1w.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbvnE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1w.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbvnE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1w.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbvnE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1w.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvnE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1w.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvnE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1w.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvnE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1w.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbvnE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1w.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbvnE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1w.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbvnE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1w.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbvnE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1w.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbvnE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvnE1w.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbvnE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

End PEBENCNP.
