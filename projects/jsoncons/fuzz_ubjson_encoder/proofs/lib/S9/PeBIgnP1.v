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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_018S9 BndP_Eb_019S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMBIGP1.
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

Module PbigA := BndP_Eb_018S9.LibSegEb_bigA.
Definition KS_bigA : list nat := Eval vm_compute in (BG.kept_list 80 PbigA.regs0 PbigA.regs_out0).
Lemma KS_bigA_ok : BG.kept_ok 80 PbigA.regs0 PbigA.regs_out0 KS_bigA = true. Proof. vm_compute. reflexivity. Qed.
Lemma bigA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 1 ->
  140735332487360 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb87bc M) (st fx' R' 0xb87fc M')
        /\ (forall x, In x KS_bigA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 0).
Proof.
  intros pvzI1 pvzI2 G2 G10 G11 pvzI3 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PbigA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbigA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbigA.kn0).
  { unfold know_ok, PbigA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbigA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbigA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbigA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbigA.ps0) with 0xb87fc in Hms. change (SR.ps_regs PbigA.ps0) with (map (fun i => (i, nth i PbigA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbigA.ps0) with PbigA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbigA.regs0 PbigA.regs_out0 80 KS_bigA KS_bigA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbigA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbigA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbigA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbigA2 := BndP_Eb_018S9.LibSegEb_bigA2.
Definition KS_bigA2 : list nat := Eval vm_compute in (BG.kept_list 80 PbigA2.regs0 PbigA2.regs_out0).
Lemma KS_bigA2_ok : BG.kept_ok 80 PbigA2.regs0 PbigA2.regs_out0 KS_bigA2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bigA2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 1 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355136 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 96 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 56) <= bv_unsigned a < ((V 50%nat) + 56) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 56) <= i < ((V 50%nat) + 56) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb8800 M) (st fx' R' 0x5edb0 M')
        /\ (forall x, In x KS_bigA2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 755764
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 96
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 2147450880
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 56) 2147450880).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G10 G11 K0 K1 K2 pvzI4 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV50l; move HV50l before pvzI3; pose proof (proj2 pvzI3) as HV50r; move HV50r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbigA2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbigA2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbigA2.kn0).
  { unfold know_ok, PbigA2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r; lia | clear - HV50l HV50r K3l K3r; lia | clear - HV50l HV50r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbigA2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbigA2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 56) <= bv_unsigned a < (vz_50 + 56) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbigA2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbigA2.ps0) with 0x5edb0 in Hms. change (SR.ps_regs PbigA2.ps0) with (map (fun i => (i, nth i PbigA2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbigA2.ps0) with PbigA2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbigA2.regs0 PbigA2.regs_out0 80 KS_bigA2 KS_bigA2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbigA2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbigA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigA2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbigA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigA2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbigA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigA2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbigA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigA2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbigA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigA2.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PbigA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigA2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbigA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigA2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbigA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbigB0 := BndP_Eb_019S9.LibSegEb_bigB0.
Definition KS_bigB0 : list nat := Eval vm_compute in (BG.kept_list 80 PbigB0.regs0 PbigB0.regs_out0).
Lemma KS_bigB0_ok : BG.kept_ok 80 PbigB0.regs0 PbigB0.regs_out0 KS_bigB0 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bigB0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 50%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 1 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355136 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 96 -> L5.u64_at RSEGS M ((V 50%nat) + 56) 2147450880 -> 6930432 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  ((V 50%nat) + 96 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 50%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.defined M ((V 36%nat) + 256) 8 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> 6930432 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> ((V 36%nat) + 296 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 36%nat)) -> ((V 36%nat) + 296 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 37 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 50%nat) + 96 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 50%nat)) -> ((V 50%nat) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 50%nat)) -> ((V 47%nat) + 128 <= 65536 \/ 65536 + 1204292 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 88) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 88) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb8834 M) (st fx' R' 0xb9944 M')
        /\ (forall x, In x KS_bigB0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756252
        /\ getr R' (reg 5) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 16384
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551602
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 16) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 2147450880
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 280)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 36%nat) + 256)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 47%nat) + 64)
        /\ getr R' (reg 25) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 24) ((((V 36%nat) + 256) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 32) ((((V 36%nat) + 272) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 40) ((((V 36%nat) + 264) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' (V 50%nat) ((V 36%nat) + 272)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 48) ((V 36%nat) + 264)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 80) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 755644
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 134988
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 56) 2147450880
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.defined M' ((V 47%nat) + 24) 8
        /\ L5.defined M' ((V 47%nat) + 40) 88
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G19 G23 K0 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 pvzI10 K19 K20 K21 K22 K23 K24 K25 pvzI11 K27 K28 K29 K30 K31 K32 K33 K34 K35.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K18l; move K18l before pvzI10; pose proof (proj2 pvzI10) as K18r; move K18r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K26l; move K26l before pvzI11; pose proof (proj2 pvzI11) as K26r; move K26r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbigB0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbigB0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbigB0.kn0).
  { unfold know_ok, PbigB0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K23]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K26l K26r K28 K29 K31 K34; lia | clear - HV48l HV48r K26l K26r K28 K29 K31 K34; lia | clear - HV48l HV48r K26l K26r K28 K29 K31 K34; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbigB0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbigB0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 88) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PbigB0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K12 K33 K34 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32 Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbigB0.ps0) with 0xb9944 in Hms. change (SR.ps_regs PbigB0.ps0) with (map (fun i => (i, nth i PbigB0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbigB0.ps0) with PbigB0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbigB0.regs0 PbigB0.regs_out0 80 KS_bigB0 KS_bigB0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB0.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbigB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbigB1a := BndP_Eb_019S9.LibSegEb_bigB1a.
Definition KS_bigB1a : list nat := Eval vm_compute in (BG.kept_list 80 PbigB1a.regs0 PbigB1a.regs_out0).
Lemma KS_bigB1a_ok : BG.kept_ok 80 PbigB1a.regs0 PbigB1a.regs_out0 KS_bigB1a = true. Proof. vm_compute. reflexivity. Qed.
Lemma bigB1a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 50%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 1 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355136 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 96 -> L5.u64_at RSEGS M ((V 50%nat) + 56) 2147450880 -> 6930432 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  ((V 50%nat) + 96 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 50%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.defined M ((V 36%nat) + 256) 8 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 1 -> 6930432 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> ((V 36%nat) + 296 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 36%nat)) -> ((V 36%nat) + 296 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 37 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 50%nat) + 96 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 50%nat)) -> ((V 50%nat) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 50%nat)) -> ((V 47%nat) + 128 <= 65536 \/ 65536 + 1204292 <= (V 47%nat)) ->
  4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 88) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 88) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb8834 M) (st fx' R' 0xb8acc M')
        /\ (forall x, In x KS_bigB1a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 35%nat) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 16) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 2147450880
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 280)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 36%nat) + 256)
        /\ getr R' (reg 25) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) ((V 35%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 80) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 755644
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 134988
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 56) 2147450880
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.defined M' ((V 47%nat) + 24) 8
        /\ L5.defined M' ((V 47%nat) + 40) 88
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G19 G23 K0 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 pvzI10 K19 K20 K21 K22 K23 K24 K25 pvzI11 K27 K28 K29 K30 K31 K32 K33 K34 K35 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K18l; move K18l before pvzI10; pose proof (proj2 pvzI10) as K18r; move K18r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K26l; move K26l before pvzI11; pose proof (proj2 pvzI11) as K26r; move K26r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K36l; move K36l before pvzI12; pose proof (proj2 pvzI12) as K36r; move K36r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbigB1a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbigB1a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbigB1a.kn0).
  { unfold know_ok, PbigB1a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear - HV35l HV35r K36l K36r) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K23]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K26l K26r K28 K29 K31 K34; lia | clear - HV48l HV48r K26l K26r K28 K29 K31 K34; lia | clear - HV48l HV48r K26l K26r K28 K29 K31 K34; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbigB1a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbigB1a.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 88) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PbigB1a.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K12 K33 K34 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32 Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbigB1a.ps0) with 0xb8acc in Hms. change (SR.ps_regs PbigB1a.ps0) with (map (fun i => (i, nth i PbigB1a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbigB1a.ps0) with PbigB1a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbigB1a.regs0 PbigB1a.regs_out0 80 KS_bigB1a KS_bigB1a_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1a.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbigB1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K36l K36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbigB1b := BndP_Eb_019S9.LibSegEb_bigB1b.
Definition KS_bigB1b : list nat := Eval vm_compute in (BG.kept_list 80 PbigB1b.regs0 PbigB1b.regs_out0).
Lemma KS_bigB1b_ok : BG.kept_ok 80 PbigB1b.regs0 PbigB1b.regs_out0 KS_bigB1b = true. Proof. vm_compute. reflexivity. Qed.
Lemma bigB1b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 50%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 1 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355136 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 96 -> L5.u64_at RSEGS M ((V 50%nat) + 56) 2147450880 -> 6930432 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  ((V 50%nat) + 96 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 50%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.defined M ((V 36%nat) + 256) 8 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) -> 6930432 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> ((V 36%nat) + 296 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 36%nat)) -> ((V 36%nat) + 296 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 37 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 50%nat) + 96 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 50%nat)) -> ((V 50%nat) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 50%nat)) -> ((V 47%nat) + 128 <= 65536 \/ 65536 + 1204292 <= (V 47%nat)) ->
  2 <= (V 33%nat) <= 16384 -> 4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 88) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 88) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb8834 M) (st fx' R' 0xb8918 M')
        /\ (forall x, In x KS_bigB1b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 755644
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551602
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 16) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 2147450880
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 280)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 36%nat) + 256)
        /\ getr R' (reg 25) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 80) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 755644
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 134988
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 56) 2147450880
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) (V 33%nat)
        /\ L5.defined M' ((V 47%nat) + 24) 8
        /\ L5.defined M' ((V 47%nat) + 40) 88
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G19 G23 K0 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 pvzI11 K19 K20 K21 K22 K23 K24 K25 pvzI12 K27 K28 K29 K30 K31 K32 K33 K34 K35 pvzI13 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K18l; move K18l before pvzI11; pose proof (proj2 pvzI11) as K18r; move K18r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K26l; move K26l before pvzI12; pose proof (proj2 pvzI12) as K26r; move K26r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K36l; move K36l before pvzI13; pose proof (proj2 pvzI13) as K36r; move K36r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K37l; move K37l before pvzI14; pose proof (proj2 pvzI14) as K37r; move K37r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbigB1b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbigB1b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbigB1b.kn0).
  { unfold know_ok, PbigB1b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | clear - HV50l HV50r K3l K3r K12 K33 K34; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear - HV35l HV35r K37l K37r) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear - HV33l HV33r K36l K36r) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K23]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K26l K26r K28 K29 K31 K34; lia | clear - HV48l HV48r K26l K26r K28 K29 K31 K34; lia | clear - HV48l HV48r K26l K26r K28 K29 K31 K34; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbigB1b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbigB1b.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 88) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PbigB1b.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K12 K33 K34 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32 Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbigB1b.ps0) with 0xb8918 in Hms. change (SR.ps_regs PbigB1b.ps0) with (map (fun i => (i, nth i PbigB1b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbigB1b.ps0) with PbigB1b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbigB1b.regs0 PbigB1b.regs_out0 80 KS_bigB1b KS_bigB1b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbigB1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K12 K33 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K37l K37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r K9 K12 K30 K31 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K36l K36r) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K18l K18r K22 K29 K30 K32 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbigB1b2 := BndP_Eb_019S9.LibSegEb_bigB1b2.
Definition KS_bigB1b2 : list nat := Eval vm_compute in (BG.kept_list 80 PbigB1b2.regs0 PbigB1b2.regs_out0).
Lemma KS_bigB1b2_ok : BG.kept_ok 80 PbigB1b2.regs0 PbigB1b2.regs_out0 KS_bigB1b2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bigB1b2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 50%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 17) = Z_to_bv 64 2147450880 -> getr R (reg 18) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 280) -> getr R (reg 22) = Z_to_bv 64 ((V 36%nat) + 256) -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355136 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 96 -> 6930432 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> ((V 50%nat) + 96 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 50%nat)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.defined M ((V 36%nat) + 256) 8 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) ->
  L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) -> 2 <= (V 33%nat) <= 16384 -> 4096 <= (V 35%nat) <= 140737488338944 -> 6930432 <= (V 47%nat) <= 140737488355200 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> ((V 36%nat) + 296 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 36%nat)) -> ((V 36%nat) + 296 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 37 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 50%nat) + 96 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 50%nat)) -> ((V 50%nat) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 50%nat)) -> ((V 47%nat) + 128 <= 65536 \/ 65536 + 1204292 <= (V 47%nat)) ->
  L5.u64_at RSEGS M ((V 47%nat) + 32) 1 -> L5KA.zeros_at M ((((V 47%nat) + 32) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb8918 M) (st fx' R' 0xb8acc M')
        /\ (forall x, In x KS_bigB1b2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 35%nat) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 27) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) ((V 33%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) ((V 35%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G17 G18 G19 G20 G21 G22 G23 G25 G26 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI11 pvzI12 pvzI13 K20 K21 K22 K23 K24 K25 pvzI14 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K17l; move K17l before pvzI11; pose proof (proj2 pvzI11) as K17r; move K17r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K18l; move K18l before pvzI12; pose proof (proj2 pvzI12) as K18r; move K18r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K26l; move K26l before pvzI14; pose proof (proj2 pvzI14) as K26r; move K26r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbigB1b2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbigB1b2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbigB1b2.kn0).
  { unfold know_ok, PbigB1b2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K11 K33 K34) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K11 K33 K34) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K11 K33 K34) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K11 K33 K34; lia | clear - HV50l HV50r K3l K3r K11 K33 K34; lia | clear - HV50l HV50r K3l K3r K11 K33 K34; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K11 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk ZA ltac:(clear - HV35l HV35r K18l K18r) | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk ZA ltac:(clear - HV33l HV33r K17l K17r) | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K26l K26r K28 K29 K31 K34; lia | clear - HV48l HV48r K26l K26r K28 K29 K31 K34; lia | clear - HV48l HV48r K26l K26r K28 K29 K31 K34; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K11 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K11 K33 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K26l K26r K28 K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | exactA K36]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | clear - HV47l HV47r K19l K19r K23 K29 K30 K32 K33 K35; lia | exactA K37]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbigB1b2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbigB1b2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbigB1b2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbigB1b2.ps0) with 0xb8acc in Hms. change (SR.ps_regs PbigB1b2.ps0) with (map (fun i => (i, nth i PbigB1b2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbigB1b2.ps0) with PbigB1b2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbigB1b2.regs0 PbigB1b2.regs_out0 80 KS_bigB1b2 KS_bigB1b2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbigB1b2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbigB1b2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbigB1b2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbigB1b2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbigB1b2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbigB1b2.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbigB1b2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K18l K18r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r K8 K11 K30 K31 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

End PMBIGP1.
