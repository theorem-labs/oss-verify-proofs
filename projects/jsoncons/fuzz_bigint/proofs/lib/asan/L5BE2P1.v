(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigLinkZA.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Bo0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA XIcptAB0 XIcptAs0KitB0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegY_ue2a1 LibSegY_ue2a2_mh LibSegY_ue2c1 LibSegY_ue2c2 LibSegY_ue2c3.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5BE2P1.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).

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
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | solve_modk k ].
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
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module Pue2a1 := LibSegY_ue2a1.
Definition KS_ue2a1 : list nat := Eval vm_compute in (BG.kept_list 56 Pue2a1.regs0 Pue2a1.regs_out0).
Lemma KS_ue2a1_ok : BG.kept_ok 56 Pue2a1.regs0 Pue2a1.regs_out0 KS_ue2a1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ue2a1_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 3) = Z_to_bv 64 67584 -> getr R (reg 4) = Z_to_bv 64 6363400 -> getr R (reg 10) = Z_to_bv 64 16 ->
  140735332552704 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> L5.defined M ((V 2%nat) - 112) 112 ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450866) 14 -> L5.img_clear M 65536 884736 -> L5.img_clear M 895824 895856 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 112) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93890 M) (st fx' R' 0x5fee0 M')
        /\ (forall x, In x KS_ue2a1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727044
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = Z_to_bv 64 144
        /\ getr R' (reg 11) = Z_to_bv 64 144
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 144
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 725240
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) 604308
        /\ L5.defined M' ((V 2%nat) - 32) 8).
Proof.
  intros [HV2l HV2r] G2 G3 G4 G10 [K0l K0r] K1 K2 K3 K4 K5 K6.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pue2a1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pue2a1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pue2a1.kn0).
  { unfold know_ok, Pue2a1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K6]. }
    apply Forall_nil. }
  destruct (Pue2a1.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pue2a1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pue2a1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pue2a1.ps0) with 0x5fee0 in Hms. change (SR.ps_regs Pue2a1.ps0) with (map (fun i => (i, nth i Pue2a1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pue2a1.ps0) with Pue2a1.cells0 in Hcells. unfold Pue2a1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pue2a1.regs0 Pue2a1.regs_out0 56 KS_ue2a1 KS_ue2a1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pue2a1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pue2a1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2a1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pue2a1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2a1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pue2a1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2a1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pue2a1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pue2a2_mh := LibSegY_ue2a2_mh.
Definition KS_ue2a2_mh : list nat := Eval vm_compute in (BG.kept_list 56 Pue2a2_mh.regs0 Pue2a2_mh.regs_out0).
Lemma KS_ue2a2_mh_ok : BG.kept_ok 56 Pue2a2_mh.regs0 Pue2a2_mh.regs_out0 KS_ue2a2_mh = true. Proof. vm_compute. reflexivity. Qed.
Lemma ue2a2_mh_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 3) = Z_to_bv 64 67584 -> getr R (reg 4) = Z_to_bv 64 6363400 -> getr R (reg 10) = Z_to_bv 64 ((V 10%nat) - 128) ->
  140735332552704 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 2736) 2704 -> L5.defined M ((V 2%nat) - 2736) 2704 ->
  17594333495424 <= (V 10%nat) <= 140737479966720 -> aligned (V 10%nat) 16 -> L5.writable RSEGS M ((V 10%nat) - 128) 144 -> L5.defined M ((V 10%nat) - 128) 144 ->
  (2147446784 + 17592186048512 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 144 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450864) 18 -> (((V 2%nat) - 2736) + 6800 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 144 <= ((V 2%nat) - 2736)) -> (((V 10%nat) - 128) + 144 <= 65536 \/ 65536 + 6438912 <= ((V 10%nat) - 128)) ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450538) 338 -> L5.img_clear M 65536 884736 -> L5.img_clear M 895824 895856 -> L5.u64_at RSEGS M 877768 911160 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u64_at RSEGS M 877776 914472 -> L5.u64_at RSEGS M 914472 0 -> L5.u64_at RSEGS M 877784 914480 ->
  L5.u64_at RSEGS M 914480 0 -> L5.u64_at RSEGS M 877792 914464 -> L5.u64_at RSEGS M 914464 140737488355327 -> L5.u64_at RSEGS M 880688 914457 ->
  L5.u8_at RSEGS M 914457 1 -> L5.u64_at RSEGS M 885800 837440 -> L5.u64_at RSEGS M 885792 836412 -> L5.u64_at RSEGS M ((V 2%nat) - 40) 725240 ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) 144 -> L5.u64_at RSEGS M ((V 2%nat) - 8) 604308 -> L5.u64_at RSEGS M ((V 2%nat) - 16) ((V 2%nat) + 384) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 2%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 2736) <= bv_unsigned a < ((V 2%nat) - 2736) + 2704) -> ~ (((V 10%nat) - 128) <= bv_unsigned a < ((V 10%nat) - 128) + 144) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 2736) <= i < ((V 2%nat) - 2736) + 2704) -> ~ (((V 10%nat) - 128) <= i < ((V 10%nat) - 128) + 144) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1804 M) (st fx' R' 0x938b0 M')
        /\ (forall x, In x KS_ue2a2_mh -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 604308
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) + 384)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 142528
        /\ getr R' (reg 19) = Z_to_bv 64 (V 10%nat)
        /\ L5KA.zeros_at M' ((V 10%nat) - 128) 144
        /\ L5.defined M' ((V 10%nat) + 16) 0).
Proof.
  intros [HV2l HV2r] [HV10l HV10r] G2 G3 G4 G10 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 10%nat => Z_to_bv 64 (V 10%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 10%nat => (V 10%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 11%nat. }
  assert (HR: regs_ok E Pue2a2_mh.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pue2a2_mh.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pue2a2_mh.kn0).
  { unfold know_ok, Pue2a2_mh.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K31]. }
    apply Forall_nil. }
  destruct (Pue2a2_mh.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pue2a2_mh.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 2736) <= bv_unsigned a < ((V 2%nat) - 2736) + 2704) -> ~ (((V 10%nat) - 128) <= bv_unsigned a < ((V 10%nat) - 128) + 144) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pue2a2_mh.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pue2a2_mh.ps0) with 0x938b0 in Hms. change (SR.ps_regs Pue2a2_mh.ps0) with (map (fun i => (i, nth i Pue2a2_mh.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pue2a2_mh.ps0) with Pue2a2_mh.cells0 in Hcells. unfold Pue2a2_mh.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pue2a2_mh.regs0 Pue2a2_mh.regs_out0 56 KS_ue2a2_mh KS_ue2a2_mh_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pue2a2_mh.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pue2a2_mh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2a2_mh.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pue2a2_mh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2a2_mh.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pue2a2_mh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2a2_mh.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pue2a2_mh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2a2_mh.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pue2a2_mh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2a2_mh.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pue2a2_mh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2a2_mh.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pue2a2_mh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pue2c1 := LibSegY_ue2c1.
Definition KS_ue2c1 : list nat := Eval vm_compute in (BG.kept_list 56 Pue2c1.regs0 Pue2c1.regs_out0).
Lemma KS_ue2c1_ok : BG.kept_ok 56 Pue2c1.regs0 Pue2c1.regs_out0 KS_ue2c1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ue2c1_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 3) = Z_to_bv 64 67584 -> getr R (reg 4) = Z_to_bv 64 6363400 -> getr R (reg 11) = Z_to_bv 64 142528 ->
  140735332552704 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> L5.defined M ((V 2%nat) - 112) 112 ->
  4224 <= (bv_unsigned (getr R (reg 10))) <= 140737488355328 -> aligned (bv_unsigned (getr R (reg 10))) 16 -> L5.writable RSEGS M ((bv_unsigned (getr R (reg 10))) - 128) 144 -> L5.defined M ((bv_unsigned (getr R (reg 10))) - 128) 144 ->
  (2147446784 + 17592186048512 <= ((bv_unsigned (getr R (reg 10))) - 128) \/ ((bv_unsigned (getr R (reg 10))) - 128) + 144 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450864) 18 -> (((V 2%nat) - 112) + 4208 <= ((bv_unsigned (getr R (reg 10))) - 128) \/ ((bv_unsigned (getr R (reg 10))) - 128) + 144 <= ((V 2%nat) - 112)) -> (((bv_unsigned (getr R (reg 10))) - 128) + 144 <= 65536 \/ 65536 + 6438912 <= ((bv_unsigned (getr R (reg 10))) - 128)) ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450866) 14 -> L5.img_clear M 65536 884736 -> L5.img_clear M 895824 895856 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 112) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x938b0 M) (st fx' R' 0x4de30 M')
        /\ (forall x, In x KS_ue2c1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 731600
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 142528
        /\ getr R' (reg 10) = Z_to_bv 64 142528
        /\ L5.u64_at RSEGS M' (bv_unsigned (getr R (reg 10))) 876464
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) 604340
        /\ L5.defined M' ((bv_unsigned (getr R (reg 10))) - 128) 128
        /\ L5.defined M' ((bv_unsigned (getr R (reg 10))) + 8) 8).
Proof.
  intros [HV2l HV2r] G2 G3 G4 G11 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 K8 K9 K10 K11 K12 K13 K14.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pue2c1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pue2c1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pue2c1.kn0).
  { unfold know_ok, Pue2c1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K4l K4r K8 K10 K11) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K4l K4r K8 K10 K11) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - K4l K4r K8 K10 K11; lia | clear - K4l K4r K8 K10 K11; lia | clear - K4l K4r K8 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - K4l K4r K8 K10 K11; lia | clear - K4l K4r K8 K10 K11; lia | clear - K4l K4r K8 K10 K11; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - K4l K4r K8 K10 K11; lia | clear - K4l K4r K8 K10 K11; lia | clear - K4l K4r K8 K10 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K14]. }
    apply Forall_nil. }
  destruct (Pue2c1.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pue2c1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pue2c1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K4l K4r K8 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear - K4l K4r K8 K10 K11 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pue2c1.ps0) with 0x4de30 in Hms. change (SR.ps_regs Pue2c1.ps0) with (map (fun i => (i, nth i Pue2c1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pue2c1.ps0) with Pue2c1.cells0 in Hcells. unfold Pue2c1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pue2c1.regs0 Pue2c1.regs_out0 56 KS_ue2c1 KS_ue2c1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pue2c1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pue2c1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2c1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pue2c1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2c1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pue2c1.regs_out0]. rewrite (BG.edenot_kept 56 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg Pue2c1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pue2c1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2c1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pue2c1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K8 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K8 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K4l K4r K8 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pue2c2 := LibSegY_ue2c2.
Definition KS_ue2c2 : list nat := Eval vm_compute in (BG.kept_list 56 Pue2c2.regs0 Pue2c2.regs_out0).
Lemma KS_ue2c2_ok : BG.kept_ok 56 Pue2c2.regs0 Pue2c2.regs_out0 KS_ue2c2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ue2c2_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 3) = Z_to_bv 64 67584 -> getr R (reg 4) = Z_to_bv 64 6363400 -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 12 ->
  140735332552704 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 80 -> L5.defined M ((V 2%nat) - 128) 80 ->
  4224 <= (V 10%nat) <= 140737488355328 -> aligned (V 10%nat) 16 -> L5.writable RSEGS M ((V 10%nat) - 128) 144 -> L5.defined M ((V 10%nat) - 128) 144 ->
  (2147446784 + 17592186048512 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 144 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450864) 18 -> (((V 2%nat) - 128) + 4176 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 144 <= ((V 2%nat) - 128)) -> (((V 10%nat) - 128) + 144 <= 65536 \/ 65536 + 6438912 <= ((V 10%nat) - 128)) ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450864) 10 -> L5.img_clear M 65536 884736 -> L5.img_clear M 895824 895856 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb29d0 M) (st fx' R' 0x5fed8 M')
        /\ (forall x, In x KS_ue2c2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 859152
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 37
        /\ getr R' (reg 10) = Z_to_bv 64 37
        /\ getr R' (reg 18) = Z_to_bv 64 12
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 731612).
Proof.
  intros [HV2l HV2r] [HV10l HV10r] G2 G3 G4 G8 G10 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 K8 K9 K10 K11 K12 K13 K14.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 10%nat => Z_to_bv 64 (V 10%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 10%nat => (V 10%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 11%nat. }
  assert (HR: regs_ok E Pue2c2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pue2c2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pue2c2.kn0).
  { unfold know_ok, Pue2c2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K14]. }
    apply Forall_nil. }
  destruct (Pue2c2.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pue2c2.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pue2c2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pue2c2.ps0) with 0x5fed8 in Hms. change (SR.ps_regs Pue2c2.ps0) with (map (fun i => (i, nth i Pue2c2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pue2c2.ps0) with Pue2c2.cells0 in Hcells. unfold Pue2c2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pue2c2.regs0 Pue2c2.regs_out0 56 KS_ue2c2 KS_ue2c2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pue2c2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pue2c2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2c2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pue2c2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2c2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pue2c2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2c2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pue2c2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2c2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pue2c2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pue2c3 := LibSegY_ue2c3.
Definition KS_ue2c3 : list nat := Eval vm_compute in (BG.kept_list 56 Pue2c3.regs0 Pue2c3.regs_out0).
Lemma KS_ue2c3_ok : BG.kept_ok 56 Pue2c3.regs0 Pue2c3.regs_out0 KS_ue2c3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ue2c3_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 3) = Z_to_bv 64 67584 -> getr R (reg 4) = Z_to_bv 64 6363400 -> getr R (reg 9) = Z_to_bv 64 142528 -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 12 ->
  140735332552704 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 64 -> L5.defined M ((V 2%nat) - 128) 64 ->
  4224 <= (V 10%nat) <= 140737488355328 -> aligned (V 10%nat) 16 -> L5.writable RSEGS M ((V 10%nat) - 128) 144 -> L5.defined M ((V 10%nat) - 128) 144 ->
  (2147446784 + 17592186048512 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 144 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450864) 18 -> 4096 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 16 ->
  L5.writable RSEGS M (V 37%nat) 37 -> L5.defined M (V 37%nat) 37 -> (((V 2%nat) - 128) + 4160 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 144 <= ((V 2%nat) - 128)) -> (((V 10%nat) - 128) + 144 <= (V 37%nat) \/ (V 37%nat) + 37 <= ((V 10%nat) - 128)) ->
  (((V 2%nat) - 128) + 4160 <= (V 37%nat) \/ (V 37%nat) + 37 <= ((V 2%nat) - 128)) -> (((V 10%nat) - 128) + 144 <= 65536 \/ 65536 + 6438912 <= ((V 10%nat) - 128)) -> ((V 37%nat) + 37 <= 65536 \/ 65536 + 6438912 <= (V 37%nat)) -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450864) 8 ->
  L5.img_clear M 65536 884736 -> L5.img_clear M 895824 895856 -> L5.u64_at RSEGS M ((V 2%nat) - 56) 731612 -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 10%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 64) -> ~ (((V 37%nat) + 0) <= bv_unsigned a < ((V 37%nat) + 0) + 20) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 64) -> ~ (((V 37%nat) + 0) <= i < ((V 37%nat) + 0) + 20) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd1c10 M) (st fx' R' 0x5e350 M')
        /\ (forall x, In x KS_ue2c3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 731644
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 142528
        /\ getr R' (reg 12) = Z_to_bv 64 13
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 37%nat) + 24)
        /\ L5.u32_at RSEGS M' ((V 37%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 37%nat) + 8) 12
        /\ L5.u64_at RSEGS M' (V 37%nat) 12
        /\ L5.defined M' ((V 37%nat) + 20) 17).
Proof.
  intros [HV2l HV2r] [HV10l HV10r] [HV37l HV37r] G2 G3 G4 G9 G10 G18 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 K8 K9 [K10l K10r] K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 10%nat => Z_to_bv 64 (V 10%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 10%nat => (V 10%nat) | 37%nat => (V 37%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E Pue2c3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pue2c3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pue2c3.kn0).
  { unfold know_ok, Pue2c3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | exactA K23]. }
    apply Forall_nil. }
  destruct (Pue2c3.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pue2c3.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 64) -> ~ (((V 37%nat) + 0) <= bv_unsigned a < ((V 37%nat) + 0) + 20) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pue2c3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K10l K10r K15 K16 K18 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pue2c3.ps0) with 0x5e350 in Hms. change (SR.ps_regs Pue2c3.ps0) with (map (fun i => (i, nth i Pue2c3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pue2c3.ps0) with Pue2c3.cells0 in Hcells. unfold Pue2c3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pue2c3.regs0 Pue2c3.regs_out0 56 KS_ue2c3 KS_ue2c3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pue2c3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pue2c3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2c3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pue2c3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2c3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pue2c3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2c3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pue2c3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2c3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pue2c3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2c3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pue2c3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue2c3.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pue2c3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End L5BE2P1.
