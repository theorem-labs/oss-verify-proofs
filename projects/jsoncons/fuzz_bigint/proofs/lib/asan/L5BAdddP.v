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
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA .
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegY_adA LibSegY_adB LibSegY_adCi LibSegY_adCd LibSegY_adD LibSegY_adL LibSegY_adS LibSegY_adR LibSegY_adE.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5AADDP.
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
Module PadA := LibSegY_adA.
Definition KS_adA : list nat := Eval vm_compute in (BG.kept_list 60 PadA.regs0 PadA.regs_out0).
Lemma KS_adA_ok : BG.kept_ok 60 PadA.regs0 PadA.regs_out0 KS_adA = true. Proof. vm_compute. reflexivity. Qed.
Lemma adA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 39%nat) ->
  140735332487344 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f62c M) (st fx' R' 0x48c38 M')
        /\ (forall x, In x KS_adA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 587420
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 96
        /\ getr R' (reg 11) = Z_to_bv 64 911160
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV39l HV39r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 39%nat => (V 39%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PadA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadA.kn0).
  { unfold know_ok, PadA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  destruct (PadA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PadA.NX0 with 60%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadA.ps0) with 0x48c38 in Hms. change (SR.ps_regs PadA.ps0) with (map (fun i => (i, nth i PadA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadA.ps0) with PadA.cells0 in Hcells. unfold PadA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadA.regs0 PadA.regs_out0 60 KS_adA KS_adA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PadA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PadA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PadA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PadA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PadA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadA.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadB := LibSegY_adB.
Definition KS_adB : list nat := Eval vm_compute in (BG.kept_list 60 PadB.regs0 PadB.regs_out0).
Lemma KS_adB_ok : BG.kept_ok 60 PadB.regs0 PadB.regs_out0 KS_adB = true. Proof. vm_compute. reflexivity. Qed.
Lemma adB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 39%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 ->
  140735332487344 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488355200 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 128 -> L5.writable RSEGS M (V 40%nat) 128 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 40%nat) + 120) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 176) + 176 <= (V 40%nat) \/ (V 40%nat) + 128 <= ((V 2%nat) - 176)) -> (((V 2%nat) - 176) + 176 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 176)) -> ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 32 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 176)) ->
  L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 1 = false -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 34%nat) ->
  0 <= (V 34%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 8) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 8) -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 24) -> ~ ((((V 40%nat) / 8) + 2147450880) <= i < (((V 40%nat) / 8) + 2147450880) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f69c M) (st fx' R' 0x8fca4 M')
        /\ (forall x, In x KS_adB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 587640
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 587308
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 18) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 40%nat)
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450888) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450887) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450884) 248
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 16) 587308
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 8) 122073
        /\ L5.u64_at RSEGS M' (V 40%nat) 1102416563
        /\ L5.defined M' ((V 40%nat) + 24) 104).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV39l HV39r] [HV40l HV40r] [HV41l HV41r] [HV43l HV43r] G1 G2 G8 G9 G10 G19 G20 G24 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 K20 K21 [K22l K22r] K23 K24 K25 K26 K27 K28 [K29l K29r] K30 K31 [K32l K32r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PadB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadB.kn0).
  { unfold know_ok, PadB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K27; lia | clear - HV2l HV2r K0l K0r K17 K18 K27; lia | clear - HV2l HV2r K0l K0r K17 K18 K27; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18 K20; lia | clear - HV41l HV41r K13l K13r K15 K16 K18 K20; lia | clear - HV41l HV41r K13l K13r K15 K16 K18 K20; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K30) | clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27; lia | byte_tac ltac:(clear - HV35l HV35r K29l K29r K30) | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K30) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K30) | clear; lia | rewrite (L5K.land2_bit1_false (V 35%nat) ltac:(clear - HV35l HV35r K29l K29r K30; lia) K30); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r) | clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV33l HV33r K19 K20 K21 K22l K22r K24 K27; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_nil. }
  destruct (PadB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PadB.NX0 with 60%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 8) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 12) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PadB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K27 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadB.ps0) with 0x8fca4 in Hms. change (SR.ps_regs PadB.ps0) with (map (fun i => (i, nth i PadB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadB.ps0) with PadB.cells0 in Hcells. unfold PadB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadB.regs0 PadB.regs_out0 60 KS_adB KS_adB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PadB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PadB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadB.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PadB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PadB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadB.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PadB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadB.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PadB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadCi := LibSegY_adCi.
Definition KS_adCi : list nat := Eval vm_compute in (BG.kept_list 60 PadCi.regs0 PadCi.regs_out0).
Lemma KS_adCi_ok : BG.kept_ok 60 PadCi.regs0 PadCi.regs_out0 KS_adCi = true. Proof. vm_compute. reflexivity. Qed.
Lemma adCi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 39%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 22) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 40%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332487344 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 176)) ->
  0 <= (V 39%nat) <= 9 -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = false ->
  L5.u64_at RSEGS M ((V 33%nat) + 8) (V 34%nat) -> 1 <= (V 34%nat) <= 2 -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 38%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 16) -> ~ (((V 33%nat) + 16) <= bv_unsigned a < ((V 33%nat) + 16) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 16) -> ~ (((V 33%nat) + 16) <= i < ((V 33%nat) + 16) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f778 M) (st fx' R' 0x8f8a0 M')
        /\ (forall x, In x KS_adCi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 20)) = (((V 38%nat) + (V 39%nat)) mod 2 ^ 64)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) (((V 38%nat) + (V 39%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 16)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV43l HV43r] [HV56l HV56r] G1 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 K16 [K17l K17r] K18.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 43%nat => (V 43%nat) | 56%nat => (V 56%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PadCi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadCi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadCi.kn0).
  { unfold know_ok, PadCi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV35l HV35r K14l K14r K15) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | byte_tac ltac:(clear - HV35l HV35r K14l K14r K15) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K14l K14r K15) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K14l K14r K15) | clear; lia | rewrite (L5K.land1_bit0_false (V 35%nat) ltac:(clear - HV35l HV35r K14l K14r K15; lia) K15); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV34l HV34r K17l K17r) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K18]. }
    apply Forall_nil. }
  destruct (PadCi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PadCi.NX0 with 60%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 16) -> ~ (((V 33%nat) + 16) <= bv_unsigned a < ((V 33%nat) + 16) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PadCi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadCi.ps0) with 0x8f8a0 in Hms. change (SR.ps_regs PadCi.ps0) with (map (fun i => (i, nth i PadCi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadCi.ps0) with PadCi.cells0 in Hcells. unfold PadCi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadCi.regs0 PadCi.regs_out0 60 KS_adCi KS_adCi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadCi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadCi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadCi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadCi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadCi.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadCi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadCi.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PadCi.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PadCi.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadCi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K17l K17r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadCd := LibSegY_adCd.
Definition KS_adCd : list nat := Eval vm_compute in (BG.kept_list 60 PadCd.regs0 PadCd.regs_out0).
Lemma KS_adCd_ok : BG.kept_ok 60 PadCd.regs0 PadCd.regs_out0 KS_adCd = true. Proof. vm_compute. reflexivity. Qed.
Lemma adCd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 39%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 22) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 40%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332487344 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 176)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 176) + 176 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 176)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> (65536 + 6438912 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 65536) -> ((V 40%nat) + 128 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 40%nat)) ->
  ((V 41%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 41%nat)) -> 0 <= (V 39%nat) <= 9 -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 ->
  Z.testbit (V 35%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 34%nat) -> 1 <= (V 34%nat) <= 134217728 -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) ->
  L5.u64_at RSEGS M (V 36%nat) (V 38%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 16) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 16) -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f778 M) (st fx' R' 0x8f8a0 M')
        /\ (forall x, In x KS_adCd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 20)) = (((V 38%nat) + (V 39%nat)) mod 2 ^ 64)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' (V 36%nat) (((V 38%nat) + (V 39%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 36%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV41l HV41r] [HV43l HV43r] [HV56l HV56r] G1 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 K22 K23 K24 [K25l K25r] K26 [K27l K27r] K28 K29 [K30l K30r] K31 K32.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 43%nat => (V 43%nat) | 56%nat => (V 56%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PadCd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadCd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadCd.kn0).
  { unfold know_ok, PadCd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV35l HV35r K27l K27r K28) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | byte_tac ltac:(clear - HV35l HV35r K27l K27r K28) | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K27l K27r K28) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K27l K27r K28) | clear; lia | rewrite (L5K.land1_bit0_true (V 35%nat) ltac:(clear - HV35l HV35r K27l K27r K28; lia) K28); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV34l HV34r K30l K30r) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K30l K30r) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24; lia | exactA K32]. }
    apply Forall_nil. }
  destruct (PadCd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PadCd.NX0 with 60%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 16) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PadCd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadCd.ps0) with 0x8f8a0 in Hms. change (SR.ps_regs PadCd.ps0) with (map (fun i => (i, nth i PadCd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadCd.ps0) with PadCd.cells0 in Hcells. unfold PadCd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadCd.regs0 PadCd.regs_out0 60 KS_adCd KS_adCd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadCd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadCd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadCd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadCd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadCd.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadCd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadCd.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PadCd.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PadCd.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadCd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K30l K30r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadD := LibSegY_adD.
Definition KS_adD : list nat := Eval vm_compute in (BG.kept_list 60 PadD.regs0 PadD.regs_out0).
Lemma KS_adD_ok : BG.kept_ok 60 PadD.regs0 PadD.regs_out0 KS_adD = true. Proof. vm_compute. reflexivity. Qed.
Lemma adD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) ->
  140735332487344 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f8a8 M) (st fx' R' 0x8f8ac M')
        /\ (forall x, In x KS_adD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 25) = Z_to_bv 64 2).
Proof.
  intros [HV2l HV2r] G2 [K0l K0r] K1 K2 K3 K4 K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PadD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadD.kn0).
  { unfold know_ok, PadD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  destruct (PadD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PadD.NX0 with 60%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadD.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadD.ps0) with 0x8f8ac in Hms. change (SR.ps_regs PadD.ps0) with (map (fun i => (i, nth i PadD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadD.ps0) with PadD.cells0 in Hcells. unfold PadD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadD.regs0 PadD.regs_out0 60 KS_adD KS_adD_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PadD.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PadD.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadL := LibSegY_adL.
Definition KS_adL : list nat := Eval vm_compute in (BG.kept_list 60 PadL.regs0 PadL.regs_out0).
Lemma KS_adL_ok : BG.kept_ok 60 PadL.regs0 PadL.regs_out0 KS_adL = true. Proof. vm_compute. reflexivity. Qed.
Lemma adL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 58%nat) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 40%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 42%nat) + 1) -> getr R (reg 26) = Z_to_bv 64 (V 57%nat) ->
  140735332487344 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 176)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 176) + 176 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 176)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> (65536 + 6438912 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 65536) -> ((V 40%nat) + 128 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 40%nat)) ->
  ((V 41%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 41%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 34%nat) -> L5KA.zeros_at M ((((V 2%nat) - 128) / 8) + 2147450880) 1 ->
  1 <= (V 42%nat) <= 134217727 -> 1 <= (V 34%nat) <= 134217728 -> 1 <= ((V 37%nat) - (V 42%nat)) <= 134217728 -> L5.u64_at RSEGS M ((V 36%nat) + (8 * (V 42%nat))) (V 38%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 36%nat) + (8 * (V 42%nat))) + 0) <= bv_unsigned a < (((V 36%nat) + (8 * (V 42%nat))) + 0) + 8) -> ~ (((V 2%nat) - 168) <= bv_unsigned a < ((V 2%nat) - 168) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 36%nat) + (8 * (V 42%nat))) + 0) <= i < (((V 36%nat) + (8 * (V 42%nat))) + 0) + 8) -> ~ (((V 2%nat) - 168) <= i < ((V 2%nat) - 168) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f8ac M) (st fx' R' 0x8f8f4 M')
        /\ (forall x, In x KS_adL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 587996
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + (8 * (V 42%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 (V 42%nat)
        /\ bv_unsigned (getr R' (reg 26)) = (((V 38%nat) + 1) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + (8 * (V 42%nat))) (((V 38%nat) + 1) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 587996).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV57l HV57r] [HV58l HV58r] G1 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 [K28l K28r] [K29l K29r] [K30l K30r] K31.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PadL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadL.kn0).
  { unfold know_ok, PadL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r K30l K30r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24 K30l K30r) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24 K30l K30r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24 K30l K30r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r K30l K30r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r K30l K30r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r K30l K30r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24 K30l K30r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r K30l K30r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r K30l K30r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV37l HV37r K16l K16r K30l K30r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24 K30l K30r) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24 K30l K30r) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24 K30l K30r) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24 K30l K30r) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24 K30l K30r) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24 K30l K30r) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24 K30l K30r) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV34l HV34r K29l K29r) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K26]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K28l K28r K30l K30r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K23 K24 K30l K30r HV42l HV42r K28l K28r) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV42l HV42r K28l K28r K30l K30r) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV42l HV42r K28l K28r K30l K30r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV42l HV42r K28l K28r K30l K30r; lia | exactA K31]. }
    apply Forall_nil. }
  destruct (PadL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PadL.NX0 with 60%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 36%nat) + (8 * (V 42%nat))) + 0) <= bv_unsigned a < (((V 36%nat) + (8 * (V 42%nat))) + 0) + 8) -> ~ (((V 2%nat) - 168) <= bv_unsigned a < ((V 2%nat) - 168) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PadL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV42l HV42r K28l K28r K30l K30r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV42l HV42r K28l K28r K30l K30r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadL.ps0) with 0x8f8f4 in Hms. change (SR.ps_regs PadL.ps0) with (map (fun i => (i, nth i PadL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadL.ps0) with PadL.cells0 in Hcells. unfold PadL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadL.regs0 PadL.regs_out0 60 KS_adL KS_adL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PadL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadL.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PadL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadL.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PadL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadL.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PadL.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 K23 K24 HV42l HV42r K28l K28r K30l K30r) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadS := LibSegY_adS.
Definition KS_adS : list nat := Eval vm_compute in (BG.kept_list 60 PadS.regs0 PadS.regs_out0).
Lemma KS_adS_ok : BG.kept_ok 60 PadS.regs0 PadS.regs_out0 KS_adS = true. Proof. vm_compute. reflexivity. Qed.
Lemma adS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 25) = Z_to_bv 64 ((V 42%nat) + 1) ->
  140735332487344 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 1 <= (V 42%nat) <= 134217727 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f8f8 M) (st fx' R' 0x8f8fc M')
        /\ (forall x, In x KS_adS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 42%nat) + 2)).
Proof.
  intros [HV2l HV2r] [HV42l HV42r] G2 G25 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 42%nat => (V 42%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PadS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadS.kn0).
  { unfold know_ok, PadS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  destruct (PadS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PadS.NX0 with 60%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadS.ps0) with 0x8f8fc in Hms. change (SR.ps_regs PadS.ps0) with (map (fun i => (i, nth i PadS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadS.ps0) with PadS.cells0 in Hcells. unfold PadS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadS.regs0 PadS.regs_out0 60 KS_adS KS_adS_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PadS.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PadS.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadR := LibSegY_adR.
Definition KS_adR : list nat := Eval vm_compute in (BG.kept_list 60 PadR.regs0 PadR.regs_out0).
Lemma KS_adR_ok : BG.kept_ok 60 PadR.regs0 PadR.regs_out0 KS_adR = true. Proof. vm_compute. reflexivity. Qed.
Lemma adR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 56%nat) -> getr R (reg 11) = Z_to_bv 64 (V 57%nat) -> getr R (reg 12) = Z_to_bv 64 (V 58%nat) -> getr R (reg 13) = Z_to_bv 64 (V 59%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 40%nat) ->
  140735332487344 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f900 M) (st fx' R' 0x90d58 M')
        /\ (forall x, In x KS_adR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 588040
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV40l HV40r] [HV43l HV43r] [HV56l HV56r] [HV57l HV57r] [HV58l HV58r] [HV59l HV59r] G1 G2 G8 G9 G10 G11 G12 G13 G18 G19 G22 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 40%nat => (V 40%nat) | 43%nat => (V 43%nat) | 56%nat => (V 56%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | 59%nat => (V 59%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PadR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadR.kn0).
  { unfold know_ok, PadR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_nil. }
  destruct (PadR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PadR.NX0 with 60%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadR.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadR.ps0) with 0x90d58 in Hms. change (SR.ps_regs PadR.ps0) with (map (fun i => (i, nth i PadR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadR.ps0) with PadR.cells0 in Hcells. unfold PadR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadR.regs0 PadR.regs_out0 60 KS_adR KS_adR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PadR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadR.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadE := LibSegY_adE.
Definition KS_adE : list nat := Eval vm_compute in (BG.kept_list 60 PadE.regs0 PadE.regs_out0).
Lemma KS_adE_ok : BG.kept_ok 60 PadE.regs0 PadE.regs_out0 KS_adE = true. Proof. vm_compute. reflexivity. Qed.
Lemma adE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 40%nat) ->
  140735332487344 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 40%nat) ->
  4096 <= (V 40%nat) <= 140737488355200 -> aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 128 -> L5.writable RSEGS M (V 40%nat) 128 ->
  (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 40%nat) + 120) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 176) + 176 <= (V 40%nat) \/ (V 40%nat) + 128 <= ((V 2%nat) - 176)) ->
  (((V 2%nat) - 176) + 176 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 176)) -> ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 128 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 8) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 8) -> ~ ((((V 40%nat) / 8) + 2147450880) <= i < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f908 M) (st fx' R' 0x8f9d4 M')
        /\ (forall x, In x KS_adE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 55%nat)
        /\ L5.u8_at RSEGS M' (V 41%nat) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 40%nat) 1172321806
        /\ L5.defined M' ((V 40%nat) + 8) 120).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV40l HV40r] [HV41l HV41r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] [HV55l HV55r] G1 G2 G8 G9 G18 G19 G22 G23 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 [K20l K20r] K21 K22 K23 K24 K25 K26 [K27l K27r] K28 K29 K30 K31 K32 K33 K34 K35.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | 55%nat => Z_to_bv 64 (V 55%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | 55%nat => (V 55%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PadE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadE.kn0).
  { unfold know_ok, PadE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34) | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K27l K27r K29 K30 K32 K34; lia | clear - HV41l HV41r K27l K27r K29 K30 K32 K34; lia | clear - HV41l HV41r K27l K27r K29 K30 K32 K34; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K33 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K33 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K33 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (PadE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PadE.NX0 with 60%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 8) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PadE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV41l HV41r K27l K27r K29 K30 K32 K34 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadE.ps0) with 0x8f9d4 in Hms. change (SR.ps_regs PadE.ps0) with (map (fun i => (i, nth i PadE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadE.ps0) with PadE.cells0 in Hcells. unfold PadE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadE.regs0 PadE.regs_out0 60 KS_adE KS_adE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadE.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PadE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End L5AADDP.
