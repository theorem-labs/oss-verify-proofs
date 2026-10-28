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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_bhnA_u LibSegBs_bhnB_u LibSegBs_bhnC_u LibSegBs_bhnD_u LibSegBs_bhnE_u LibSegBs_bhnEr_u LibSegBs_bhnF_u LibSegBs_bhnG_u LibSegBs_bhnGi_u LibSegBs_bhnHs_u LibSegBs_bhnHl_u LibSegBs_bhnQs_u LibSegBs_bhnQl_u LibSegBs_bhnVn_u LibSegBs_bhnVl_u LibSegBs_bhnI_u LibSegBs_bhnJs_u LibSegBs_bhnJl_u LibSegBs_bhnK_u LibSegBs_bhnL_u LibSegBs_bhnMs_u LibSegBs_bhnMl_u LibSegBs_bhnN_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSHP.
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
Module PbhnA := LibSegBs_bhnA_u.
Definition KS_bhnA : list nat := Eval vm_compute in (BG.kept_list 48 PbhnA.regs0 PbhnA.regs_out0).
Lemma KS_bhnA_ok : BG.kept_ok 48 PbhnA.regs0 PbhnA.regs_out0 KS_bhnA = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3471c M) (st fx' R' 0x3490c M')
        /\ (forall x, In x KS_bhnA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 214840
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 784)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 40)
        /\ getr R' (reg 11) = getr R (reg 10)
        /\ getr R' (reg 12) = getr R (reg 11)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 G2 pvzI2 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PbhnA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnA.kn0).
  { unfold know_ok, PbhnA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnA.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbhnA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnA.ps0) with 0x3490c in Hms. change (SR.ps_regs PbhnA.ps0) with (map (fun i => (i, nth i PbhnA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnA.ps0) with PbhnA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnA.regs0 PbhnA.regs_out0 48 KS_bhnA KS_bhnA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbhnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhnA.regs_out0]. rewrite (BG.edenot_kept 48 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PbhnA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhnA.regs_out0]. rewrite (BG.edenot_kept 48 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnB := LibSegBs_bhnB_u.
Definition KS_bhnB : list nat := Eval vm_compute in (BG.kept_list 48 PbhnB.regs0 PbhnB.regs_out0).
Lemma KS_bhnB_ok : BG.kept_ok 48 PbhnB.regs0 PbhnB.regs_out0 KS_bhnB = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x34738 M) (st fx' R' 0x349d4 M')
        /\ (forall x, In x KS_bhnB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 214856
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 312)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 40)
        /\ getr R' (reg 12) = Z_to_bv 64 8).
Proof.
  intros pvzI1 G2 pvzI2 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PbhnB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnB.kn0).
  { unfold know_ok, PbhnB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnB.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbhnB.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnB.ps0) with 0x349d4 in Hms. change (SR.ps_regs PbhnB.ps0) with (map (fun i => (i, nth i PbhnB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnB.ps0) with PbhnB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnB.regs0 PbhnB.regs_out0 48 KS_bhnB KS_bhnB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbhnB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnC := LibSegBs_bhnC_u.
Definition KS_bhnC : list nat := Eval vm_compute in (BG.kept_list 48 PbhnC.regs0 PbhnC.regs_out0).
Lemma KS_bhnC_ok : BG.kept_ok 48 PbhnC.regs0 PbhnC.regs_out0 KS_bhnC = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 768) <= bv_unsigned a < ((V 2%nat) - 768) + 24) -> ~ (((V 2%nat) - 320) <= bv_unsigned a < ((V 2%nat) - 320) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 768) <= i < ((V 2%nat) - 768) + 24) -> ~ (((V 2%nat) - 320) <= i < ((V 2%nat) - 320) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x34748 M) (st fx' R' 0x36410 M')
        /\ (forall x, In x KS_bhnC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 214924
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 744)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 312)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 768)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 769)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 752) 1024
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 748) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 760) 726664
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 768) 726624
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) 726280).
Proof.
  intros pvzI1 G2 pvzI2 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PbhnC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnC.kn0).
  { unfold know_ok, PbhnC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnC.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 768) <= bv_unsigned a < (vz_2 - 768) + 24) -> ~ ((vz_2 - 320) <= bv_unsigned a < (vz_2 - 320) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbhnC.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnC.ps0) with 0x36410 in Hms. change (SR.ps_regs PbhnC.ps0) with (map (fun i => (i, nth i PbhnC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnC.ps0) with PbhnC.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnC.regs0 PbhnC.regs_out0 48 KS_bhnC KS_bhnC_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnC.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnC.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnC.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhnC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnC.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhnC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnC.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbhnC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnD := LibSegBs_bhnD_u.
Definition KS_bhnD : list nat := Eval vm_compute in (BG.kept_list 48 PbhnD.regs0 PbhnD.regs_out0).
Lemma KS_bhnD_ok : BG.kept_ok 48 PbhnD.regs0 PbhnD.regs_out0 KS_bhnD = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 328) <= bv_unsigned a < ((V 2%nat) - 328) + 8) -> ~ (((V 2%nat) - 768) <= bv_unsigned a < ((V 2%nat) - 768) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 328) <= i < ((V 2%nat) - 328) + 8) -> ~ (((V 2%nat) - 768) <= i < ((V 2%nat) - 768) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3478c M) (st fx' R' 0x5c280 M')
        /\ (forall x, In x KS_bhnD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 214940
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 320)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 768) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) ((V 2%nat) - 320)).
Proof.
  intros pvzI1 G2 pvzI2 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PbhnD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnD.kn0).
  { unfold know_ok, PbhnD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnD.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 328) <= bv_unsigned a < (vz_2 - 328) + 8) -> ~ ((vz_2 - 768) <= bv_unsigned a < (vz_2 - 768) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbhnD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnD.ps0) with 0x5c280 in Hms. change (SR.ps_regs PbhnD.ps0) with (map (fun i => (i, nth i PbhnD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnD.ps0) with PbhnD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnD.regs0 PbhnD.regs_out0 48 KS_bhnD KS_bhnD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnE := LibSegBs_bhnE_u.
Definition KS_bhnE : list nat := Eval vm_compute in (BG.kept_list 48 PbhnE.regs0 PbhnE.regs_out0).
Lemma KS_bhnE_ok : BG.kept_ok 48 PbhnE.regs0 PbhnE.regs_out0 KS_bhnE = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 760) <= bv_unsigned a < ((V 2%nat) - 760) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 760) <= i < ((V 2%nat) - 760) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3479c M) (st fx' R' 0x347a0 M')
        /\ (forall x, In x KS_bhnE -> getr R' (reg x) = getr R (reg x))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 760) (bv_unsigned (getr R (reg 10)))).
Proof.
  intros pvzI1 G2 pvzI2 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PbhnE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnE.kn0).
  { unfold know_ok, PbhnE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnE.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 760) <= bv_unsigned a < (vz_2 - 760) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbhnE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnE.ps0) with 0x347a0 in Hms. change (SR.ps_regs PbhnE.ps0) with (map (fun i => (i, nth i PbhnE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnE.ps0) with PbhnE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnE.regs0 PbhnE.regs_out0 48 KS_bhnE KS_bhnE_ok HR Hag Hregs j Hj). }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.

Module PbhnEr := LibSegBs_bhnEr_u.
Definition KS_bhnEr : list nat := Eval vm_compute in (BG.kept_list 48 PbhnEr.regs0 PbhnEr.regs_out0).
Lemma KS_bhnEr_ok : BG.kept_ok 48 PbhnEr.regs0 PbhnEr.regs_out0 KS_bhnEr = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnEr_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.writable RSEGS M ((V 2%nat) - 816) 32 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 816) <= bv_unsigned a < ((V 2%nat) - 816) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 816) <= i < ((V 2%nat) - 816) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x347a0 M) (st fx' R' 0x36a90 M')
        /\ (forall x, In x KS_bhnEr -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 215812
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 816)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 768)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 744)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 744)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 768)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 808) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 800) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 792) 214956).
Proof.
  intros pvzI1 G2 pvzI2 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PbhnEr.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnEr.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnEr.kn0).
  { unfold know_ok, PbhnEr.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnEr.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnEr.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 816) <= bv_unsigned a < (vz_2 - 816) + 32) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbhnEr.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnEr.ps0) with 0x36a90 in Hms. change (SR.ps_regs PbhnEr.ps0) with (map (fun i => (i, nth i PbhnEr.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnEr.ps0) with PbhnEr.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnEr.regs0 PbhnEr.regs_out0 48 KS_bhnEr KS_bhnEr_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnEr.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnEr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnEr.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbhnEr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnEr.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbhnEr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnEr.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbhnEr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnEr.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnEr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnEr.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhnEr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnF := LibSegBs_bhnF_u.
Definition KS_bhnF : list nat := Eval vm_compute in (BG.kept_list 48 PbhnF.regs0 PbhnF.regs_out0).
Lemma KS_bhnF_ok : BG.kept_ok 48 PbhnF.regs0 PbhnF.regs_out0 KS_bhnF = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 816) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 768) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 744) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 808) (V 9%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 800) (V 8%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 792) 214956 -> L5.u64_at RSEGS M ((V 2%nat) - 328) ((V 2%nat) - 320) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x34b04 M) (st fx' R' 0x36bc0 M')
        /\ (forall x, In x KS_bhnF -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 214956
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 784)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 9%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 744)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 320)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 768)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 pvzI4 K1 K2 K3 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV8l; move HV8l before pvzI2; pose proof (proj2 pvzI2) as HV8r; move HV8r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV9l; move HV9l before pvzI3; pose proof (proj2 pvzI3) as HV9r; move HV9r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_8 := V 8%nat) in *. set (vz_9 := V 9%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 8%nat => Z_to_bv 64 vz_8 | 9%nat => Z_to_bv 64 vz_9 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 8%nat => vz_8 | 9%nat => vz_9 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 10%nat. }
  assert (HR: regs_ok E PbhnF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnF.kn0).
  { unfold know_ok, PbhnF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV9l HV9r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV8l HV8r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnF.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbhnF.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnF.ps0) with 0x36bc0 in Hms. change (SR.ps_regs PbhnF.ps0) with (map (fun i => (i, nth i PbhnF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnF.ps0) with PbhnF.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnF.regs0 PbhnF.regs_out0 48 KS_bhnF KS_bhnF_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnF.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnF.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbhnF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnF.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbhnF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnF.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbhnF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnF.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnF.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhnF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbhnF.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhnF.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnG := LibSegBs_bhnG_u.
Definition KS_bhnG_0 : list nat := Eval vm_compute in (BG.kept_list 48 PbhnG.regs0 PbhnG.regs_out0).
Lemma KS_bhnG_0_ok : BG.kept_ok 48 PbhnG.regs0 PbhnG.regs_out0 KS_bhnG_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bhnG_1 : list nat := Eval vm_compute in (BG.kept_list 48 PbhnG.regs0 PbhnG.regs_out1).
Lemma KS_bhnG_1_ok : BG.kept_ok 48 PbhnG.regs0 PbhnG.regs_out1 KS_bhnG_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.u64_at RSEGS M ((V 2%nat) - 352) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 344) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 336) (V 34%nat) -> 4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 744) <= bv_unsigned a < ((V 2%nat) - 744) + 8) -> ~ (((V 2%nat) - 344) <= bv_unsigned a < ((V 2%nat) - 344) + 8) -> ~ (((V 2%nat) - 768) <= bv_unsigned a < ((V 2%nat) - 768) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 744) <= i < ((V 2%nat) - 744) + 8) -> ~ (((V 2%nat) - 344) <= i < ((V 2%nat) - 344) + 8) -> ~ (((V 2%nat) - 768) <= i < ((V 2%nat) - 768) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x347ac M) (st fx' R' 0x35e54 M')
        /\ (forall x, In x KS_bhnG_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 214984
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 352)
        /\ getr R' (reg 13) = Z_to_bv 64 40
        /\ 1 <= (((V 33%nat) - (V 35%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 768) ((V 2%nat) - 352)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 744) 726752
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 344) (V 35%nat))
      \/ (msteps RSEGS (st fx R 0x347ac M) (st fx' R' 0x56720 M')
        /\ (forall x, In x KS_bhnG_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 214984
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 33%nat)) + (V 34%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 352)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 344) (V 33%nat)
        /\ (((V 33%nat) - (V 35%nat)) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 768) ((V 2%nat) - 352)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 744) 726752)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 pvzI5 K1 K2 K3 K4 K5 pvzI6 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PbhnG.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnG.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnG.kn0).
  { unfold know_ok, PbhnG.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnG.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnG.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 744) <= bv_unsigned a < (vz_2 - 744) + 8) -> ~ ((vz_2 - 344) <= bv_unsigned a < (vz_2 - 344) + 8) -> ~ ((vz_2 - 768) <= bv_unsigned a < (vz_2 - 768) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbhnG.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PbhnG.ps0) with 0x35e54 in Hms. change (SR.ps_regs PbhnG.ps0) with (map (fun i => (i, nth i PbhnG.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbhnG.ps0) with PbhnG.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnG.regs0 PbhnG.regs_out0 48 KS_bhnG_0 KS_bhnG_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbhnG.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnG.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnG.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhnG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnG.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhnG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnG.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbhnG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. 
  - right.
    change (SR.ps_pc PbhnG.ps1) with 0x56720 in Hms. change (SR.ps_regs PbhnG.ps1) with (map (fun i => (i, nth i PbhnG.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbhnG.ps1) with PbhnG.cells1 in Hcells. unfold PbhnG.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnG.regs0 PbhnG.regs_out1 48 KS_bhnG_1 KS_bhnG_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbhnG.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnG.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnG.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhnG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnG.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhnG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | clear; lia]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.

Module PbhnGi := LibSegBs_bhnGi_u.
Definition KS_bhnGi_0 : list nat := Eval vm_compute in (BG.kept_list 48 PbhnGi.regs0 PbhnGi.regs_out0).
Lemma KS_bhnGi_0_ok : BG.kept_ok 48 PbhnGi.regs0 PbhnGi.regs_out0 KS_bhnGi_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bhnGi_1 : list nat := Eval vm_compute in (BG.kept_list 48 PbhnGi.regs0 PbhnGi.regs_out1).
Lemma KS_bhnGi_1_ok : BG.kept_ok 48 PbhnGi.regs0 PbhnGi.regs_out1 KS_bhnGi_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnGi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 214984 -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 36%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 13) = Z_to_bv 64 40 ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.u64_at RSEGS M ((V 2%nat) - 352) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 344) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 336) (V 34%nat) -> 4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 2 ->
  4136 <= (V 36%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 344) <= bv_unsigned a < ((V 2%nat) - 344) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 344) <= i < ((V 2%nat) - 344) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x35e54 M) (st fx' R' 0x35e54 M')
        /\ (forall x, In x KS_bhnGi_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) - 40)
        /\ 1 <= (((((V 36%nat) + 18446744073709551576) mod 2 ^ 64) - (V 33%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 344) (V 35%nat))
      \/ (msteps RSEGS (st fx R 0x35e54 M) (st fx' R' 0x56720 M')
        /\ (forall x, In x KS_bhnGi_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 33%nat)) + (V 34%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 344) (V 33%nat)
        /\ (((((V 36%nat) + 18446744073709551576) mod 2 ^ 64) - (V 33%nat)) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G1 G2 G10 G11 G12 G13 pvzI6 K1 K2 K3 K4 K5 pvzI7 K7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PbhnGi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnGi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnGi.kn0).
  { unfold know_ok, PbhnGi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnGi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnGi.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 344) <= bv_unsigned a < (vz_2 - 344) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbhnGi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PbhnGi.ps0) with 0x35e54 in Hms. change (SR.ps_regs PbhnGi.ps0) with (map (fun i => (i, nth i PbhnGi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbhnGi.ps0) with PbhnGi.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnGi.regs0 PbhnGi.regs_out0 48 KS_bhnGi_0 KS_bhnGi_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbhnGi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhnGi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. 
  - right.
    change (SR.ps_pc PbhnGi.ps1) with 0x56720 in Hms. change (SR.ps_regs PbhnGi.ps1) with (map (fun i => (i, nth i PbhnGi.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbhnGi.ps1) with PbhnGi.cells1 in Hcells. unfold PbhnGi.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnGi.regs0 PbhnGi.regs_out1 48 KS_bhnGi_1 KS_bhnGi_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbhnGi.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhnGi.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | clear; lia]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnHs := LibSegBs_bhnHs_u.
Definition KS_bhnHs : list nat := Eval vm_compute in (BG.kept_list 48 PbhnHs.regs0 PbhnHs.regs_out0).
Lemma KS_bhnHs_ok : BG.kept_ok 48 PbhnHs.regs0 PbhnHs.regs_out0 KS_bhnHs = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnHs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.u8_at RSEGS M ((V 2%nat) - 376) (V 35%nat) ->
  0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x347c8 M) (st fx' R' 0x347e4 M')
        /\ (forall x, In x KS_bhnHs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 G2 pvzI3 K1 K2 K3 pvzI4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV35l; move HV35l before pvzI2; pose proof (proj2 pvzI2) as HV35r; move HV35r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K4l; move K4l before pvzI4; pose proof (proj2 pvzI4) as K4r; move K4r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PbhnHs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnHs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnHs.kn0).
  { unfold know_ok, PbhnHs.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV35l HV35r K4l K4r K5) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false vz_35 ltac:(clear - HV35l HV35r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnHs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnHs.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbhnHs.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnHs.ps0) with 0x347e4 in Hms. change (SR.ps_regs PbhnHs.ps0) with (map (fun i => (i, nth i PbhnHs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnHs.ps0) with PbhnHs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnHs.regs0 PbhnHs.regs_out0 48 KS_bhnHs KS_bhnHs_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PbhnHs.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnHs.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnHl := LibSegBs_bhnHl_u.
Definition KS_bhnHl : list nat := Eval vm_compute in (BG.kept_list 48 PbhnHl.regs0 PbhnHl.regs_out0).
Lemma KS_bhnHl_ok : BG.kept_ok 48 PbhnHl.regs0 PbhnHl.regs_out0 KS_bhnHl = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnHl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.u8_at RSEGS M ((V 2%nat) - 376) (V 35%nat) ->
  0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = true -> L5.defined M ((V 2%nat) - 375) 7 -> L5.u64_at RSEGS M ((V 2%nat) - 360) (V 37%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x347c8 M) (st fx' R' 0x56720 M')
        /\ (forall x, In x KS_bhnHl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 215012
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 pvzI4 K1 K2 K3 pvzI5 K5 K6 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV35l; move HV35l before pvzI2; pose proof (proj2 pvzI2) as HV35r; move HV35r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K4l; move K4l before pvzI5; pose proof (proj2 pvzI5) as K4r; move K4r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbhnHl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnHl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnHl.kn0).
  { unfold know_ok, PbhnHl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV35l HV35r K4l K4r K5) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_true vz_35 ltac:(clear - HV35l HV35r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnHl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnHl.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbhnHl.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnHl.ps0) with 0x56720 in Hms. change (SR.ps_regs PbhnHl.ps0) with (map (fun i => (i, nth i PbhnHl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnHl.ps0) with PbhnHl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnHl.regs0 PbhnHl.regs_out0 48 KS_bhnHl KS_bhnHl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnHl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnHl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbhnHl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnHl.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnQs := LibSegBs_bhnQs_u.
Definition KS_bhnQs : list nat := Eval vm_compute in (BG.kept_list 48 PbhnQs.regs0 PbhnQs.regs_out0).
Lemma KS_bhnQs_ok : BG.kept_ok 48 PbhnQs.regs0 PbhnQs.regs_out0 KS_bhnQs = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnQs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.u8_at RSEGS M ((V 2%nat) - 400) (V 35%nat) ->
  0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x347e4 M) (st fx' R' 0x34800 M')
        /\ (forall x, In x KS_bhnQs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 G2 pvzI3 K1 K2 K3 pvzI4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV35l; move HV35l before pvzI2; pose proof (proj2 pvzI2) as HV35r; move HV35r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K4l; move K4l before pvzI4; pose proof (proj2 pvzI4) as K4r; move K4r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PbhnQs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnQs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnQs.kn0).
  { unfold know_ok, PbhnQs.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV35l HV35r K4l K4r K5) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false vz_35 ltac:(clear - HV35l HV35r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnQs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnQs.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbhnQs.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnQs.ps0) with 0x34800 in Hms. change (SR.ps_regs PbhnQs.ps0) with (map (fun i => (i, nth i PbhnQs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnQs.ps0) with PbhnQs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnQs.regs0 PbhnQs.regs_out0 48 KS_bhnQs KS_bhnQs_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PbhnQs.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnQs.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnQl := LibSegBs_bhnQl_u.
Definition KS_bhnQl : list nat := Eval vm_compute in (BG.kept_list 48 PbhnQl.regs0 PbhnQl.regs_out0).
Lemma KS_bhnQl_ok : BG.kept_ok 48 PbhnQl.regs0 PbhnQl.regs_out0 KS_bhnQl = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnQl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.u8_at RSEGS M ((V 2%nat) - 400) (V 35%nat) ->
  0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = true -> L5.defined M ((V 2%nat) - 399) 7 -> L5.u64_at RSEGS M ((V 2%nat) - 384) (V 37%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x347e4 M) (st fx' R' 0x56720 M')
        /\ (forall x, In x KS_bhnQl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 215040
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 pvzI4 K1 K2 K3 pvzI5 K5 K6 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV35l; move HV35l before pvzI2; pose proof (proj2 pvzI2) as HV35r; move HV35r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K4l; move K4l before pvzI5; pose proof (proj2 pvzI5) as K4r; move K4r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbhnQl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnQl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnQl.kn0).
  { unfold know_ok, PbhnQl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV35l HV35r K4l K4r K5) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_true vz_35 ltac:(clear - HV35l HV35r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnQl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnQl.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbhnQl.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnQl.ps0) with 0x56720 in Hms. change (SR.ps_regs PbhnQl.ps0) with (map (fun i => (i, nth i PbhnQl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnQl.ps0) with PbhnQl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnQl.regs0 PbhnQl.regs_out0 48 KS_bhnQl KS_bhnQl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnQl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnQl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbhnQl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnQl.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnVn := LibSegBs_bhnVn_u.
Definition KS_bhnVn : list nat := Eval vm_compute in (BG.kept_list 48 PbhnVn.regs0 PbhnVn.regs_out0).
Lemma KS_bhnVn_ok : BG.kept_ok 48 PbhnVn.regs0 PbhnVn.regs_out0 KS_bhnVn = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnVn_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.u64_at RSEGS M ((V 2%nat) - 424) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 768) <= bv_unsigned a < ((V 2%nat) - 768) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 768) <= i < ((V 2%nat) - 768) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x34800 M) (st fx' R' 0x35cd0 M')
        /\ (forall x, In x KS_bhnVn -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 215064
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 728)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 424)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 768) ((V 2%nat) - 424)).
Proof.
  intros pvzI1 G2 pvzI2 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PbhnVn.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnVn.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnVn.kn0).
  { unfold know_ok, PbhnVn.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnVn.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnVn.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 768) <= bv_unsigned a < (vz_2 - 768) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbhnVn.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnVn.ps0) with 0x35cd0 in Hms. change (SR.ps_regs PbhnVn.ps0) with (map (fun i => (i, nth i PbhnVn.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnVn.ps0) with PbhnVn.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnVn.regs0 PbhnVn.regs_out0 48 KS_bhnVn KS_bhnVn_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnVn.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnVn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnVn.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnVn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnVn.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhnVn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnVl := LibSegBs_bhnVl_u.
Definition KS_bhnVl_0 : list nat := Eval vm_compute in (BG.kept_list 48 PbhnVl.regs0 PbhnVl.regs_out0).
Lemma KS_bhnVl_0_ok : BG.kept_ok 48 PbhnVl.regs0 PbhnVl.regs_out0 KS_bhnVl_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bhnVl_1 : list nat := Eval vm_compute in (BG.kept_list 48 PbhnVl.regs0 PbhnVl.regs_out1).
Lemma KS_bhnVl_1_ok : BG.kept_ok 48 PbhnVl.regs0 PbhnVl.regs_out1 KS_bhnVl_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnVl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.u64_at RSEGS M ((V 2%nat) - 424) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 408) (V 34%nat) -> 4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 2 -> L5.u64_at RSEGS M ((V 2%nat) - 416) (((V 33%nat) - (V 38%nat)) + 18446744073709551615) ->
  18446744073575333887 <= (V 38%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 768) <= bv_unsigned a < ((V 2%nat) - 768) + 8) -> ~ (((V 2%nat) - 416) <= bv_unsigned a < ((V 2%nat) - 416) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 768) <= i < ((V 2%nat) - 768) + 8) -> ~ (((V 2%nat) - 416) <= i < ((V 2%nat) - 416) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x34800 M) (st fx' R' 0x56720 M')
        /\ (forall x, In x KS_bhnVl_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 215056
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 33%nat)) + (V 34%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 424)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 416) (V 33%nat)
        /\ (((V 33%nat) - (((((V 33%nat) - (V 38%nat)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 768) ((V 2%nat) - 424))
      \/ (msteps RSEGS (st fx R 0x34800 M) (st fx' R' 0x56720 M')
        /\ (forall x, In x KS_bhnVl_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 215056
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 33%nat)) + (V 34%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 424)
        /\ getr R' (reg 13) = Z_to_bv 64 ((((-1) * (V 33%nat)) + (V 38%nat)) + 1)
        /\ getr R' (reg 14) = Z_to_bv 64 (((-1) * (V 33%nat)) + (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 416) (V 33%nat)
        /\ 1 <= (((V 33%nat) - (((((V 33%nat) - (V 38%nat)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 768) ((V 2%nat) - 424))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 pvzI5 K1 K2 K3 K4 pvzI6 K6 K7 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K5l; move K5l before pvzI6; pose proof (proj2 pvzI6) as K5r; move K5r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K8l; move K8l before pvzI7; pose proof (proj2 pvzI7) as K8r; move K8r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PbhnVl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnVl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnVl.kn0).
  { unfold know_ok, PbhnVl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r HV38l HV38r K8l K8r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnVl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnVl.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 768) <= bv_unsigned a < (vz_2 - 768) + 8) -> ~ ((vz_2 - 416) <= bv_unsigned a < (vz_2 - 416) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbhnVl.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PbhnVl.ps0) with 0x56720 in Hms. change (SR.ps_regs PbhnVl.ps0) with (map (fun i => (i, nth i PbhnVl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbhnVl.ps0) with PbhnVl.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnVl.regs0 PbhnVl.regs_out0 48 KS_bhnVl_0 KS_bhnVl_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbhnVl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnVl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnVl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnVl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnVl.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhnVl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnVl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhnVl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r) | clear; lia]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. 
  - right.
    change (SR.ps_pc PbhnVl.ps1) with 0x56720 in Hms. change (SR.ps_regs PbhnVl.ps1) with (map (fun i => (i, nth i PbhnVl.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbhnVl.ps1) with PbhnVl.cells1 in Hcells. unfold PbhnVl.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnVl.regs0 PbhnVl.regs_out1 48 KS_bhnVl_1 KS_bhnVl_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbhnVl.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnVl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnVl.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnVl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnVl.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhnVl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnVl.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhnVl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnVl.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PbhnVl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbhnVl.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PbhnVl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r) | clear; lia]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnI := LibSegBs_bhnI_u.
Definition KS_bhnI : list nat := Eval vm_compute in (BG.kept_list 48 PbhnI.regs0 PbhnI.regs_out0).
Lemma KS_bhnI_ok : BG.kept_ok 48 PbhnI.regs0 PbhnI.regs_out0 KS_bhnI = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x34810 M) (st fx' R' 0x35cd0 M')
        /\ (forall x, In x KS_bhnI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 215064
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 728)).
Proof.
  intros pvzI1 G2 pvzI2 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PbhnI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnI.kn0).
  { unfold know_ok, PbhnI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnI.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbhnI.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnI.ps0) with 0x35cd0 in Hms. change (SR.ps_regs PbhnI.ps0) with (map (fun i => (i, nth i PbhnI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnI.ps0) with PbhnI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnI.regs0 PbhnI.regs_out0 48 KS_bhnI KS_bhnI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnI.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbhnI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnI.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnJs := LibSegBs_bhnJs_u.
Definition KS_bhnJs : list nat := Eval vm_compute in (BG.kept_list 48 PbhnJs.regs0 PbhnJs.regs_out0).
Lemma KS_bhnJs_ok : BG.kept_ok 48 PbhnJs.regs0 PbhnJs.regs_out0 KS_bhnJs = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnJs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.img_clear M 65536 754672 ->
  L5.u8_at RSEGS M ((V 2%nat) - 232) (V 35%nat) -> 0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 312) <= bv_unsigned a < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 312) <= i < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= i < ((V 2%nat) - 296) + 8) -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x34818 M) (st fx' R' 0x81cb4 M')
        /\ (forall x, In x KS_bhnJs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 215168
        /\ getr R' (reg 8) = Z_to_bv 64 740848
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 288)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 751672
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) 740424
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 740832
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) 740792).
Proof.
  intros pvzI1 pvzI2 G2 pvzI3 K1 K2 K3 K4 pvzI4 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV35l; move HV35l before pvzI2; pose proof (proj2 pvzI2) as HV35r; move HV35r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K5l; move K5l before pvzI4; pose proof (proj2 pvzI4) as K5r; move K5r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PbhnJs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnJs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnJs.kn0).
  { unfold know_ok, PbhnJs.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K6) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV35l HV35r K5l K5r K6) | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K6) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K6) | clear; lia | rewrite (L5K.land1_bit0_false vz_35 ltac:(clear - HV35l HV35r K5l K5r K6; lia) K6); clear; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnJs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnJs.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 312) <= bv_unsigned a < (vz_2 - 312) + 8) -> ~ ((vz_2 - 296) <= bv_unsigned a < (vz_2 - 296) + 8) -> ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbhnJs.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnJs.ps0) with 0x81cb4 in Hms. change (SR.ps_regs PbhnJs.ps0) with (map (fun i => (i, nth i PbhnJs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnJs.ps0) with PbhnJs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnJs.regs0 PbhnJs.regs_out0 48 KS_bhnJs KS_bhnJs_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnJs.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnJs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnJs.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbhnJs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnJs.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnJs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnJs.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhnJs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnJs.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhnJs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnJl := LibSegBs_bhnJl_u.
Definition KS_bhnJl : list nat := Eval vm_compute in (BG.kept_list 48 PbhnJl.regs0 PbhnJl.regs_out0).
Lemma KS_bhnJl_ok : BG.kept_ok 48 PbhnJl.regs0 PbhnJl.regs_out0 KS_bhnJl = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnJl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.img_clear M 65536 754672 ->
  L5.u8_at RSEGS M ((V 2%nat) - 232) (V 35%nat) -> 0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = true -> L5.defined M ((V 2%nat) - 231) 7 ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (V 37%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 312) <= bv_unsigned a < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 312) <= i < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= i < ((V 2%nat) - 296) + 8) -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x34818 M) (st fx' R' 0x56720 M')
        /\ (forall x, In x KS_bhnJl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 215144
        /\ getr R' (reg 8) = Z_to_bv 64 740848
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 751672
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) 740552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 740832
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) 740792).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 pvzI4 K1 K2 K3 K4 pvzI5 K6 K7 K8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV35l; move HV35l before pvzI2; pose proof (proj2 pvzI2) as HV35r; move HV35r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K5l; move K5l before pvzI5; pose proof (proj2 pvzI5) as K5r; move K5r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbhnJl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnJl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnJl.kn0).
  { unfold know_ok, PbhnJl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K6) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV35l HV35r K5l K5r K6) | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K6) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K6) | clear; lia | rewrite (L5K.land1_bit0_true vz_35 ltac:(clear - HV35l HV35r K5l K5r K6; lia) K6); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnJl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnJl.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 312) <= bv_unsigned a < (vz_2 - 312) + 8) -> ~ ((vz_2 - 296) <= bv_unsigned a < (vz_2 - 296) + 8) -> ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbhnJl.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnJl.ps0) with 0x56720 in Hms. change (SR.ps_regs PbhnJl.ps0) with (map (fun i => (i, nth i PbhnJl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnJl.ps0) with PbhnJl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnJl.regs0 PbhnJl.regs_out0 48 KS_bhnJl KS_bhnJl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnJl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnJl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnJl.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbhnJl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnJl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnJl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnJl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhnJl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnK := LibSegBs_bhnK_u.
Definition KS_bhnK : list nat := Eval vm_compute in (BG.kept_list 48 PbhnK.regs0 PbhnK.regs_out0).
Lemma KS_bhnK_ok : BG.kept_ok 48 PbhnK.regs0 PbhnK.regs_out0 KS_bhnK = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnK_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 296) <= i < ((V 2%nat) - 296) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x34868 M) (st fx' R' 0x81cb4 M')
        /\ (forall x, In x KS_bhnK -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 215168
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 288)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) 740424).
Proof.
  intros pvzI1 G2 pvzI2 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PbhnK.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnK.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnK.kn0).
  { unfold know_ok, PbhnK.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnK.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnK.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 296) <= bv_unsigned a < (vz_2 - 296) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbhnK.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnK.ps0) with 0x81cb4 in Hms. change (SR.ps_regs PbhnK.ps0) with (map (fun i => (i, nth i PbhnK.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnK.ps0) with PbhnK.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnK.regs0 PbhnK.regs_out0 48 KS_bhnK KS_bhnK_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnK.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnK.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnK.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnK.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnL := LibSegBs_bhnL_u.
Definition KS_bhnL : list nat := Eval vm_compute in (BG.kept_list 48 PbhnL.regs0 PbhnL.regs_out0).
Lemma KS_bhnL_ok : BG.kept_ok 48 PbhnL.regs0 PbhnL.regs_out0 KS_bhnL = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x34880 M) (st fx' R' 0x5d4d0 M')
        /\ (forall x, In x KS_bhnL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 215188
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 11) = Z_to_bv 64 ((bv_unsigned (getr R (reg 8))) + 8)).
Proof.
  intros pvzI1 G2 pvzI2 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PbhnL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnL.kn0).
  { unfold know_ok, PbhnL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnL.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbhnL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnL.ps0) with 0x5d4d0 in Hms. change (SR.ps_regs PbhnL.ps0) with (map (fun i => (i, nth i PbhnL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnL.ps0) with PbhnL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnL.regs0 PbhnL.regs_out0 48 KS_bhnL KS_bhnL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbhnL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhnL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnMs := LibSegBs_bhnMs_u.
Definition KS_bhnMs : list nat := Eval vm_compute in (BG.kept_list 48 PbhnMs.regs0 PbhnMs.regs_out0).
Lemma KS_bhnMs_ok : BG.kept_ok 48 PbhnMs.regs0 PbhnMs.regs_out0 KS_bhnMs = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnMs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.u8_at RSEGS M ((V 2%nat) - 40) (V 35%nat) ->
  0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = false -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 39%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x34894 M) (st fx' R' 0x348c0 M')
        /\ (forall x, In x KS_bhnMs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 pvzI5 K1 K2 K3 pvzI6 K5 K6 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV35l; move HV35l before pvzI2; pose proof (proj2 pvzI2) as HV35r; move HV35r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV39l; move HV39l before pvzI4; pose proof (proj2 pvzI4) as HV39r; move HV39r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 35%nat => Z_to_bv 64 vz_35 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 35%nat => vz_35 | 38%nat => vz_38 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PbhnMs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnMs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnMs.kn0).
  { unfold know_ok, PbhnMs.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV35l HV35r K4l K4r K5) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false vz_35 ltac:(clear - HV35l HV35r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnMs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnMs.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbhnMs.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnMs.ps0) with 0x348c0 in Hms. change (SR.ps_regs PbhnMs.ps0) with (map (fun i => (i, nth i PbhnMs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnMs.ps0) with PbhnMs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnMs.regs0 PbhnMs.regs_out0 48 KS_bhnMs KS_bhnMs_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnMs.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnMs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnMs.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbhnMs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnMs.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbhnMs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbhnMs.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnMs.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnMl := LibSegBs_bhnMl_u.
Definition KS_bhnMl : list nat := Eval vm_compute in (BG.kept_list 48 PbhnMl.regs0 PbhnMl.regs_out0).
Lemma KS_bhnMl_ok : BG.kept_ok 48 PbhnMl.regs0 PbhnMl.regs_out0 KS_bhnMl = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnMl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.u8_at RSEGS M ((V 2%nat) - 40) (V 35%nat) ->
  0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = true -> L5.defined M ((V 2%nat) - 39) 7 -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 37%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x34894 M) (st fx' R' 0x56720 M')
        /\ (forall x, In x KS_bhnMl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 215216
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 pvzI4 K1 K2 K3 pvzI5 K5 K6 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV35l; move HV35l before pvzI2; pose proof (proj2 pvzI2) as HV35r; move HV35r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K4l; move K4l before pvzI5; pose proof (proj2 pvzI5) as K4r; move K4r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PbhnMl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnMl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnMl.kn0).
  { unfold know_ok, PbhnMl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV35l HV35r K4l K4r K5) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_true vz_35 ltac:(clear - HV35l HV35r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnMl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnMl.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbhnMl.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnMl.ps0) with 0x56720 in Hms. change (SR.ps_regs PbhnMl.ps0) with (map (fun i => (i, nth i PbhnMl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnMl.ps0) with PbhnMl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnMl.regs0 PbhnMl.regs_out0 48 KS_bhnMl KS_bhnMl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnMl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnMl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbhnMl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnMl.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhnN := LibSegBs_bhnN_u.
Definition KS_bhnN : list nat := Eval vm_compute in (BG.kept_list 48 PbhnN.regs0 PbhnN.regs_out0).
Lemma KS_bhnN_ok : BG.kept_ok 48 PbhnN.regs0 PbhnN.regs_out0 KS_bhnN = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhnN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 784) ->
  140735332483856 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 784) 784 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 39%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x348b0 M) (st fx' R' 0x348c0 M')
        /\ (forall x, In x KS_bhnN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 pvzI4 K1 K2 K3 K4.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV38l; move HV38l before pvzI2; pose proof (proj2 pvzI2) as HV38r; move HV38r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV39l; move HV39l before pvzI3; pose proof (proj2 pvzI3) as HV39r; move HV39r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 38%nat => vz_38 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PbhnN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhnN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhnN.kn0).
  { unfold know_ok, PbhnN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhnN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhnN.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbhnN.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhnN.ps0) with 0x348c0 in Hms. change (SR.ps_regs PbhnN.ps0) with (map (fun i => (i, nth i PbhnN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhnN.ps0) with PbhnN.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhnN.regs0 PbhnN.regs_out0 48 KS_bhnN KS_bhnN_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhnN.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhnN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnN.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbhnN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhnN.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbhnN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbhnN.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhnN.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End PNSHP.
