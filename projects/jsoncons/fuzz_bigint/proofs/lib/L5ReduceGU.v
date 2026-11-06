(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     Ub0_code_21248_21b5c BigBranchUb0 BigContractUb0 BigContractDivU BigLinkBase BigLinkGlueUb0 BigLinkInlBaseU BigLinkDivBaseU L5Defs L5Words L5ReduceU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5ReduceGU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5REDGU.
Import L5REDU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Module P0 := LibSegZ_rd0u.
Module PI := LibSegZ_rdAiu.
Module PD := LibSegZ_rdAdu.
Module PK := LibSegZ_rdkeepu.
Module PP := LibSegZ_rdpopu.
Module PZ := LibSegZ_rdpopzu.

Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


(* [comment removed for export] *)
Definition KS : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Lemma KS0_ok : BGU.kept_ok 40 P0.regs0 P0.regs_out KS = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSI_ok : BGU.kept_ok 40 PI.regs0 PI.regs_out KS = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSD_ok : BGU.kept_ok 40 PD.regs0 PD.regs_out KS = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSK_ok : BGU.kept_ok 40 PK.regs0 PK.regs_out KS = true. Proof. vm_compute. reflexivity. Qed.
Definition KS11 : list nat := 11%nat :: KS.
Lemma KSP_ok : BGU.kept_ok 40 PP.regs0 PP.regs_out KS11 = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSZ_ok : BGU.kept_ok 40 PZ.regs0 PZ.regs_out KS = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac ks Hc := simpl in Hc; repeat (destruct Hc as [Hc|Hc]; [subst; vm_compute; tauto|]); contradiction.

(* [comment removed for export] *)
Definition e8L : expr := EMd M_MUL (ELit 8) (EVar 34).
Definition z8L : BL.za := Eval vm_compute in (BL.zc e8L).
Lemma z8L_ok : BL.zcomp e8L = Some z8L. Proof. vm_compute. reflexivity. Qed.
Lemma z8L_val V n : V 34%nat = n -> 0 <= n <= 2 ^ 27 -> BL.zden V z8L = 8 * n.
Proof. intros H Hn. cbn [BL.zden z8L]. rewrite H. unfold BL.MM. rewrite Z.mod_small; lia. Qed.
Definition z16 : BL.za := Eval vm_compute in (BL.zc (ELit 16)).
Lemma z16_ok : BL.zcomp (ELit 16) = Some z16. Proof. vm_compute. reflexivity. Qed.
Lemma z16_val V : BL.zden V z16 = 16. Proof. reflexivity. Qed.
Definition eCUR : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 34)) (EVar 35)) (ELit (-8)).
Definition zCUR : BL.za := Eval vm_compute in (BL.zc eCUR).
Lemma zCUR_ok : BL.zcomp eCUR = Some zCUR. Proof. vm_compute. reflexivity. Qed.
Definition eCUR2 : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 34)) (EVar 35)) (ELit (-16)).
Definition zCUR2 : BL.za := Eval vm_compute in (BL.zc eCUR2).
Lemma zCUR2_ok : BL.zcomp eCUR2 = Some zCUR2. Proof. vm_compute. reflexivity. Qed.

Definition eTOP : expr := EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 34)) (EVar 35).   (* [comment removed for export] *)
Definition zTOP : BL.za := Eval vm_compute in (BL.zc eTOP).
Lemma zTOP_ok : BL.zcomp eTOP = Some zTOP. Proof. vm_compute. reflexivity. Qed.
Definition eTOPI : expr := EAlu ALU_ADD (EVar 10) (EMd M_MUL (ELit 8) (EVar 34)).  (* [comment removed for export] *)
Definition zTOPI : BL.za := Eval vm_compute in (BL.zc eTOPI).
Lemma zTOPI_ok : BL.zcomp eTOPI = Some zTOPI. Proof. vm_compute. reflexivity. Qed.
Lemma kn0_P : PP.kn0 = [KRange (EVar 10) 1048576 140737488355328; KAlign (EVar 10) 8; KWr (SA (EVar 10) 0) (ELit 16);
   KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 8;
   KDisj (SA (EVar 10) 0) (ELit 16) (SA (EVar 35) 0) e8L; KRange (EVar 34) 2 134217728; KWord (SA eTOP (-16)) 8 (EVar 36)].
Proof. vm_compute. reflexivity. Qed.
Lemma kn0_D : PD.kn0 = [KRange (EVar 10) 1048576 140737488355328; KAlign (EVar 10) 8; KWr (SA (EVar 10) 0) (ELit 16);
   KWord (SA (EVar 10) 0) 1 (EVar 33); KRange (EVar 33) 0 255; KRange (EAlu ALU_AND (EVar 33) (ELit 1)) 1 1;
   KWord (SA (EVar 10) 8) 8 (EVar 34); KWord (SA (EVar 10) 24) 8 (EVar 35); KRange (EVar 34) 1 134217728;
   KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 8;
   KDisj (SA (EVar 10) 0) (ELit 16) (SA (EVar 35) 0) e8L; KWord (SA eTOP (-8)) 8 (EVar 36)].
Proof. vm_compute. reflexivity. Qed.
Lemma kn0_I : PI.kn0 = [KRange (EVar 10) 1048576 140737488355328; KAlign (EVar 10) 8; KWr (SA (EVar 10) 0) (ELit 16);
   KWord (SA (EVar 10) 0) 1 (EVar 33); KRange (EVar 33) 0 255; KRange (EAlu ALU_AND (EVar 33) (ELit 1)) 0 0;
   KWord (SA (EVar 10) 8) 8 (EVar 34); KRange (EVar 34) 1 2; KWord (SA eTOPI 8) 8 (EVar 36)].
Proof. vm_compute. reflexivity. Qed.
Lemma kn0_Z : PZ.kn0 = [KRange (EVar 10) 1048576 140737488355328; KAlign (EVar 10) 8; KWr (SA (EVar 10) 0) (ELit 16);
   KRange (EVar 35) 4096 140737488355328; KWord (SA (EVar 10) 0) 1 (EVar 33); KRange (EVar 33) 0 255].
Proof. vm_compute. reflexivity. Qed.
Lemma kn0_0 : P0.kn0 = [KRange (EVar 10) 1048576 140737488355328; KAlign (EVar 10) 8; KWr (SA (EVar 10) 0) (ELit 16);
   KWord (SA (EVar 10) 0) 1 (EVar 33); KRange (EVar 33) 0 255; KWord (SA (EVar 10) 8) 8 (ELit 0)].
Proof. vm_compute. reflexivity. Qed.
Lemma r16_D : nth 16 PD.regs_out (ELit 0) = eCUR. Proof. vm_compute. reflexivity. Qed.
Lemma r16_I : nth 16 PI.regs_out (ELit 0) = EAlu ALU_ADD (EAlu ALU_ADD (EVar 10) (EMd M_MUL (ELit 8) (EVar 34))) (ELit 8). Proof. vm_compute. reflexivity. Qed.
Lemma r16_P : nth 16 PP.regs_out (ELit 0) = eCUR2. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pc_lit (z : Z) (w : word) : bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof. intros H. symmetry. apply BGU.word_of_unsigned. exact H. Qed.
Lemma rl17 : (17%bv : bv 5) = reg 17. Proof. apply bv_eq. reflexivity. Qed.
Lemma br219f4_tk fx M R : getr R (reg 17) <> Z_to_bv 64 0 -> msteps RSEGS (st fx R 0x21b2c M) (st fx R 0x21b44 M).
Proof. intros H. rewrite (pc_lit 0x21b2c (0x21b2c%bv : word)) by reflexivity. rewrite (pc_lit 0x21b44 (0x21b44%bv : word)) by reflexivity.
  apply bru_21a84_tk. rewrite rl17. exact H. Qed.
Lemma br219f4_ft fx M R : getr R (reg 17) = Z_to_bv 64 0 -> msteps RSEGS (st fx R 0x21b2c M) (st fx R 0x21b30 M).
Proof. intros H. rewrite (pc_lit 0x21b2c (0x21b2c%bv : word)) by reflexivity. rewrite (pc_lit 0x21b30 (0x21b30%bv : word)) by reflexivity.
  apply bru_21a84_ft. rewrite rl17. exact H. Qed.
Lemma cells_P : PP.cells = [KWord (SA (EVar 10) 8) 8 (EAlu ALU_ADD (EVar 34) (ELit (-1)))]. Proof. vm_compute. reflexivity. Qed.
Lemma cells_Z : PZ.cells = [KWord (SA (EVar 10) 0) 1 (EAlu ALU_AND (EVar 33) (ELit 253)); KWord (SA (EVar 10) 8) 8 (ELit 0)]. Proof. vm_compute. reflexivity. Qed.
Lemma cells_0 : P0.cells = [KWord (SA (EVar 10) 0) 1 (EAlu ALU_AND (EVar 33) (ELit 253))]. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition at_test (R : bvmap 5 word) (M : word -> option byte) (o fb d X : Z) (L : nat) : Prop :=
  getr R (reg 10) = Z_to_bv 64 o /\ getr R (reg 11) = Z_to_bv 64 fb /\ getr R (reg 12) = Z_to_bv 64 d /\
  getr R (reg 13) = Z_to_bv 64 (Z.of_nat L - 1) /\ getr R (reg 14) = Z_to_bv 64 9 /\ getr R (reg 15) = Z_to_bv 64 0 /\
  getr R (reg 16) = Z_to_bv 64 (d + 8 * Z.of_nat L - 8) /\ getr R (reg 17) = Z_to_bv 64 X /\
  0 <= X < 2 ^ 64 /\ BGU.u64_at M (o + 8) (Z.of_nat L) /\ BGU.u64_at M (d + 8 * Z.of_nat L - 8) X.

(* [comment removed for export] *)
Record frame_ok (M : word -> option byte) (o fb d cap : Z) : Prop := FOK {
  f_o : 2 ^ 20 <= o /\ o + 32 <= 2 ^ 47 /\ o mod 8 = 0;
  f_w : BGU.writable M o 16;
  f_fb : 0 <= fb < 256 /\ BGU.u8_at M o fb;
  f_d : 4096 <= d /\ d + 8 * cap <= 2 ^ 47 /\ d mod 8 = 0 /\ 1 <= cap <= 2 ^ 27;
  f_def : BGU.defined M d (8 * cap);
  f_ap : o + 16 <= d \/ d + 8 * cap <= o }.

Lemma frame_ok_keep M M' o fb d cap : frame_ok M o fb d cap -> mem_grows M M' ->
  (forall x : word, ~ (o + 8 <= bv_unsigned x < o + 16) -> M' x = M x) -> frame_ok M' o fb d cap.
Proof.
  intros [Fo Fw [Ffb Fu8] Fd Fdef Fap] G K. constructor; auto.
  - eapply BGU.writable_grows; eauto.
  - split. exact Ffb. eapply (BGU.u8_keep M M'). exact K. lia. lia. exact Fu8.
  - eapply BGU.defined_grows; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma keep_conc fx R M (L : nat) :
  getr R (reg 13) = Z_to_bv 64 (Z.of_nat L - 1) -> (1 <= L)%nat -> Z.of_nat L <= 2 ^ 27 ->
  exists fx' R' M', msteps RSEGS (st fx R 0x21b44 M) (st fx' R' 0x21b4c M')
    /\ (forall x, In x KS -> getr R' (reg x) = getr R (reg x)) /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros H13 HL1 HL2.
  set (Vf := fun k : nat => match k with 34%nat => Z_to_bv 64 (Z.of_nat L) | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U34: bv_unsigned (ev E 34) = Z.of_nat L) by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E PK.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbn [BGU.slots tl PK.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
    rewrite BGU.alu_add_lit, H13. f_equal; lia. }
  assert (HK: know_ok RSEGS E M PK.kn0).
  { unfold know_ok. change PK.kn0 with [KRange (EVar 34) 1 134217728]. apply Forall_cons. eapply BGU.kentry_KRange_var. exact U34. lia. apply Forall_nil. }
  destruct (PK.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change PK.NX0 with 40%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' PK.regs0 PK.regs_out 40 KS KSK_ok HR Hag Hregs j Hj). }
  split. { intros a. apply Hfr. constructor. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pop_conc fx R M (o fb d cap X' : Z) (L : nat) :
  frame_ok M o fb d cap ->
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 12) = Z_to_bv 64 d -> getr R (reg 13) = Z_to_bv 64 (Z.of_nat L - 1) ->
  getr R (reg 14) = Z_to_bv 64 9 -> getr R (reg 15) = Z_to_bv 64 0 -> getr R (reg 16) = Z_to_bv 64 (d + 8 * Z.of_nat L - 8) ->
  (2 <= L)%nat -> Z.of_nat L <= cap ->
  BGU.u64_at M (d + 8 * Z.of_nat L - 16) X' -> 0 <= X' < 2 ^ 64 ->
  exists fx' R' M', msteps RSEGS (st fx R 0x21b30 M) (st fx' R' 0x21b2c M')
    /\ (forall x, In x KS11 -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 12) = Z_to_bv 64 d /\ getr R' (reg 13) = Z_to_bv 64 (Z.of_nat L - 2)
    /\ getr R' (reg 14) = Z_to_bv 64 9 /\ getr R' (reg 15) = Z_to_bv 64 0
    /\ getr R' (reg 16) = Z_to_bv 64 (d + 8 * Z.of_nat L - 16) /\ getr R' (reg 17) = Z_to_bv 64 X'
    /\ BGU.u64_at M' (o + 8) (Z.of_nat L - 1)
    /\ (forall a : word, ~ (o + 8 <= bv_unsigned a < o + 16) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros FR H10 H12 H13 H14 H15 H16 HL HLc HX RX. destruct FR as [Fo Fw [Ffb Fu8] Fd Fdef Fap].
  set (Vf := fun k : nat => match k with 34%nat => Z_to_bv 64 (Z.of_nat L) | 35%nat => Z_to_bv 64 d | 36%nat => Z_to_bv 64 X' | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U10: bv_unsigned (ev E 10) = o) by (cbn [E ev Vf]; rewrite H10; apply BGU.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = Z.of_nat L) by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = d) by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = X') by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (Z8: BL.zden (BL.uv E) z8L = 8 * Z.of_nat L) by (apply z8L_val; [exact U34 | lia]).
  assert (ATOP: bv_unsigned (edenot E eTOP) = 8 * Z.of_nat L + d).
  { rewrite (BL.zcomp_sound E eTOP zTOP zTOP_ok). cbn [BL.zden zTOP]. unfold BL.uv. rewrite U34, U35. unfold BL.MM.
    rewrite (Z.mod_small (8 * _)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (HR: regs_ok E PP.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbn [BGU.slots tl PP.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
    rewrite BGU.alu_add_lit, H13. f_equal; lia.
    rewrite BGU.md_mul_lit, !BGU.alu_add_lit, H16. f_equal; lia. }
  assert (HK: know_ok RSEGS E M PP.kn0).
  { unfold know_ok. rewrite kn0_P.
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U10. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U10. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U10. lia. lia. lia. rewrite Z.add_0_r. exact Fw. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U35. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U35. lia. lia. }
    apply Forall_cons. { eapply (BGU.kentry_KDisj_z E M 10 0 (ELit 16) z16 16 35 0 e8L z8L (8 * Z.of_nat L) o d U10 U35 z16_ok (z16_val _) z8L_ok Z8). lia. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U34. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_e. exact ATOP. cbn [edenot]. exact U36. lia. lia. replace (8 * Z.of_nat L + d + -16) with (d + 8 * Z.of_nat L - 16) by lia. exact HX. }
    apply Forall_nil. }
  destruct (PP.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change PP.NX0 with 40%nat in Hag.
  assert (AG: forall k, (k < 40)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (A10: bv_unsigned (ev E' 10) = o) by (rewrite AG by lia; exact U10).
  assert (MF: forall a : word, ~ (o + 8 <= bv_unsigned a < o + 16) -> M' a = M a).
  { intros a Ha. apply Hfr. unfold SGP.outside. change PP.F0 with [(EVar 10, 8, ELit 8)]. constructor; [|constructor].
    unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A10. rewrite BGU.unsigned_lit by lia. lia. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' PP.regs0 PP.regs_out 40 KS11 KSP_ok HR Hag Hregs j Hj). }
  split. { rewrite (BGU.out_reg PP.regs_out E' R' 12 Hregs) by lia. change (nth 12 PP.regs_out (ELit 0)) with (EVar 35). cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U35. }
  split. { rewrite (BGU.out_reg PP.regs_out E' R' 13 Hregs) by lia. change (nth 13 PP.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 34) (ELit (-2))).
           apply BGU.word_of_unsigned. cbn [edenot]. rewrite AG by lia. rewrite (BL.zalu_sound ALU_ADD (ev E 34) (Z_to_bv 64 (-2)) (Z.of_nat L - 2)). reflexivity.
           cbn [BL.zalu]. rewrite U34. unfold BL.MM. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
           rewrite Zplus_mod_idemp_r. rewrite Z.mod_small by lia. f_equal; lia. }
  split. { rewrite (BGU.out_reg PP.regs_out E' R' 14 Hregs) by lia. reflexivity. }
  split. { rewrite (BGU.out_reg PP.regs_out E' R' 15 Hregs) by lia. reflexivity. }
  split. { rewrite (BGU.out_reg PP.regs_out E' R' 16 Hregs) by lia. rewrite r16_P. apply BGU.word_of_unsigned.
           rewrite (BGU.edenot_kept 40 E E') by (auto; reflexivity). rewrite (BL.zcomp_sound E eCUR2 zCUR2 zCUR2_ok). cbn [BL.zden zCUR2]. unfold BL.uv.
           rewrite U34, U35. unfold BL.MM. rewrite (Z.mod_small (8 * _)) by lia. rewrite (Z.mod_small (_ + d)) by lia.
           replace (8 * Z.of_nat L + d + 18446744073709551600) with ((d + 8 * Z.of_nat L - 16) + 1 * 2 ^ 64) by lia.
           rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
  split. { rewrite (BGU.out_reg PP.regs_out E' R' 17 Hregs) by lia. change (nth 17 PP.regs_out (ELit 0)) with (EVar 36). cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U36. }
  split. { eapply (BGU.u64_of_KWord E' M' 10 8). apply Hcells. change (SR.ps_cells PP.ps0) with PP.cells. rewrite cells_P. left; reflexivity. exact A10.
           cbn [edenot]. rewrite AG by lia. rewrite (BL.zalu_sound ALU_ADD (ev E 34) (Z_to_bv 64 (-1)) (Z.of_nat L - 1)). reflexivity.
           cbn [BL.zalu]. rewrite U34. unfold BL.MM. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
           rewrite Zplus_mod_idemp_r. rewrite Z.mod_small by lia. f_equal; lia. }
  split. exact MF. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma popz_conc fx R M (o fb d cap : Z) :
  frame_ok M o fb d cap ->
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 fb -> getr R (reg 12) = Z_to_bv 64 d ->
  getr R (reg 13) = Z_to_bv 64 0 -> getr R (reg 14) = Z_to_bv 64 9 -> getr R (reg 15) = Z_to_bv 64 0 -> getr R (reg 16) = Z_to_bv 64 d ->
  exists fx' R' M', msteps RSEGS (st fx R 0x21b30 M) (st fx' R' 0x21b58 M')
    /\ (forall x, In x KS -> getr R' (reg x) = getr R (reg x))
    /\ BGU.u8_at M' o (Z.land fb 253) /\ BGU.u64_at M' (o + 8) 0
    /\ (forall a : word, ~ (o <= bv_unsigned a < o + 16) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros FR H10 H11 H12 H13 H14 H15 H16. destruct FR as [Fo Fw [Ffb Fu8] Fd Fdef Fap].
  set (Vf := fun k : nat => match k with 33%nat => Z_to_bv 64 fb | 35%nat => Z_to_bv 64 d | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U10: bv_unsigned (ev E 10) = o) by (cbn [E ev Vf]; rewrite H10; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb) by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = d) by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E PZ.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbn [BGU.slots tl PZ.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. }
  assert (HK: know_ok RSEGS E M PZ.kn0).
  { unfold know_ok. rewrite kn0_Z.
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U10. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U10. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U10. lia. lia. lia. rewrite Z.add_0_r. exact Fw. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U35. lia. }
    apply Forall_cons. { eapply (BDU.kentry_KWord1_var E M 10 0 33 o fb U10 U33). lia. lia. lia. rewrite Z.add_0_r. exact Fu8. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U33. lia. }
    apply Forall_nil. }
  destruct (PZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change PZ.NX0 with 40%nat in Hag.
  assert (AG: forall k, (k < 40)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (A10: bv_unsigned (ev E' 10) = o) by (rewrite AG by lia; exact U10).
  assert (A33: bv_unsigned (ev E' 33) = fb) by (rewrite AG by lia; exact U33).
  assert (MF: forall a : word, ~ (o <= bv_unsigned a < o + 16) -> M' a = M a).
  { intros a Ha. apply Hfr. unfold SGP.outside. change PZ.F0 with [(EVar 10, 0, ELit 1); (EVar 10, 8, ELit 8)].
    constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A10. rewrite BGU.unsigned_lit by lia. lia. }
    constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A10. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' PZ.regs0 PZ.regs_out 40 KS KSZ_ok HR Hag Hregs j Hj). }
  split. { replace o with (o + 0) by lia. eapply (BIU.u8_of_KWord1_e E' M' 10 0 (EAlu ALU_AND (EVar 33) (ELit 253)) o (Z.land fb 253)).
           apply Hcells. change (SR.ps_cells PZ.ps0) with PZ.cells. rewrite cells_Z. left; reflexivity. exact A10.
           cbn [edenot]. apply BGU.word_of_unsigned. rewrite BDU.and_lit_val by lia. rewrite A33. reflexivity.
           apply L5.land_byte_range. lia. }
  split. { eapply (BGU.u64_of_KWord E' M' 10 8). apply Hcells. change (SR.ps_cells PZ.ps0) with PZ.cells. rewrite cells_Z. right; left; reflexivity. exact A10. reflexivity. }
  split. exact MF. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rd0_conc fx R M (o fb : Z) :
  getr R (reg 10) = Z_to_bv 64 o -> 2 ^ 20 <= o -> o + 32 <= 2 ^ 47 -> o mod 8 = 0 -> BGU.writable M o 16 ->
  0 <= fb < 256 -> BGU.u8_at M o fb -> BGU.u64_at M (o + 8) 0 ->
  exists fx' R' M', msteps RSEGS (st fx R 0x21abc M) (st fx' R' 0x21b58 M')
    /\ (forall x, In x KS -> getr R' (reg x) = getr R (reg x))
    /\ BGU.u8_at M' o (Z.land fb 253)
    /\ (forall a : word, ~ (o <= bv_unsigned a < o + 1) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros H10 Ro Rh A8 Fw Ffb Fu8 O8.
  set (Vf := fun k : nat => match k with 33%nat => Z_to_bv 64 fb | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U10: bv_unsigned (ev E 10) = o) by (cbn [E ev Vf]; rewrite H10; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb) by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E P0.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbn [BGU.slots tl P0.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. }
  assert (HK: know_ok RSEGS E M P0.kn0).
  { unfold know_ok. rewrite kn0_0.
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U10. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U10. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U10. lia. lia. lia. rewrite Z.add_0_r. exact Fw. }
    apply Forall_cons. { eapply (BDU.kentry_KWord1_var E M 10 0 33 o fb U10 U33). lia. lia. lia. rewrite Z.add_0_r. exact Fu8. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U33. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_lit. exact U10. lia. lia. exact O8. }
    apply Forall_nil. }
  destruct (P0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change P0.NX0 with 40%nat in Hag.
  assert (AG: forall k, (k < 40)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (A10: bv_unsigned (ev E' 10) = o) by (rewrite AG by lia; exact U10).
  assert (A33: bv_unsigned (ev E' 33) = fb) by (rewrite AG by lia; exact U33).
  assert (MF: forall a : word, ~ (o <= bv_unsigned a < o + 1) -> M' a = M a).
  { intros a Ha. apply Hfr. unfold SGP.outside. change P0.F0 with [(EVar 10, 0, ELit 1)].
    constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A10. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' P0.regs0 P0.regs_out 40 KS KS0_ok HR Hag Hregs j Hj). }
  split. { replace o with (o + 0) by lia. eapply (BIU.u8_of_KWord1_e E' M' 10 0 (EAlu ALU_AND (EVar 33) (ELit 253)) o (Z.land fb 253)).
           apply Hcells. change (SR.ps_cells P0.ps0) with P0.cells. rewrite cells_0. left; reflexivity. exact A10.
           cbn [edenot]. apply BGU.word_of_unsigned. rewrite BDU.and_lit_val by lia. rewrite A33. reflexivity.
           apply L5.land_byte_range. lia. }
  split. exact MF. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdAd_conc fx R M (o fb d cap X : Z) (L : nat) :
  frame_ok M o fb d cap -> Z.testbit fb 0 = true ->
  getr R (reg 10) = Z_to_bv 64 o -> (1 <= L)%nat -> Z.of_nat L <= cap ->
  BGU.u64_at M (o + 8) (Z.of_nat L) -> BGU.u64_at M (o + 24) d -> BGU.u64_at M (d + 8 * Z.of_nat L - 8) X -> 0 <= X < 2 ^ 64 ->
  exists fx' R' M', msteps RSEGS (st fx R 0x21abc M) (st fx' R' 0x21b2c M')
    /\ (forall x, In x KS -> getr R' (reg x) = getr R (reg x))
    /\ at_test R' M' o fb d X L
    /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros FR B0 H10 HL HLc O8 O24 HX RX. destruct FR as [Fo Fw [Ffb Fu8] Fd Fdef Fap].
  set (Vf := fun k : nat => match k with 33%nat => Z_to_bv 64 fb | 34%nat => Z_to_bv 64 (Z.of_nat L) | 35%nat => Z_to_bv 64 d | 36%nat => Z_to_bv 64 X | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U10: bv_unsigned (ev E 10) = o) by (cbn [E ev Vf]; rewrite H10; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb) by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = Z.of_nat L) by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = d) by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = X) by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (Z8: BL.zden (BL.uv E) z8L = 8 * Z.of_nat L) by (apply z8L_val; [exact U34 | lia]).
  assert (ATOP: bv_unsigned (edenot E eTOP) = 8 * Z.of_nat L + d).
  { rewrite (BL.zcomp_sound E eTOP zTOP zTOP_ok). cbn [BL.zden zTOP]. unfold BL.uv. rewrite U34, U35. unfold BL.MM.
    rewrite (Z.mod_small (8 * _)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (HR: regs_ok E PD.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbn [BGU.slots tl PD.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. }
  assert (HK: know_ok RSEGS E M PD.kn0).
  { unfold know_ok. rewrite kn0_D.
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U10. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U10. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U10. lia. lia. lia. rewrite Z.add_0_r. exact Fw. }
    apply Forall_cons. { eapply (BDU.kentry_KWord1_var E M 10 0 33 o fb U10 U33). lia. lia. lia. rewrite Z.add_0_r. exact Fu8. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U33. lia. }
    apply Forall_cons. { cbn [kentry_ok edenot]. rewrite BDU.and_lit_val by lia. cbn [ev E Vf]. rewrite BGU.unsigned_lit by lia.
                         rewrite <- (Z.land_ones fb 1) in B0 |- * || idtac.
                         assert (Hb : Z.land fb 1 = 1). { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
                           destruct (Z.eq_dec i 0) as [->|Hi0]. rewrite B0. reflexivity.
                           replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r. reflexivity. }
                         rewrite Hb. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U10. exact U34. lia. lia. exact O8. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U10. exact U35. lia. lia. exact O24. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U34. lia. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U35. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U35. lia. lia. }
    apply Forall_cons. { eapply (BGU.kentry_KDisj_z E M 10 0 (ELit 16) z16 16 35 0 e8L z8L (8 * Z.of_nat L) o d U10 U35 z16_ok (z16_val _) z8L_ok Z8). lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_e. exact ATOP. cbn [edenot]. exact U36. lia. lia. replace (8 * Z.of_nat L + d + -8) with (d + 8 * Z.of_nat L - 8) by lia. exact HX. }
    apply Forall_nil. }
  destruct (PD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change PD.NX0 with 40%nat in Hag.
  assert (AG: forall k, (k < 40)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr. constructor. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' PD.regs0 PD.regs_out 40 KS KSD_ok HR Hag Hregs j Hj). }
  split.
  { unfold at_test. repeat split.
    - rewrite (BGU.kept_regs E E' R R' PD.regs0 PD.regs_out 40 KS KSD_ok HR Hag Hregs 10%nat) by (cbn; tauto). exact H10.
    - rewrite (BGU.out_reg PD.regs_out E' R' 11 Hregs) by lia. change (nth 11 PD.regs_out (ELit 0)) with (EVar 33). cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U33.
    - rewrite (BGU.out_reg PD.regs_out E' R' 12 Hregs) by lia. change (nth 12 PD.regs_out (ELit 0)) with (EVar 35). cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U35.
    - rewrite (BGU.out_reg PD.regs_out E' R' 13 Hregs) by lia. change (nth 13 PD.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 34) (ELit (-1))).
      apply BGU.word_of_unsigned. cbn [edenot]. rewrite AG by lia. rewrite (BL.zalu_sound ALU_ADD (ev E 34) (Z_to_bv 64 (-1)) (Z.of_nat L - 1)). reflexivity.
      cbn [BL.zalu]. rewrite U34. unfold BL.MM. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Zplus_mod_idemp_r. rewrite Z.mod_small by lia. f_equal; lia.
    - rewrite (BGU.out_reg PD.regs_out E' R' 14 Hregs) by lia. reflexivity.
    - rewrite (BGU.out_reg PD.regs_out E' R' 15 Hregs) by lia. reflexivity.
    - rewrite (BGU.out_reg PD.regs_out E' R' 16 Hregs) by lia. rewrite r16_D. apply BGU.word_of_unsigned.
      rewrite (BGU.edenot_kept 40 E E') by (auto; reflexivity). rewrite (BL.zcomp_sound E eCUR zCUR zCUR_ok). cbn [BL.zden zCUR]. unfold BL.uv.
      rewrite U34, U35. unfold BL.MM. rewrite (Z.mod_small (8 * _)) by lia. rewrite (Z.mod_small (_ + d)) by lia.
      replace (8 * Z.of_nat L + d + 18446744073709551608) with ((d + 8 * Z.of_nat L - 8) + 1 * 2 ^ 64) by lia.
      rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity.
    - rewrite (BGU.out_reg PD.regs_out E' R' 17 Hregs) by lia. change (nth 17 PD.regs_out (ELit 0)) with (EVar 36). cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U36.
    - exact (proj1 RX). - exact (proj2 RX).
    - eapply BGU.u64_at_frame. lia. lia. intros k Hk; apply MM. exact O8.
    - eapply BGU.u64_at_frame. lia. lia. intros k Hk; apply MM. exact HX. }
  split. exact MM. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdAi_conc fx R M (o fb cap X : Z) (L : nat) :
  frame_ok M o fb (o + 16) cap -> Z.testbit fb 0 = false ->
  getr R (reg 10) = Z_to_bv 64 o -> (1 <= L <= 2)%nat ->
  BGU.u64_at M (o + 8) (Z.of_nat L) -> BGU.u64_at M (o + 16 + 8 * Z.of_nat L - 8) X -> 0 <= X < 2 ^ 64 ->
  exists fx' R' M', msteps RSEGS (st fx R 0x21abc M) (st fx' R' 0x21b2c M')
    /\ (forall x, In x KS -> getr R' (reg x) = getr R (reg x))
    /\ at_test R' M' o fb (o + 16) X L
    /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros FR B0 H10 HL O8 HX RX. destruct FR as [Fo Fw [Ffb Fu8] Fd Fdef Fap].
  set (Vf := fun k : nat => match k with 33%nat => Z_to_bv 64 fb | 34%nat => Z_to_bv 64 (Z.of_nat L) | 36%nat => Z_to_bv 64 X | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U10: bv_unsigned (ev E 10) = o) by (cbn [E ev Vf]; rewrite H10; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb) by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = Z.of_nat L) by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = X) by (cbn [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (ATOP: bv_unsigned (edenot E eTOPI) = o + 8 * Z.of_nat L).
  { rewrite (BL.zcomp_sound E eTOPI zTOPI zTOPI_ok). cbn [BL.zden zTOPI]. unfold BL.uv. rewrite U34, U10. unfold BL.MM.
    rewrite (Z.mod_small (8 * _)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (HR: regs_ok E PI.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbn [BGU.slots tl PI.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. }
  assert (HK: know_ok RSEGS E M PI.kn0).
  { unfold know_ok. rewrite kn0_I.
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U10. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U10. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U10. lia. lia. lia. rewrite Z.add_0_r. exact Fw. }
    apply Forall_cons. { eapply (BDU.kentry_KWord1_var E M 10 0 33 o fb U10 U33). lia. lia. lia. rewrite Z.add_0_r. exact Fu8. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U33. lia. }
    apply Forall_cons. { cbn [kentry_ok edenot]. rewrite BDU.and_lit_val by lia. cbn [ev E Vf]. rewrite BGU.unsigned_lit by lia.
                         assert (Hb : Z.land fb 1 = 0). { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
                           destruct (Z.eq_dec i 0) as [->|Hi0]. rewrite B0. reflexivity.
                           replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). apply Bool.andb_false_r. }
                         rewrite Hb. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U10. exact U34. lia. lia. exact O8. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U34. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_e. exact ATOP. cbn [edenot]. exact U36. lia. lia. replace (o + 8 * Z.of_nat L + 8) with (o + 16 + 8 * Z.of_nat L - 8) by lia. exact HX. }
    apply Forall_nil. }
  destruct (PI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change PI.NX0 with 40%nat in Hag.
  assert (AG: forall k, (k < 40)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr. constructor. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' PI.regs0 PI.regs_out 40 KS KSI_ok HR Hag Hregs j Hj). }
  split.
  { unfold at_test. repeat split.
    - rewrite (BGU.kept_regs E E' R R' PI.regs0 PI.regs_out 40 KS KSI_ok HR Hag Hregs 10%nat) by (cbn; tauto). exact H10.
    - rewrite (BGU.out_reg PI.regs_out E' R' 11 Hregs) by lia. change (nth 11 PI.regs_out (ELit 0)) with (EVar 33). cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U33.
    - rewrite (BGU.out_reg PI.regs_out E' R' 12 Hregs) by lia. change (nth 12 PI.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 10) (ELit 16)). cbn [edenot]. rewrite AG by lia.
      apply BGU.word_of_unsigned. rewrite (BL.zalu_sound ALU_ADD (ev E 10) (Z_to_bv 64 16) (o + 16)). reflexivity. cbn [BL.zalu]. rewrite U10, BGU.unsigned_lit by lia. unfold BL.MM. rewrite Z.mod_small by lia. reflexivity.
    - rewrite (BGU.out_reg PI.regs_out E' R' 13 Hregs) by lia. change (nth 13 PI.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 34) (ELit (-1))).
      apply BGU.word_of_unsigned. cbn [edenot]. rewrite AG by lia. rewrite (BL.zalu_sound ALU_ADD (ev E 34) (Z_to_bv 64 (-1)) (Z.of_nat L - 1)). reflexivity.
      cbn [BL.zalu]. rewrite U34. unfold BL.MM. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Zplus_mod_idemp_r. rewrite Z.mod_small by lia. f_equal; lia.
    - rewrite (BGU.out_reg PI.regs_out E' R' 14 Hregs) by lia. reflexivity.
    - rewrite (BGU.out_reg PI.regs_out E' R' 15 Hregs) by lia. reflexivity.
    - rewrite (BGU.out_reg PI.regs_out E' R' 16 Hregs) by lia. rewrite r16_I. apply BGU.word_of_unsigned.
      replace (edenot E' (EAlu ALU_ADD (EAlu ALU_ADD (EVar 10) (EMd M_MUL (ELit 8) (EVar 34))) (ELit 8))) with (alu64 ALU_ADD (edenot E' eTOPI) (Z_to_bv 64 8)) by reflexivity.
      rewrite (BGU.edenot_kept 40 E E') by (auto; reflexivity). rewrite (BL.zalu_sound ALU_ADD (edenot E eTOPI) (Z_to_bv 64 8) (o + 16 + 8 * Z.of_nat L - 8)). reflexivity.
      cbn [BL.zalu]. rewrite ATOP, BGU.unsigned_lit by lia. unfold BL.MM. rewrite Z.mod_small by lia. f_equal. lia.
    - rewrite (BGU.out_reg PI.regs_out E' R' 17 Hregs) by lia. change (nth 17 PI.regs_out (ELit 0)) with (EVar 36). cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U36.
    - exact (proj1 RX). - exact (proj2 RX).
    - eapply BGU.u64_at_frame. lia. lia. intros k Hk; apply MM. exact O8.
    - eapply BGU.u64_at_frame. lia. lia. intros k Hk; apply MM. exact HX. }
  split. exact MM. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma KS_regs_preserved R R' : (forall x, In x KS -> getr R' (reg x) = getr R (reg x)) -> regs_preserved R R'.
Proof.
  intros K r Hr. rewrite <- (AX2S.ridx_roundtrip r). apply K.
  unfold callee_saved_idx in Hr. unfold AX2.ridx. set (z := bv_unsigned r) in *. cbn in Hr.
  repeat (destruct Hr as [Hr|Hr]; [rewrite <- Hr; cbn; tauto|]). destruct Hr.
Qed.
Lemma KS_trans R R' R'' : (forall x, In x KS -> getr R' (reg x) = getr R (reg x)) -> (forall x, In x KS -> getr R'' (reg x) = getr R' (reg x)) ->
  forall x, In x KS -> getr R'' (reg x) = getr R (reg x).
Proof. intros A B x Hx. rewrite (B x Hx). apply A. exact Hx. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rloop (L : nat) : forall fx R M (o fb d cap r : Z) (ws : list Z),
  frame_ok M o fb d cap ->
  (forall i, (i < length ws)%nat -> BGU.u64_at M (d + 8 * Z.of_nat i) (L5W.nth_w ws i)) -> L5W.words_ok ws -> (L <= length ws)%nat -> Z.of_nat (length ws) <= cap ->
  at_test R M o fb d (L5W.nth_w ws (L - 1)) L -> (1 <= L)%nat -> Z.of_nat L <= cap ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  exists fx' R' M' (n' : nat),
    msteps RSEGS (st fx R 0x21b2c M) (st fx' R' r M')
    /\ (forall x, In x KS -> getr R' (reg x) = getr R (reg x))
    /\ (n' <= L)%nat
    /\ BGU.u64_at M' (o + 8) (Z.of_nat n')
    /\ BGU.u8_at M' o (if Nat.eqb n' 0 then Z.land fb 253 else fb)
    /\ ((1 <= n')%nat -> L5W.nth_w ws (n' - 1) <> 0)
    /\ (forall i : nat, (n' <= i < L)%nat -> L5W.nth_w ws i = 0)
    /\ (forall a : word, ~ (o <= bv_unsigned a < o + 16) -> M' a = M a)
    /\ mem_grows M M'.
Proof.
  induction L as [|L IH]; intros fx R M o fb d cap r ws FR WS WO WL WC AT HL HLc H1 [Hr Hre]. lia.
  pose proof FR as [Fo Fw [Ffb Fu8] Fd Fdef Fap].
  destruct AT as (A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & RX & O8 & OX).
  replace (S L - 1)%nat with L in * by lia.
  destruct (Z.eq_dec (L5W.nth_w ws L) 0) as [X0 | XNZ].
  - (* [comment removed for export] *)
    pose proof (br219f4_ft fx M R ltac:(rewrite A17, X0; reflexivity)) as Mb.
    destruct (Nat.eq_dec L 0) as [L0 | Lpos].
    + (* [comment removed for export] *)
      subst L.
      destruct (popz_conc fx R M o fb d cap FR A10 A11 A12 ltac:(rewrite A13; f_equal; lia) A14 A15 ltac:(rewrite A16; f_equal; lia)) as (fx2 & R2 & M2 & MS2 & K2 & Z0 & Z8 & Fr2 & Gr2).
      pose proof (BDU.ret_21ab0 fx2 R2 M2 r ltac:(rewrite K2 by (cbn; tauto); exact H1) Hr Hre) as MS3.
      exists fx2, R2, M2, 0%nat.
      split. { eapply msteps_trans. exact Mb. eapply msteps_trans. exact MS2. exact MS3. }
      split. exact K2. split. lia. split. exact Z8. split. exact Z0. split. intros; lia.
      split. { intros i Hi. replace i with 0%nat by lia. exact X0. }
      split. exact Fr2. exact Gr2.
    + (* [comment removed for export] *)
      set (X' := L5W.nth_w ws (L - 1)).
      assert (OX' : BGU.u64_at M (d + 8 * Z.of_nat (S L) - 16) X').
      { replace (d + 8 * Z.of_nat (S L) - 16) with (d + 8 * Z.of_nat (L - 1)) by lia. apply WS. lia. }
      assert (RX' : 0 <= X' < 2 ^ 64) by (apply L5W.words_ok_nth; exact WO).
      destruct (pop_conc fx R M o fb d cap X' (S L) FR A10 A12 A13 A14 A15 A16 ltac:(lia) HLc OX' RX') as (fx2 & R2 & M2 & MS2 & K2 & B12 & B13 & B14 & B15 & B16 & B17 & P8 & Fr2 & Gr2).
      assert (FR2: frame_ok M2 o fb d cap) by (eapply frame_ok_keep; eauto).
      assert (WS2: forall i, (i < length ws)%nat -> BGU.u64_at M2 (d + 8 * Z.of_nat i) (L5W.nth_w ws i)).
      { intros i Hi. eapply BGU.u64_at_frame. lia. lia. intros k Hk. apply Fr2. rewrite BGU.unsigned_lit by lia. lia. apply WS. exact Hi. }
      destruct (IH fx2 R2 M2 o fb d cap r ws FR2 WS2 WO ltac:(lia) WC) as (fx' & R' & M' & n' & MS & K & Hn' & Q8 & Q0 & TOP & ZER & Fr & Gr).
      { unfold at_test. subst X'. repeat split.
        - rewrite K2 by (cbn; tauto). exact A10. - rewrite K2 by (cbn; tauto). exact A11.
        - exact B12. - rewrite B13. f_equal. lia. - exact B14. - exact B15. - rewrite B16. f_equal. lia. - exact B17. - lia. - lia.
        - replace (Z.of_nat L) with (Z.of_nat (S L) - 1) by lia. exact P8.
        - replace (d + 8 * Z.of_nat L - 8) with (d + 8 * Z.of_nat (L - 1)) by lia. apply WS2. lia. }
      lia. lia. rewrite K2 by (cbn; tauto). exact H1. split; assumption.
      exists fx', R', M', n'.
      split. { eapply msteps_trans. exact Mb. eapply msteps_trans. exact MS2. exact MS. }
      split. { eapply KS_trans. 2: exact K. intros x Hx. apply K2. right. exact Hx. }
      split. lia. split. exact Q8. split. exact Q0. split. exact TOP.
      split. { intros i Hi. destruct (Nat.eq_dec i L) as [->|NE]. exact X0. apply ZER. lia. }
      split. { intros a Ha. rewrite (Fr a Ha). apply Fr2. lia. } eapply mem_grows_trans; eauto.
  - (* [comment removed for export] *)
    pose proof (br219f4_tk fx M R ltac:(rewrite A17; apply BIU.lit_nonzero; lia)) as Mb.
    destruct (keep_conc fx R M (S L) A13 ltac:(lia) ltac:(lia)) as (fx2 & R2 & M2 & MS2 & K2 & MM2 & Gr2).
    pose proof (BDU.ret_21aa4 fx2 R2 M2 r ltac:(rewrite K2 by (cbn; tauto); exact H1) Hr Hre) as MS3.
    exists fx2, R2, M2, (S L).
    split. { eapply msteps_trans. exact Mb. eapply msteps_trans. exact MS2. exact MS3. }
    split. exact K2. split. lia.
    split. { eapply BGU.u64_at_frame. lia. lia. intros k Hk; apply MM2. exact O8. }
    split. { cbn [Nat.eqb]. replace o with (o + 0) by lia. eapply BGU.u8_at_frame. apply MM2. rewrite Z.add_0_r. exact Fu8. }
    split. { intros _. replace (S L - 1)%nat with L by lia. exact XNZ. }
    split. { intros; lia. }
    split. { intros a _. apply MM2. } exact Gr2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma testbit0_land253 fb : Z.testbit (Z.land fb 253) 0 = Z.testbit fb 0.
Proof. rewrite Z.land_spec. change (Z.testbit 253 0) with true. apply Bool.andb_true_r. Qed.

Theorem reduce_run (fx : FPState) R M (o r : Z) (b : L5.bigobj) (ws : list Z) :
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  L5.big_at RSEGS M o b -> o mod 8 = 0 -> 2 ^ 20 <= o -> o + 32 <= 2 ^ 47 -> L5.writable RSEGS M o 16 ->
  L5.defined M (L5.bo_data o b) (8 * L5.bo_cap b) ->
  L5.limbs_at RSEGS M (L5.bo_data o b) ws -> length ws = L5.bo_len b -> L5W.words_ok ws ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> q + 8 * cap <= o \/ o + 32 <= q) ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R REDUCE M) (st fx' R' r M') /\ reduce_post M M' o b ws R R'.
Proof.
  intros H10 H1 Hra OB A8 OLO OHI OW DEF WS WL WO AP. unfold REDUCE.
  destruct b as [fb len sto]. unfold L5.big_at in OB. cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data L5.bo_cap] in *.
  destruct OB as (O0 & Ffb & O8 & OST).
  set (d := match sto with L5.BInl _ _ => o + 16 | L5.BDyn _ q => q end) in *.
  assert (WS' : forall i, (i < length ws)%nat -> BGU.u64_at M (d + 8 * Z.of_nat i) (L5W.nth_w ws i)).
  { intros i Hi. exact (WS i Hi). }
  (* [comment removed for export] *)
  assert (PACK : forall (fx' : FPState) R' M' (n' : nat),
    (forall x, In x KS -> getr R' (reg x) = getr R (reg x)) -> (n' <= len)%nat ->
    BGU.u64_at M' (o + 8) (Z.of_nat n') -> BGU.u8_at M' o (if Nat.eqb n' 0 then Z.land fb 253 else fb) ->
    ((1 <= n')%nat -> L5W.nth_w ws (n' - 1) <> 0) ->
    (forall i : nat, (n' <= i < len)%nat -> L5W.nth_w ws i = 0) ->
    (forall a : word, ~ (o <= bv_unsigned a < o + 16) -> M' a = M a) -> mem_grows M M' ->
    reduce_post M M' o (L5.BO fb len sto) ws R R').
  { intros fx' R' M' n' K Hn Q8 Q0 TOP ZER Fr Gr.
    assert (RL: L5W.rlen ws = n').
    { apply L5W.rlen_charact. lia. intros i Hi. apply ZER. lia. destruct (Nat.eq_dec n' 0). left; exact e. right. apply TOP. lia. }
    unfold reduce_post. cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data]. rewrite RL.
    split. { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact Q0.
             split. { destruct (Nat.eqb n' 0). apply L5.land_byte_range; lia. exact Ffb. }
             split. exact Q8.
             destruct sto as [v0 v1 | cap q].
             - destruct OST as (B0 & O16 & O24 & Hl2 & Rv0 & Rv1). repeat split; try lia.
               + destruct (Nat.eqb n' 0); [rewrite testbit0_land253|]; exact B0.
               + eapply (BGU.u64_keep M M'). exact Fr. lia. lia. lia. exact O16.
               + eapply (BGU.u64_keep M M'). exact Fr. lia. lia. lia. exact O24.
             - destruct OST as (B0 & O16 & O24 & Hlc & Hcap & Aq & QLO & QHI & HAP). repeat split; try lia.
               + destruct (Nat.eqb n' 0); [rewrite testbit0_land253|]; exact B0.
               + eapply (BGU.u64_keep M M'). exact Fr. lia. lia. lia. exact O16.
               + eapply (BGU.u64_keep M M'). exact Fr. lia. lia. lia. exact O24.
               + exact HAP. }
    split. { apply KS_regs_preserved. exact K. }
    split. { rewrite BDU.rl10. rewrite (K 10%nat) by (cbn; tauto). exact H10. }
    split. { intros x Hx. apply Fr. intros Hin. apply (Hx (o, 16)). left; reflexivity. exact Hin. }
    exact Gr. }
  destruct (Nat.eq_dec len 0) as [L0 | Lpos].
  - (* [comment removed for export] *)
    rewrite L0 in *.
    destruct (rd0_conc fx R M o fb H10 OLO OHI A8 OW Ffb O0 O8) as (fx2 & R2 & M2 & MS2 & K2 & Z0 & Fr2 & Gr2).
    pose proof (BDU.ret_21ab0 fx2 R2 M2 r ltac:(rewrite K2 by (cbn; tauto); exact H1) (proj1 Hra) (proj2 Hra)) as MS3.
    exists fx2, R2, M2. split. { eapply msteps_trans. exact MS2. exact MS3. }
    apply (PACK fx2 R2 M2 0%nat K2 ltac:(lia)).
    + eapply BGU.u64_at_frame. lia. lia. intros k Hk. apply Fr2. rewrite BGU.unsigned_lit by lia. lia. exact O8.
    + exact Z0.
    + intros; lia.
    + intros; lia.
    + intros a Ha; apply Fr2; lia. + exact Gr2.
  - assert (OX: BGU.u64_at M (d + 8 * Z.of_nat len - 8) (L5W.nth_w ws (len - 1))).
    { replace (d + 8 * Z.of_nat len - 8) with (d + 8 * Z.of_nat (len - 1)) by lia. apply WS'. lia. }
    assert (RX: 0 <= L5W.nth_w ws (len - 1) < 2 ^ 64) by (apply L5W.words_ok_nth; exact WO).
    destruct sto as [v0 v1 | cap q].
    + (* [comment removed for export] *)
      destruct OST as (B0 & O16 & O24 & Hl2 & Rv0 & Rv1). subst d.
      assert (FR: frame_ok M o fb (o + 16) 2).
      { constructor. lia. exact OW. split; [lia|exact O0].
        (repeat split; try lia); try (replace (o + 16) with (o + 2 * 8) by lia; rewrite Z_mod_plus_full; exact A8). exact DEF. lia. }
      destruct (rdAi_conc fx R M o fb 2 (L5W.nth_w ws (len - 1)) len FR B0 H10 ltac:(lia) O8 ltac:(replace (o + 16 + 8 * Z.of_nat len - 8) with (o + 16 + 8 * Z.of_nat (len - 1)) by lia; apply WS'; lia) RX)
        as (fx1 & R1 & M1 & MS1 & K1 & AT1 & MM1 & Gr1).
      assert (FR1: frame_ok M1 o fb (o + 16) 2). { eapply frame_ok_keep. exact FR. exact Gr1. intros a _; apply MM1. }
      assert (WS1: forall i, (i < length ws)%nat -> BGU.u64_at M1 (o + 16 + 8 * Z.of_nat i) (L5W.nth_w ws i)).
      { intros i Hi. eapply BGU.u64_at_frame. lia. lia. intros k Hk; apply MM1. apply WS'. exact Hi. }
      destruct (rloop len fx1 R1 M1 o fb (o + 16) 2 r ws FR1 WS1 WO ltac:(lia) ltac:(lia) AT1 ltac:(lia) ltac:(lia) ltac:(rewrite K1 by (cbn; tauto); exact H1) Hra)
        as (fx' & R' & M' & n' & MS & K & Hn' & Q8 & Q0 & TOP & ZER & Fr & Gr).
      exists fx', R', M'. split. { eapply msteps_trans. exact MS1. exact MS. }
      apply (PACK fx' R' M' n' (KS_trans _ _ _ K1 K) Hn' Q8 Q0 TOP ZER).
      { intros a Ha. rewrite (Fr a Ha). apply MM1. } { eapply mem_grows_trans; eauto. }
    + (* [comment removed for export] *)
      destruct OST as (B0 & O16 & O24 & Hlc & Hcap & Aq & QLO & QHI). subst d.
      assert (FR: frame_ok M o fb q cap).
      { constructor. lia. exact OW. split; [lia|exact O0]. lia. exact DEF. destruct (AP cap q eq_refl); lia. }
      destruct (rdAd_conc fx R M o fb q cap (L5W.nth_w ws (len - 1)) len FR B0 H10 ltac:(lia) Hlc O8 O24 OX RX) as (fx1 & R1 & M1 & MS1 & K1 & AT1 & MM1 & Gr1).
      assert (FR1: frame_ok M1 o fb q cap). { eapply frame_ok_keep. exact FR. exact Gr1. intros a _; apply MM1. }
      assert (WS1: forall i, (i < length ws)%nat -> BGU.u64_at M1 (q + 8 * Z.of_nat i) (L5W.nth_w ws i)).
      { intros i Hi. eapply BGU.u64_at_frame. lia. lia. intros k Hk; apply MM1. apply WS'. exact Hi. }
      destruct (rloop len fx1 R1 M1 o fb q cap r ws FR1 WS1 WO ltac:(lia) ltac:(lia) AT1 ltac:(lia) Hlc ltac:(rewrite K1 by (cbn; tauto); exact H1) Hra)
        as (fx' & R' & M' & n' & MS & K & Hn' & Q8 & Q0 & TOP & ZER & Fr & Gr).
      exists fx', R', M'. split. { eapply msteps_trans. exact MS1. exact MS. }
      apply (PACK fx' R' M' n' (KS_trans _ _ _ K1 K) Hn' Q8 Q0 TOP ZER).
      { intros a Ha. rewrite (Fr a Ha). apply MM1. } { eapply mem_grows_trans; eauto. }
Qed.

(* [comment removed for export] *)
Theorem reduce_ok : reduce_spec.
Proof.
  intros fx R M model K o r b ws Hh Hl H10 H1 Hra OB A8 OLO OHI OW DEF WS WL WO AP HK.
  unfold cfg. eapply (L5.run_cps RSEGS (fun _ R' M' => reduce_post M M' o b ws R R')). exact Hh. exact Hl.
  - rewrite BDU.rl10 in H10. rewrite BDU.rl1 in H1. exact (reduce_run fx R M o r b ws H10 H1 Hra OB A8 OLO OHI OW DEF WS WL WO AP).
  - intros fx' R' M' HP. apply HK. exact HP.
Qed.
End SCFG_1.


End L5REDGU.
