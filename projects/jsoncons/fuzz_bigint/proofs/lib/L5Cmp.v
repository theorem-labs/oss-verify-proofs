(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_21134_21d54 BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkDq BigLinkReduce L5Defs L5Kn
     L5Core L5Words.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsOps.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5Cmp.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5CMP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Module PAii := LibSegZ_cmAii. Module PAid := LibSegZ_cmAid. Module PAdi := LibSegZ_cmAdi. Module PAdd := LibSegZ_cmAdd.
Module PN := LibSegZ_cmN. Module PP := LibSegZ_cmP. Module PE := LibSegZ_cmE. Module PI := LibSegZ_cmI. Module PJ := LibSegZ_cmJ. Module PZ := LibSegZ_cmZ.
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition CMP : Z := 0x21a7c.
Definition SZBR : Z := 0x21ae0. Definition SZBR2 : Z := 0x21ae4. Definition PLUS : Z := 0x21ae8. Definition EQSET : Z := 0x21af4.
Definition LHEAD : Z := 0x21b08. Definition WBR : Z := 0x21b18. Definition WNEXT : Z := 0x21b1c. Definition WBR2 : Z := 0x21b24.
Definition MINUS : Z := 0x21b28. Definition RET : Z := 0x21b2c.
Definition MAXW : Z := 18446744073709551615.
End SCFG_1.


Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Section SCFG_2.
Context {SCFG_P : ScfgP}.

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cmp_kept : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
Definition cmp_obj (M : word -> option byte) (o : Z) (b : L5.bigobj) : Prop :=
  L5.big_at RSEGS M o b /\ Z.testbit (L5.bo_fb b) 1 = false /\ (1 <= L5.bo_len b)%nat /\ Z.of_nat (L5.bo_len b) <= 300 /\
  o mod 8 = 0 /\ 4096 <= o /\ o + 32 <= 2 ^ 47 /\
  4096 <= L5.bo_data o b /\ L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b) <= 2 ^ 47 /\
  L5.defined M (L5.bo_data o b) (8 * Z.of_nat (L5.bo_len b)).

(* [comment removed for export] *)
Definition res_sized (c : Z) (nx ny : nat) : Prop := (c = 0 \/ c = 1 \/ c = MAXW) /\ ((nx < ny)%nat -> c = MAXW) /\ ((ny < nx)%nat -> c = 1).
Definition cmp_val (wx wy : list Z) : Z :=
  if BigFactsBase.val wx <? BigFactsBase.val wy then MAXW else if BigFactsBase.val wy <? BigFactsBase.val wx then 1 else 0.
Lemma cmp_val_cases wx wy : cmp_val wx wy = 0 \/ cmp_val wx wy = 1 \/ cmp_val wx wy = MAXW.
Proof. unfold cmp_val. destruct (_ <? _); [|destruct (_ <? _)]; tauto. Qed.
Lemma cmp_val_lt wx wy : cmp_val wx wy = MAXW <-> BigFactsBase.val wx < BigFactsBase.val wy.
Proof. unfold cmp_val, MAXW. destruct (Z.ltb_spec (BigFactsBase.val wx) (BigFactsBase.val wy)); [|destruct (Z.ltb_spec (BigFactsBase.val wy) (BigFactsBase.val wx))]; split; intros; lia. Qed.
Lemma cmp_val_gt wx wy : cmp_val wx wy = 1 <-> BigFactsBase.val wy < BigFactsBase.val wx.
Proof. unfold cmp_val, MAXW. destruct (Z.ltb_spec (BigFactsBase.val wx) (BigFactsBase.val wy)); [|destruct (Z.ltb_spec (BigFactsBase.val wy) (BigFactsBase.val wx))]; split; intros; lia. Qed.
Lemma cmp_val_eq wx wy : cmp_val wx wy = 0 <-> BigFactsBase.val wx = BigFactsBase.val wy.
Proof. unfold cmp_val, MAXW. destruct (Z.ltb_spec (BigFactsBase.val wx) (BigFactsBase.val wy)); [|destruct (Z.ltb_spec (BigFactsBase.val wy) (BigFactsBase.val wx))]; split; intros; lia. Qed.

Definition cmp_post (M M' : word -> option byte) (R R' : bvmap 5 word) (nx ny : nat) (wx wy : list Z) : Prop :=
  (forall i, In i cmp_kept -> getr R' (reg i) = getr R (reg i)) /\ regs_preserved R R'
  /\ (exists c, getr R' (reg 10) = Z_to_bv 64 c /\ res_sized c nx ny /\ (nx = ny -> c = cmp_val wx wy))
  /\ (forall a, M' a = M a) /\ mem_grows M M'.

Definition cmp_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (xo yo r : Z) (bx by_ : L5.bigobj)
         (wx wy : list Z),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr R 10%bv = Z_to_bv 64 xo -> getr R 11%bv = Z_to_bv 64 yo -> getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    cmp_obj M xo bx -> cmp_obj M yo by_ -> L5C.obj_limbs RSEGS M bx wx -> L5C.obj_limbs RSEGS M by_ wy ->
    (forall (fx' : FPState) R' M', cmp_post M M' R R' (L5.bo_len bx) (L5.bo_len by_) wx wy -> srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model) K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx) R CMP M model) K.

(* [comment removed for export] *)
Lemma obj_limbs_data M o b ws : L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws ->
  L5.limbs_at RSEGS M (L5.bo_data o b) ws /\ length ws = L5.bo_len b /\ L5W.words_ok ws.
Proof.
  intros B (Ln & F & S). split; [|split; [exact Ln|exact F]]. unfold L5.big_at in B.
  destruct b as [fb n [v0 v1|cap q]]; cbn [L5.bo_st L5.bo_len L5.bo_data L5.bo_fb] in *.
  - destruct B as (_ & _ & _ & _ & U16 & U24 & Hn & _). subst ws.
    destruct n as [|[|[|n]]]; [apply (L5C.limbs_at_nil RSEGS)| | |exfalso; lia]; cbn [firstn]; intros i Hi; cbn [length] in Hi.
    + destruct i; [|exfalso; lia]. cbn [nth]. replace (o + 16 + 8 * Z.of_nat 0) with (o + 16) by lia. exact U16.
    + destruct i as [|[|i]]; [| |exfalso; lia]; cbn [nth].
      replace (o + 16 + 8 * Z.of_nat 0) with (o + 16) by lia. exact U16.
      replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) by lia. exact U24.
  - exact S.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rl14 : (14%bv : bv 5) = reg 14. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl15 : (15%bv : bv 5) = reg 15. Proof. apply bv_eq. reflexivity. Qed.
Lemma br_219a8 fx R M : msteps RSEGS (st fx R 0x21ae0 M) (st fx R (if branch_taken BC_LTU (getr R (reg 14)) (getr R (reg 15)) then 0x21b28 else 0x21ae4) M).
Proof. rewrite <- rl14, <- rl15. apply (@BDQ.br_site fx M R 0x21ae0 0x21b28 (0x21ae0%bv : word) _ BC_LTU 14 15 _ eq_refl F_21ae0 eq_refl D_21ae0). reflexivity. Qed.
Lemma br_219ac fx R M : msteps RSEGS (st fx R 0x21ae4 M) (st fx R (if branch_taken BC_GEU (getr R (reg 15)) (getr R (reg 14)) then 0x21af4 else 0x21ae8) M).
Proof. rewrite <- rl14, <- rl15. apply (@BDQ.br_site fx M R 0x21ae4 0x21af4 (0x21ae4%bv : word) _ BC_GEU 15 14 _ eq_refl F_21ae4 eq_refl D_21ae4). reflexivity. Qed.
Lemma br_219e0 fx R M : msteps RSEGS (st fx R 0x21b18 M) (st fx R (if branch_taken BC_LTU (getr R (reg 15)) (getr R (reg 14)) then 0x21ae8 else 0x21b1c) M).
Proof. rewrite <- rl14, <- rl15. apply (@BDQ.br_site fx M R 0x21b18 0x21ae8 (0x21b18%bv : word) _ BC_LTU 15 14 _ eq_refl F_21b18 eq_refl D_21b18). reflexivity. Qed.
Lemma br_219ec fx R M : msteps RSEGS (st fx R 0x21b24 M) (st fx R (if branch_taken BC_GEU (getr R (reg 14)) (getr R (reg 15)) then 0x21b08 else 0x21b28) M).
Proof. rewrite <- rl14, <- rl15. apply (@BDQ.br_site fx M R 0x21b24 0x21b08 (0x21b24%bv : word) _ BC_GEU 14 15 _ eq_refl F_21b24 eq_refl D_21b24). reflexivity. Qed.
Lemma ret_219f4 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R 0x21b2c M) (st fx R r M).
Proof. intros H1 Hr He. apply (BRED.ret_to fx R M 0x21b2c W_21b2c r F_21b2c eq_refl D_21b2c H1 Hr He). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition VAL (R : bvmap 5 word) (xo yo nx ny xd yd fbx fby k xk yk : Z) (i : nat) : word :=
  match i with
  | 33%nat => Z_to_bv 64 xo | 34%nat => Z_to_bv 64 yo | 35%nat => Z_to_bv 64 nx | 36%nat => Z_to_bv 64 ny
  | 37%nat => Z_to_bv 64 xd | 38%nat => Z_to_bv 64 yd | 39%nat => Z_to_bv 64 fbx | 40%nat => Z_to_bv 64 fby | 41%nat => Z_to_bv 64 k
  | 42%nat => Z_to_bv 64 xk | 43%nat => Z_to_bv 64 yk
  | _ => getr R (reg i)
  end.
Definition VZ (R : bvmap 5 word) (xo yo nx ny xd yd fbx fby k xk yk : Z) (i : nat) : Z :=
  match i with
  | 33%nat => xo | 34%nat => yo | 35%nat => nx | 36%nat => ny | 37%nat => xd | 38%nat => yd | 39%nat => fbx | 40%nat => fby | 41%nat => k
  | 42%nat => xk | 43%nat => yk
  | _ => bv_unsigned (getr R (reg i))
  end.
Lemma VAL_VZ R xo yo nx ny xd yd fbx fby k xk yk :
  0 <= xo < 2 ^ 64 -> 0 <= yo < 2 ^ 64 -> 0 <= nx < 2 ^ 64 -> 0 <= ny < 2 ^ 64 -> 0 <= xd < 2 ^ 64 -> 0 <= yd < 2 ^ 64 ->
  0 <= fbx < 256 -> 0 <= fby < 256 -> 0 <= k < 2 ^ 64 -> 0 <= xk < 2 ^ 64 -> 0 <= yk < 2 ^ 64 ->
  forall i, bv_unsigned (ev (Env (VAL R xo yo nx ny xd yd fbx fby k xk yk) (fun _ => [])) i) = VZ R xo yo nx ny xd yd fbx fby k xk yk i.
Proof.
  intros until i. cbn [ev]. unfold VAL, VZ.
  repeat (lazymatch goal with
          | |- bv_unsigned (match i with _ => _ end) = _ => destruct i as [|i]
          | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.

(* [comment removed for export] *)
Local Ltac run_piece P ZA HR HK :=
  let X := fresh in
  destruct (P _ _ _ _ HR HK ltac:(constructor)) as (?fx' & ?E' & ?R' & ?M' & ?k & ?ps & ?Hnth & ?Hag & ?Hms & ?Hregs & ?Hx0 & ?Hrok & ?Hfr & ?Hcells & ?Hgr).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KSA : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Lemma KSAii_ok : BG.kept_ok 48 PAii.regs0 PAii.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSAid_ok : BG.kept_ok 48 PAid.regs0 PAid.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSAdi_ok : BG.kept_ok 48 PAdi.regs0 PAdi.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSAdd_ok : BG.kept_ok 48 PAdd.regs0 PAdd.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.

Definition at_szbr (R : bvmap 5 word) (xd yd nx ny : Z) : Prop :=
  getr R (reg 10) = Z_to_bv 64 MAXW /\ getr R (reg 11) = Z_to_bv 64 0 /\ getr R (reg 12) = Z_to_bv 64 xd /\
  getr R (reg 14) = Z_to_bv 64 nx /\ getr R (reg 15) = Z_to_bv 64 ny /\ getr R (reg 16) = Z_to_bv 64 yd.

Local Ltac intro_obj OX Hd :=
  let B := fresh in
  destruct OX as (B & ?Xs1 & ?Xl1 & ?Xl2 & ?Xa8 & ?Xlo & ?Xhi & ?Xdlo & ?Xdhi & Hd);
  unfold L5.big_at in B; cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data] in *.

Lemma cmA_conc fx R M (xo yo : Z) (bx by_ : L5.bigobj) :
  cmp_obj M xo bx -> cmp_obj M yo by_ ->
  getr R (reg 10) = Z_to_bv 64 xo -> getr R (reg 11) = Z_to_bv 64 yo ->
  exists fx' R' M', msteps RSEGS (st fx R CMP M) (st fx' R' SZBR M')
    /\ (forall x, In x KSA -> getr R' (reg x) = getr R (reg x))
    /\ at_szbr R' (L5.bo_data xo bx) (L5.bo_data yo by_) (Z.of_nat (L5.bo_len bx)) (Z.of_nat (L5.bo_len by_))
    /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  intros OX OY H10 H11.
  destruct bx as [fbx nx [xv0 xv1 | xcap xq]]; destruct by_ as [fby ny [yv0 yv1 | ycap yq]];
    intro_obj OX Xd; intro_obj OY Yd;
    destruct H as (X0 & Xfb & X8 & Xb0 & X16 & X24 & XR); destruct H0 as (Y0 & Yfb & Y8 & Yb0 & Y16 & Y24 & YR).
  - set (Vf := VAL R xo yo (Z.of_nat nx) (Z.of_nat ny) (xo + 16) (yo + 16) fbx fby 0 0 0). set (E := Env Vf (fun _ => [])).
    assert (ZA : forall i, bv_unsigned (ev E i) = VZ R xo yo (Z.of_nat nx) (Z.of_nat ny) (xo + 16) (yo + 16) fbx fby 0 0 0 i) by (apply VAL_VZ; lia). unfold VZ in ZA.
    assert (HR: regs_ok E PAii.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAii.regs0 nth]. repeat split; L5K.slot ZA. }
    assert (HK: know_ok RSEGS E M PAii.kn0). { unfold know_ok, PAii.kn0. L5K.kn_all ZA. }
    destruct (PAii.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply L5K.nth_error_single in Hnth. subst ps. change PAii.NX0 with 48%nat in Hag.
    exists fx', R', M'. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PAii.regs0 PAii.regs_out0 48 KSA KSAii_ok HR Hag Hregs j Hj). }
    split. { unfold at_szbr, MAXW. repeat split; rewrite (BG.out_reg PAii.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAii.regs_out0]; L5K.wordE' ZA Hag. }
    split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
  - set (Vf := VAL R xo yo (Z.of_nat nx) (Z.of_nat ny) (xo + 16) yq fbx fby 0 0 0). set (E := Env Vf (fun _ => [])).
    assert (ZA : forall i, bv_unsigned (ev E i) = VZ R xo yo (Z.of_nat nx) (Z.of_nat ny) (xo + 16) yq fbx fby 0 0 0 i) by (apply VAL_VZ; lia). unfold VZ in ZA.
    assert (HR: regs_ok E PAid.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAid.regs0 nth]. repeat split; L5K.slot ZA. }
    assert (HK: know_ok RSEGS E M PAid.kn0). { unfold know_ok, PAid.kn0. L5K.kn_all ZA. }
    destruct (PAid.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply L5K.nth_error_single in Hnth. subst ps. change PAid.NX0 with 48%nat in Hag.
    exists fx', R', M'. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PAid.regs0 PAid.regs_out0 48 KSA KSAid_ok HR Hag Hregs j Hj). }
    split. { unfold at_szbr, MAXW. repeat split; rewrite (BG.out_reg PAid.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAid.regs_out0]; L5K.wordE' ZA Hag. }
    split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
  - set (Vf := VAL R xo yo (Z.of_nat nx) (Z.of_nat ny) xq (yo + 16) fbx fby 0 0 0). set (E := Env Vf (fun _ => [])).
    assert (ZA : forall i, bv_unsigned (ev E i) = VZ R xo yo (Z.of_nat nx) (Z.of_nat ny) xq (yo + 16) fbx fby 0 0 0 i) by (apply VAL_VZ; lia). unfold VZ in ZA.
    assert (HR: regs_ok E PAdi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAdi.regs0 nth]. repeat split; L5K.slot ZA. }
    assert (HK: know_ok RSEGS E M PAdi.kn0). { unfold know_ok, PAdi.kn0. L5K.kn_all ZA. }
    destruct (PAdi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply L5K.nth_error_single in Hnth. subst ps. change PAdi.NX0 with 48%nat in Hag.
    exists fx', R', M'. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PAdi.regs0 PAdi.regs_out0 48 KSA KSAdi_ok HR Hag Hregs j Hj). }
    split. { unfold at_szbr, MAXW. repeat split; rewrite (BG.out_reg PAdi.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAdi.regs_out0]; L5K.wordE' ZA Hag. }
    split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
  - set (Vf := VAL R xo yo (Z.of_nat nx) (Z.of_nat ny) xq yq fbx fby 0 0 0). set (E := Env Vf (fun _ => [])).
    assert (ZA : forall i, bv_unsigned (ev E i) = VZ R xo yo (Z.of_nat nx) (Z.of_nat ny) xq yq fbx fby 0 0 0 i) by (apply VAL_VZ; lia). unfold VZ in ZA.
    assert (HR: regs_ok E PAdd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAdd.regs0 nth]. repeat split; L5K.slot ZA. }
    assert (HK: know_ok RSEGS E M PAdd.kn0). { unfold know_ok, PAdd.kn0. L5K.kn_all ZA. }
    destruct (PAdd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply L5K.nth_error_single in Hnth. subst ps. change PAdd.NX0 with 48%nat in Hag.
    exists fx', R', M'. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PAdd.regs0 PAdd.regs_out0 48 KSA KSAdd_ok HR Hag Hregs j Hj). }
    split. { unfold at_szbr, MAXW. repeat split; rewrite (BG.out_reg PAdd.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAdd.regs_out0]; L5K.wordE' ZA Hag. }
    split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac piece_tail P KS KSOK HR Hag Hregs :=
  idtac.

Definition KSN : list nat := Eval vm_compute in (BG.kept_list 48 PN.regs0 PN.regs_out0).
Lemma KSN_ok : BG.kept_ok 48 PN.regs0 PN.regs_out0 KSN = true. Proof. vm_compute. reflexivity. Qed.
Definition KSP : list nat := Eval vm_compute in (BG.kept_list 48 PP.regs0 PP.regs_out0).
Lemma KSP_ok : BG.kept_ok 48 PP.regs0 PP.regs_out0 KSP = true. Proof. vm_compute. reflexivity. Qed.
Definition KSE : list nat := Eval vm_compute in (BG.kept_list 48 PE.regs0 PE.regs_out0).
Lemma KSE_ok : BG.kept_ok 48 PE.regs0 PE.regs_out0 KSE = true. Proof. vm_compute. reflexivity. Qed.
Definition KSI : list nat := Eval vm_compute in (BG.kept_list 48 PI.regs0 PI.regs_out0).
Lemma KSI_ok : BG.kept_ok 48 PI.regs0 PI.regs_out0 KSI = true. Proof. vm_compute. reflexivity. Qed.
Definition KSJ : list nat := Eval vm_compute in (BG.kept_list 48 PJ.regs0 PJ.regs_out0).
Lemma KSJ_ok : BG.kept_ok 48 PJ.regs0 PJ.regs_out0 KSJ = true. Proof. vm_compute. reflexivity. Qed.
Definition KSZ : list nat := Eval vm_compute in (BG.kept_list 48 PZ.regs0 PZ.regs_out0).
Lemma KSZ_ok : BG.kept_ok 48 PZ.regs0 PZ.regs_out0 KSZ = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cmN_conc fx R M : getr R (reg 11) = Z_to_bv 64 0 ->
  exists fx' R' M', msteps RSEGS (st fx R MINUS M) (st fx' R' RET M')
    /\ (forall x, In x KSN -> getr R' (reg x) = getr R (reg x)) /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  intros H11.
  set (Vf := VAL R 0 0 0 0 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R 0 0 0 0 0 0 0 0 0 0 0 i) by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PN.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PN.kn0). { unfold know_ok, PN.kn0. apply Forall_nil. }
  destruct (PN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PN.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PN.regs0 PN.regs_out0 48 KSN KSN_ok HR Hag Hregs j Hj). }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma cmP_conc fx R M : getr R (reg 11) = Z_to_bv 64 0 ->
  exists fx' R' M', msteps RSEGS (st fx R PLUS M) (st fx' R' RET M')
    /\ (forall x, In x KSP -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 10) = Z_to_bv 64 1 /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  intros H11.
  set (Vf := VAL R 0 0 0 0 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R 0 0 0 0 0 0 0 0 0 0 0 i) by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PP.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PP.kn0). { unfold know_ok, PP.kn0. apply Forall_nil. }
  destruct (PP.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PP.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP.regs0 PP.regs_out0 48 KSP KSP_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PP.regs_out0 E' R' 10 Hregs) by lia. reflexivity. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Definition at_head (R : bvmap 5 word) (xd yd : Z) (k : nat) : Prop :=
  getr R (reg 11) = Z_to_bv 64 0 /\ getr R (reg 12) = Z_to_bv 64 (xd + 8 * Z.of_nat k - 8) /\
  getr R (reg 13) = Z_to_bv 64 (Z.of_nat k + 1) /\ getr R (reg 16) = Z_to_bv 64 (yd + 8 * Z.of_nat k - 8).

(* [comment removed for export] *)
Lemma cmE_conc fx R M (xd yd : Z) (n : nat) :
  getr R (reg 11) = Z_to_bv 64 0 -> getr R (reg 12) = Z_to_bv 64 xd -> getr R (reg 14) = Z_to_bv 64 (Z.of_nat n) ->
  getr R (reg 15) = Z_to_bv 64 (Z.of_nat n) -> getr R (reg 16) = Z_to_bv 64 yd ->
  (1 <= n)%nat -> Z.of_nat n <= 300 -> 4096 <= xd /\ xd + 8 * Z.of_nat n <= 2 ^ 47 -> 4096 <= yd /\ yd + 8 * Z.of_nat n <= 2 ^ 47 ->
  exists fx' R' M', msteps RSEGS (st fx R EQSET M) (st fx' R' LHEAD M')
    /\ (forall x, In x KSE -> getr R' (reg x) = getr R (reg x)) /\ at_head R' xd yd n /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  intros H11 H12 H14 H15 H16 Hn1 Hn2 Hx Hy.
  set (Vf := VAL R 0 0 (Z.of_nat n) (Z.of_nat n) xd yd 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R 0 0 (Z.of_nat n) (Z.of_nat n) xd yd 0 0 0 0 0 i) by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PE.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PE.kn0). { unfold know_ok, PE.kn0. L5K.kn_all ZA. }
  destruct (PE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PE.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PE.regs0 PE.regs_out0 48 KSE KSE_ok HR Hag Hregs j Hj). }
  split. { unfold at_head. repeat split; rewrite (BG.out_reg PE.regs_out0 E' R' _ Hregs) by lia; cbn [nth PE.regs_out0]; L5K.wordE' ZA Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma cmI_conc fx R M (xd yd : Z) (n k : nat) (xk yk : Z) :
  at_head R xd yd k -> (1 <= k <= n)%nat -> Z.of_nat n <= 300 ->
  4096 <= xd /\ xd + 8 * Z.of_nat n <= 2 ^ 47 -> 4096 <= yd /\ yd + 8 * Z.of_nat n <= 2 ^ 47 -> xd mod 8 = 0 -> yd mod 8 = 0 ->
  L5.u64_at RSEGS M (xd + 8 * (Z.of_nat k - 1)) xk -> L5.u64_at RSEGS M (yd + 8 * (Z.of_nat k - 1)) yk -> 0 <= xk < 2 ^ 64 -> 0 <= yk < 2 ^ 64 ->
  exists fx' R' M', msteps RSEGS (st fx R LHEAD M) (st fx' R' WBR M')
    /\ (forall x, In x KSI -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 13) = Z_to_bv 64 (Z.of_nat k)
    /\ (getr R' (reg 14) = Z_to_bv 64 xk /\ getr R' (reg 15) = Z_to_bv 64 yk)
    /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  intros (A11 & A12 & A13 & A16) Hk Hn Hx Hy Ax Ay Ux Uy Rx Ry.
  set (Vf := VAL R 0 0 (Z.of_nat n) (Z.of_nat n) xd yd 0 0 (Z.of_nat k) xk yk). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R 0 0 (Z.of_nat n) (Z.of_nat n) xd yd 0 0 (Z.of_nat k) xk yk i) by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PI.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PI.kn0). { unfold know_ok, PI.kn0. L5K.kn_all ZA. }
  destruct (PI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PI.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PI.regs0 PI.regs_out0 48 KSI KSI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PI.regs_out0 E' R' 13 Hregs) by lia; cbn [nth PI.regs_out0]; L5K.wordE' ZA Hag. }
  split. { split. rewrite (BG.out_reg PI.regs_out0 E' R' 14 Hregs) by lia; cbn [nth PI.regs_out0]; L5K.wordE' ZA Hag.
           rewrite (BG.out_reg PI.regs_out0 E' R' 15 Hregs) by lia; cbn [nth PI.regs_out0]; L5K.wordE' ZA Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma cmJ_conc fx R M (xd yd : Z) (k : nat) :
  getr R (reg 11) = Z_to_bv 64 0 -> getr R (reg 12) = Z_to_bv 64 (xd + 8 * Z.of_nat k - 8) -> getr R (reg 16) = Z_to_bv 64 (yd + 8 * Z.of_nat k - 8) ->
  (1 <= k)%nat -> Z.of_nat k <= 300 -> 4096 <= xd /\ xd + 8 * Z.of_nat k <= 2 ^ 47 -> 4096 <= yd /\ yd + 8 * Z.of_nat k <= 2 ^ 47 ->
  exists fx' R' M', msteps RSEGS (st fx R WNEXT M) (st fx' R' WBR2 M')
    /\ (forall x, In x KSJ -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 12) = Z_to_bv 64 (xd + 8 * (Z.of_nat k - 1) - 8) /\ getr R' (reg 16) = Z_to_bv 64 (yd + 8 * (Z.of_nat k - 1) - 8)
    /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  intros H11 H12 H16 Hk1 Hk2 Hx Hy.
  set (Vf := VAL R 0 0 0 0 xd yd 0 0 (Z.of_nat k) 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R 0 0 0 0 xd yd 0 0 (Z.of_nat k) 0 0 i) by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PJ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PJ.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PJ.kn0). { unfold know_ok, PJ.kn0. L5K.kn_all ZA. }
  destruct (PJ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PJ.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PJ.regs0 PJ.regs_out0 48 KSJ KSJ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PJ.regs_out0 E' R' 12 Hregs) by lia; cbn [nth PJ.regs_out0]; L5K.wordE' ZA Hag. }
  split. { rewrite (BG.out_reg PJ.regs_out0 E' R' 16 Hregs) by lia; cbn [nth PJ.regs_out0]; L5K.wordE' ZA Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma cmZ_conc fx R M : getr R (reg 11) = Z_to_bv 64 0 -> getr R (reg 13) = Z_to_bv 64 1 ->
  exists fx' R' M', msteps RSEGS (st fx R LHEAD M) (st fx' R' RET M')
    /\ (forall x, In x KSZ -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 10) = Z_to_bv 64 0 /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  intros H11 H13.
  set (Vf := VAL R 0 0 0 0 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R 0 0 0 0 0 0 0 0 0 0 0 i) by (apply VAL_VZ; lia). unfold VZ in ZA.
  assert (HR: regs_ok E PZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PZ.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PZ.kn0). { unfold know_ok, PZ.kn0. apply Forall_nil. }
  destruct (PZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PZ.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PZ.regs0 PZ.regs_out0 48 KSZ KSZ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PZ.regs_out0 E' R' 10 Hregs) by lia. reflexivity. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enc (z : Z) : Z := if z <? 0 then MAXW else z.
Lemma compare_loop_cases k wx wy :
  BigModel.compare_loop k wx wy = 0 \/ BigModel.compare_loop k wx wy = 1 \/ BigModel.compare_loop k wx wy = -1.
Proof. induction k as [|k IH]; cbn [BigModel.compare_loop]. tauto. destruct (_ <? _). tauto. destruct (_ <? _); tauto. Qed.
Lemma enc_cases k wx wy : let c := enc (BigModel.compare_loop k wx wy) in c = 0 \/ c = 1 \/ c = MAXW.
Proof. unfold enc. destruct (compare_loop_cases k wx wy) as [->|[->| ->]]; cbn; tauto. Qed.

Lemma wloop (k : nat) : forall fx R M (xd yd : Z) (n : nat) (wx wy : list Z),
  at_head R xd yd k -> getr R (reg 10) = Z_to_bv 64 MAXW -> (k <= n)%nat -> (1 <= n)%nat -> Z.of_nat n <= 300 ->
  4096 <= xd /\ xd + 8 * Z.of_nat n <= 2 ^ 47 -> 4096 <= yd /\ yd + 8 * Z.of_nat n <= 2 ^ 47 -> xd mod 8 = 0 -> yd mod 8 = 0 ->
  L5.limbs_at RSEGS M xd wx -> L5.limbs_at RSEGS M yd wy -> length wx = n -> length wy = n -> L5W.words_ok wx -> L5W.words_ok wy ->
  exists fx' R' M', msteps RSEGS (st fx R LHEAD M) (st fx' R' RET M')
    /\ (forall x, In x cmp_kept -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 10) = Z_to_bv 64 (enc (BigModel.compare_loop k wx wy))
    /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  induction k as [|k IH]; intros fx R M xd yd n wx wy AT A10 Hkn Hn1 Hn2 Bx By Ax Ay Lx Ly Nx Ny Wx Wy.
  - (* [comment removed for export] *)
    destruct AT as (A11 & _ & A13 & _).
    destruct (cmZ_conc fx R M A11 ltac:(rewrite A13; f_equal; lia)) as (fx1 & R1 & M1 & MS1 & K1 & B10 & MM1 & G1).
    exists fx1, R1, M1. split. exact MS1. split. { intros x Hx. apply K1. apply (L5K.incl_b cmp_kept KSZ ltac:(vm_compute; reflexivity)). exact Hx. }
    split. { exact B10. } split. exact MM1. exact G1.
  - pose proof AT as (A11 & A12 & A13 & A16).
    set (xk := L5W.nth_w wx k). set (yk := L5W.nth_w wy k).
    assert (Rxk : 0 <= xk < 2 ^ 64) by (apply L5W.words_ok_nth; exact Wx). assert (Ryk : 0 <= yk < 2 ^ 64) by (apply L5W.words_ok_nth; exact Wy).
    assert (Ux : L5.u64_at RSEGS M (xd + 8 * (Z.of_nat (S k) - 1)) xk).
    { replace (xd + 8 * (Z.of_nat (S k) - 1)) with (xd + 8 * Z.of_nat k) by lia. apply Lx. lia. }
    assert (Uy : L5.u64_at RSEGS M (yd + 8 * (Z.of_nat (S k) - 1)) yk).
    { replace (yd + 8 * (Z.of_nat (S k) - 1)) with (yd + 8 * Z.of_nat k) by lia. apply Ly. lia. }
    destruct (cmI_conc fx R M xd yd n (S k) xk yk AT ltac:(lia) Hn2 Bx By Ax Ay Ux Uy Rxk Ryk) as (fx1 & R1 & M1 & MS1 & K1 & B13 & (B14 & B15) & MM1 & G1).
    pose proof (br_219e0 fx1 R1 M1) as MB1. rewrite B14, B15 in MB1.
    assert (K1' : forall x, In x cmp_kept -> getr R1 (reg x) = getr R (reg x)).
    { intros x Hx. apply K1. apply (L5K.incl_b cmp_kept KSI ltac:(vm_compute; reflexivity)). exact Hx. }
    cbn [BigModel.compare_loop]. change (BigModel.nth_w wx k) with xk. change (BigModel.nth_w wy k) with yk.
    destruct (branch_taken BC_LTU (Z_to_bv 64 yk) (Z_to_bv 64 xk)) eqn:LT1.
    + (* [comment removed for export] *)
      assert (LT1': (yk <? xk) = true). { unfold branch_taken, bv_ltu in LT1. rewrite !BG.unsigned_lit in LT1 by lia. exact LT1. }
      rewrite LT1'.
      destruct (cmP_conc fx1 R1 M1 ltac:(rewrite (K1 11%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact A11)) as (fx2 & R2 & M2 & MS2 & K2 & B10 & MM2 & G2).
      exists fx2, R2, M2. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MB1. exact MS2. }
      split. { intros x Hx. rewrite (K2 x). apply K1'. exact Hx. apply (L5K.incl_b cmp_kept KSP ltac:(vm_compute; reflexivity)). exact Hx. }
      split. { exact B10. }
      split. { intros a. rewrite MM2. apply MM1. } eapply mem_grows_trans; eauto.
    + (* [comment removed for export] *)
      assert (LT1': (yk <? xk) = false). { unfold branch_taken, bv_ltu in LT1. rewrite !BG.unsigned_lit in LT1 by lia. exact LT1. }
      rewrite LT1'.
      destruct (cmJ_conc fx1 R1 M1 xd yd (S k) ltac:(rewrite (K1 11%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact A11)
                  ltac:(rewrite (K1 12%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact A12)
                  ltac:(rewrite (K1 16%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact A16) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
        as (fx2 & R2 & M2 & MS2 & K2 & C12 & C16 & MM2 & G2).
      pose proof (br_219ec fx2 R2 M2) as MB2.
      rewrite (K2 14%nat) in MB2 by (apply L5K.in_b; vm_compute; reflexivity). rewrite (K2 15%nat) in MB2 by (apply L5K.in_b; vm_compute; reflexivity).
      rewrite B14, B15 in MB2.
      destruct (branch_taken BC_GEU (Z_to_bv 64 xk) (Z_to_bv 64 yk)) eqn:GE2.
      * (* [comment removed for export] *)
        assert (GE2': (xk <? yk) = false).
        { unfold branch_taken, bv_ltu in GE2. apply Bool.negb_true_iff in GE2. rewrite !BG.unsigned_lit in GE2 by lia. exact GE2. }
        rewrite GE2'.
        assert (AT2: at_head R2 xd yd k).
        { unfold at_head. split. rewrite (K2 11%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (K1 11%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact A11.
          split. rewrite C12. f_equal. lia. split. rewrite (K2 13%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite B13. f_equal. lia.
          rewrite C16. f_equal. lia. }
        assert (A10': getr R2 (reg 10) = Z_to_bv 64 MAXW).
        { rewrite (K2 10%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (K1 10%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact A10. }
        assert (Lx2: L5.limbs_at RSEGS M2 xd wx).
        { apply (L5C.limbs_at_agree RSEGS M M2). intros i Hi. rewrite MM2. apply MM1. lia. rewrite Nx. lia. exact Lx. }
        assert (Ly2: L5.limbs_at RSEGS M2 yd wy).
        { apply (L5C.limbs_at_agree RSEGS M M2). intros i Hi. rewrite MM2. apply MM1. lia. rewrite Ny. lia. exact Ly. }
        destruct (IH fx2 R2 M2 xd yd n wx wy AT2 A10' ltac:(lia) Hn1 Hn2 Bx By Ax Ay Lx2 Ly2 Nx Ny Wx Wy) as (fx3 & R3 & M3 & MS3 & K3 & RES & MM3 & G3).
        exists fx3, R3, M3. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MB1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact MB2. exact MS3. }
        split. { intros x Hx. rewrite (K3 x Hx). rewrite (K2 x). apply K1'. exact Hx. apply (L5K.incl_b cmp_kept KSJ ltac:(vm_compute; reflexivity)). exact Hx. }
        split. exact RES. split. { intros a. rewrite MM3, MM2. apply MM1. } eapply mem_grows_trans. exact G1. eapply mem_grows_trans; eauto.
      * (* [comment removed for export] *)
        assert (GE2': (xk <? yk) = true).
        { unfold branch_taken, bv_ltu in GE2. apply Bool.negb_false_iff in GE2. rewrite !BG.unsigned_lit in GE2 by lia. exact GE2. }
        rewrite GE2'.
        destruct (cmN_conc fx2 R2 M2 ltac:(rewrite (K2 11%nat) by (apply L5K.in_b; vm_compute; reflexivity); rewrite (K1 11%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact A11))
          as (fx3 & R3 & M3 & MS3 & K3 & MM3 & G3).
        exists fx3, R3, M3. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MB1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact MB2. exact MS3. }
        split. { intros x Hx. rewrite (K3 x). rewrite (K2 x). apply K1'. exact Hx. apply (L5K.incl_b cmp_kept KSJ ltac:(vm_compute; reflexivity)). exact Hx.
                 apply (L5K.incl_b cmp_kept KSN ltac:(vm_compute; reflexivity)). exact Hx. }
        split. { rewrite (K3 10%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (K2 10%nat) by (apply L5K.in_b; vm_compute; reflexivity).
                 rewrite (K1 10%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact A10. }
        split. { intros a. rewrite MM3, MM2. apply MM1. } eapply mem_grows_trans. exact G1. eapply mem_grows_trans; eauto.
Qed.

(* [comment removed for export] *)
Lemma enc_full wx wy n : length wx = n -> length wy = n -> L5W.words_ok wx -> L5W.words_ok wy ->
  enc (BigModel.compare_loop n wx wy) = cmp_val wx wy.
Proof.
  intros Nx Ny Wx Wy. apply L5W.words_ok_BF in Wx. apply L5W.words_ok_BF in Wy.
  rewrite (BigFactsOps.compare_loop_spec wx wy Wx Wy n) by lia.
  rewrite <- Nx at 1. rewrite firstn_all. rewrite <- Ny. rewrite firstn_all.
  unfold enc, cmp_val, BigFactsOps.cmp3.
  destruct (Z.compare_spec (BigFactsBase.val wx) (BigFactsBase.val wy));
    destruct (Z.ltb_spec (BigFactsBase.val wx) (BigFactsBase.val wy)); try lia;
    destruct (Z.ltb_spec (BigFactsBase.val wy) (BigFactsBase.val wx)); try lia; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kept_regs_preserved R R' : (forall i, In i cmp_kept -> getr R' (reg i) = getr R (reg i)) -> regs_preserved R R'.
Proof.
  intros K x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply K.
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.

Theorem cmp_run (fx : FPState) R M (xo yo r : Z) (bx by_ : L5.bigobj) (wx wy : list Z) :
  getr R (reg 10) = Z_to_bv 64 xo -> getr R (reg 11) = Z_to_bv 64 yo -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  cmp_obj M xo bx -> cmp_obj M yo by_ -> L5C.obj_limbs RSEGS M bx wx -> L5C.obj_limbs RSEGS M by_ wy ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R CMP M) (st fx' R' r M') /\ cmp_post M M' R R' (L5.bo_len bx) (L5.bo_len by_) wx wy.
Proof.
  intros H10 H11 H1 [Hr He] OX OY OLX OLY.
  destruct (obj_limbs_data M xo bx wx ltac:(exact (proj1 OX)) OLX) as (Lx & Nx & Wx).
  destruct (obj_limbs_data M yo by_ wy ltac:(exact (proj1 OY)) OLY) as (Ly & Ny & Wy).
  destruct (cmA_conc fx R M xo yo bx by_ OX OY H10 H11) as (fx1 & R1 & M1 & MS1 & K1 & (A10 & A11 & A12 & A14 & A15 & A16) & MM1 & G1).
  pose proof OX as (_ & _ & Xl1 & Xl2 & _ & _ & _ & Xdlo & Xdhi & Xd). pose proof OY as (_ & _ & Yl1 & Yl2 & _ & _ & _ & Ydlo & Ydhi & Yd).
  pose proof OX as ((_ & _ & _ & XST) & _). pose proof OY as ((_ & _ & _ & YST) & _).
  assert (Ax: L5.bo_data xo bx mod 8 = 0).
  { destruct bx as [f l [v0 v1|c q]]; cbn [L5.bo_data L5.bo_st] in *. pose proof OX as (_ & _ & _ & _ & X8 & _). rewrite Z.add_mod, X8 by lia. reflexivity.
    destruct XST as (_ & _ & _ & _ & _ & Q8 & _). exact Q8. }
  assert (Ay: L5.bo_data yo by_ mod 8 = 0).
  { destruct by_ as [f l [v0 v1|c q]]; cbn [L5.bo_data L5.bo_st] in *. pose proof OY as (_ & _ & _ & _ & Y8 & _). rewrite Z.add_mod, Y8 by lia. reflexivity.
    destruct YST as (_ & _ & _ & _ & _ & Q8 & _). exact Q8. }
  set (xd := L5.bo_data xo bx) in *. set (yd := L5.bo_data yo by_) in *.
  set (nx := L5.bo_len bx) in *. set (ny := L5.bo_len by_) in *.
  assert (K1' : forall x, In x cmp_kept -> getr R1 (reg x) = getr R (reg x)).
  { intros x Hx. apply K1. apply (L5K.incl_b cmp_kept KSA ltac:(vm_compute; reflexivity)). exact Hx. }
  assert (B1: getr R1 (reg 1) = Z_to_bv 64 r). { rewrite (K1 1%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H1. }
  assert (PACK: forall (fx' : FPState) R' M' c, msteps RSEGS (st fx1 R1 SZBR M1) (st fx' R' RET M') ->
      (forall x, In x cmp_kept -> getr R' (reg x) = getr R1 (reg x)) -> getr R' (reg 10) = Z_to_bv 64 c -> res_sized c nx ny -> (nx = ny -> c = cmp_val wx wy) ->
      (forall a, M' a = M1 a) -> mem_grows M1 M' ->
      exists (fx'' : FPState) R'' M'', msteps RSEGS (st fx R CMP M) (st fx'' R'' r M'') /\ cmp_post M M'' R R'' nx ny wx wy).
  { intros fx' R' M' c MS K B10 RES VAL' MM G.
    pose proof (ret_219f4 fx' R' M' r ltac:(rewrite (K 1%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact B1) Hr He) as MSR.
    exists fx', R', M'. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS. exact MSR. }
    assert (KK: forall i, In i cmp_kept -> getr R' (reg i) = getr R (reg i)). { intros i Hi. rewrite (K i Hi). apply K1'. exact Hi. }
    split. exact KK. split. apply kept_regs_preserved; exact KK. split. exists c; split; [exact B10 | split; [exact RES | exact VAL']].
    split. { intros a. rewrite MM. apply MM1. } eapply mem_grows_trans; eauto. }
  pose proof (br_219a8 fx1 R1 M1) as MB1. rewrite A14, A15 in MB1.
  destruct (branch_taken BC_LTU (Z_to_bv 64 (Z.of_nat nx)) (Z_to_bv 64 (Z.of_nat ny))) eqn:LT.
  - (* [comment removed for export] *)
    assert (LT': (nx < ny)%nat).
    { unfold branch_taken, bv_ltu in LT. rewrite !BG.unsigned_lit in LT by lia. apply Z.ltb_lt in LT. lia. }
    destruct (cmN_conc fx1 R1 M1 A11) as (fx2 & R2 & M2 & MS2 & K2 & MM2 & G2).
    apply (PACK fx2 R2 M2 MAXW). { eapply msteps_trans. exact MB1. exact MS2. }
    { intros x Hx. apply K2. apply (L5K.incl_b cmp_kept KSN ltac:(vm_compute; reflexivity)). exact Hx. }
    { rewrite (K2 10%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact A10. }
    { split. right; right; reflexivity. split. reflexivity. intros; lia. } { intros; exfalso; lia. } exact MM2. exact G2.
  - pose proof (br_219ac fx1 R1 M1) as MB2. rewrite A14, A15 in MB2.
    destruct (branch_taken BC_GEU (Z_to_bv 64 (Z.of_nat ny)) (Z_to_bv 64 (Z.of_nat nx))) eqn:GE.
    + (* [comment removed for export] *)
      assert (EQ: nx = ny).
      { unfold branch_taken in LT, GE. apply Bool.negb_true_iff in GE.
        unfold bv_ltu in LT, GE. rewrite !BG.unsigned_lit in LT, GE by lia. apply Z.ltb_ge in LT. apply Z.ltb_ge in GE. lia. }
      destruct (cmE_conc fx1 R1 M1 xd yd nx A11 A12 A14 ltac:(rewrite A15; f_equal; lia) A16 Xl1 Xl2 ltac:(lia) ltac:(lia))
        as (fx2 & R2 & M2 & MS2 & K2 & AT2 & MM2 & G2).
      assert (Lx2: L5.limbs_at RSEGS M2 xd wx).
      { apply (L5C.limbs_at_agree RSEGS M M2). intros i Hi. rewrite MM2. apply MM1. lia. rewrite Nx. lia. exact Lx. }
      assert (Ly2: L5.limbs_at RSEGS M2 yd wy).
      { apply (L5C.limbs_at_agree RSEGS M M2). intros i Hi. rewrite MM2. apply MM1. lia. rewrite Ny. lia. exact Ly. }
      destruct (wloop nx fx2 R2 M2 xd yd nx wx wy AT2 ltac:(rewrite (K2 10%nat) by (apply L5K.in_b; vm_compute; reflexivity); exact A10)
                  ltac:(lia) Xl1 Xl2 ltac:(lia) ltac:(lia) Ax Ay Lx2 Ly2 Nx ltac:(lia) Wx Wy) as (fx3 & R3 & M3 & MS3 & K3 & B10 & MM3 & G3).
      apply (PACK fx3 R3 M3 (enc (BigModel.compare_loop nx wx wy))). { eapply msteps_trans. exact MB1. eapply msteps_trans. exact MB2. eapply msteps_trans. exact MS2. exact MS3. }
      { intros x Hx. rewrite (K3 x Hx). apply K2. apply (L5K.incl_b cmp_kept KSE ltac:(vm_compute; reflexivity)). exact Hx. }
      exact B10. { split. apply enc_cases. split; intros; lia. } { intros _. apply (enc_full wx wy nx Nx ltac:(lia) Wx Wy). }
      { intros a. rewrite MM3. apply MM2. } eapply mem_grows_trans; eauto.
    + (* [comment removed for export] *)
      assert (GE': (ny < nx)%nat).
      { unfold branch_taken, bv_ltu in LT, GE. apply Bool.negb_false_iff in GE. rewrite !BG.unsigned_lit in LT, GE by lia.
        apply Z.ltb_ge in LT. apply Z.ltb_lt in GE. lia. }
      destruct (cmP_conc fx1 R1 M1 A11) as (fx2 & R2 & M2 & MS2 & K2 & B10 & MM2 & G2).
      apply (PACK fx2 R2 M2 1). { eapply msteps_trans. exact MB1. eapply msteps_trans. exact MB2. exact MS2. }
      { intros x Hx. apply K2. apply (L5K.incl_b cmp_kept KSP ltac:(vm_compute; reflexivity)). exact Hx. }
      exact B10. { split. right; left; reflexivity. split. intros; lia. reflexivity. } { intros; exfalso; lia. } exact MM2. exact G2.
Qed.

Lemma r1 : (1%bv : bv 5) = reg 1. Proof. apply bv_eq; reflexivity. Qed.
Lemma r10 : (10%bv : bv 5) = reg 10. Proof. apply bv_eq; reflexivity. Qed.
Lemma r11 : (11%bv : bv 5) = reg 11. Proof. apply bv_eq; reflexivity. Qed.

Theorem cmp_ok : cmp_spec.
Proof.
  intros fx R M model K xo yo r bx by_ wx wy Hh Hl H10 H11 H1 Hra OX OY OLX OLY HK. unfold cfg.
  rewrite r10 in H10. rewrite r11 in H11. rewrite r1 in H1.
  eapply (L5.run_cps RSEGS (fun _ R' M' => cmp_post M M' R R' (L5.bo_len bx) (L5.bo_len by_) wx wy)). exact Hh. exact Hl.
  - exact (cmp_run fx R M xo yo r bx by_ wx wy H10 H11 H1 Hra OX OY OLX OLY).
  - intros fx' R' M' HP. apply HK. exact HP.
Qed.
End SCFG_2.


End L5CMP.
