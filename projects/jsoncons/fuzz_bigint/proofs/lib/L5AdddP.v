(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore AsanPlanSoundSums Src0Sums
     Src0_code_20088_210bc BigLinkBase BigLinkGlue BigLinkInlBase BigLinkShl BigLinkReduce L5Defs L5Core L5CoreKit L5CoreKitS L5CoreSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5AdddP.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigModel BigFactsBase BigFactsDigits.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADDP.
Import L5CS.
Module PA1 := LibSegZ_lca1.
Module P2D := LibSegZ_lca2d.
Module P2I := LibSegZ_lca2i.
Module P3Z := LibSegZ_lca3z.
Module P3N := LibSegZ_lca3n.
Module P3C := LibSegZ_lca3c.
Module PIT := LibSegZ_lcait.
Module PIN := LibSegZ_lcain.
Module PIC := LibSegZ_lcaic.
Module P4 := LibSegZ_lca4.
Module P5 := LibSegZ_lca5.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition RET1 : Z := 0x20ebc.      (* [comment removed for export] *)
Definition BR3 : Z := 0x20f68.       (* [comment removed for export] *)
Definition LOOP : Z := 0x20f7c.      (* [comment removed for export] *)
Definition TAIL : Z := 0x20f9c.      (* [comment removed for export] *)
Definition RET2 : Z := 0x20fa4.      (* [comment removed for export] *)
Definition RETI : Z := 0x20fb8.      (* [comment removed for export] *)
Definition REDUCE : Z := 0x215d0.

Definition KS1 : list nat := Eval vm_compute in (BG.kept_list 48 PA1.regs0 PA1.regs_out).
Lemma KS1_ok : BG.kept_ok 48 PA1.regs0 PA1.regs_out KS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS2 : list nat := Eval vm_compute in (BG.kept_list 48 P2D.regs0 P2D.regs_out).
Lemma KS2d_ok : BG.kept_ok 48 P2D.regs0 P2D.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS2i_ok : BG.kept_ok 48 P2I.regs0 P2I.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS3 : list nat := Eval vm_compute in (BG.kept_list 48 P3C.regs0 P3C.regs_out).
Lemma KS3z_ok : BG.kept_ok 48 P3Z.regs0 P3Z.regs_out KS3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS3n_ok : BG.kept_ok 48 P3N.regs0 P3N.regs_out KS3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS3c_ok : BG.kept_ok 48 P3C.regs0 P3C.regs_out KS3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KSIT : list nat := Eval vm_compute in (BG.kept_list 48 PIT.regs0 PIT.regs_out).
Lemma KSIT_ok : BG.kept_ok 48 PIT.regs0 PIT.regs_out KSIT = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSIN_ok : BG.kept_ok 48 PIN.regs0 PIN.regs_out KSIT = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSIC_ok : BG.kept_ok 48 PIC.regs0 PIC.regs_out KSIT = true. Proof. vm_compute. reflexivity. Qed.
Definition KS4 : list nat := Eval vm_compute in (BG.kept_list 48 P4.regs0 P4.regs_out).
Lemma KS4_ok : BG.kept_ok 48 P4.regs0 P4.regs_out KS4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS5 : list nat := Eval vm_compute in (BG.kept_list 48 P5.regs0 P5.regs_out).
Lemma KS5_ok : BG.kept_ok 48 P5.regs0 P5.regs_out KS5 = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition KSF : list nat := [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma KSF_2 x : In x KSF -> In x KS2. Proof. intros H. L5K.inlist H. Qed.
Lemma KSF_3 x : In x KSF -> In x KS3. Proof. intros H. L5K.inlist H. Qed.
Lemma KSF_IT x : In x KSF -> In x KSIT. Proof. intros H. L5K.inlist H. Qed.

Definition z8 : BL.za := Eval vm_compute in (BL.zc (ELit 8)).
Definition z32 : BL.za := Eval vm_compute in (BL.zc (ELit 32)).
Definition z96 : BL.za := Eval vm_compute in (BL.zc (ELit 96)).
Lemma z8_ok : BL.zcomp (ELit 8) = Some z8. Proof. vm_compute. reflexivity. Qed.
Lemma z32_ok : BL.zcomp (ELit 32) = Some z32. Proof. vm_compute. reflexivity. Qed.
Lemma z96_ok : BL.zcomp (ELit 96) = Some z96. Proof. vm_compute. reflexivity. Qed.

Lemma ret_20eb4 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RETI M) (st fx R r M).
Proof. intros H1 Hr He. apply (BRED.ret_to fx R M RETI W_20fb8 r F_20fb8 eq_refl D_20fb8 H1 Hr He). Qed.

(* [comment removed for export] *)
Lemma land1_of_bit0 fb (b : bool) : 0 <= fb -> Z.testbit fb 0 = b -> Z.land fb 1 = (if b then 1 else 0).
Proof.
  intros Hfb Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hi0]. { rewrite Hb. destruct b; reflexivity. }
  replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r.
  destruct b. symmetry; apply Z.bits_above_log2; cbn; lia. rewrite Z.bits_0. reflexivity.
Qed.
Lemma land2_of_bit1 fb : 0 <= fb -> Z.testbit fb 1 = false -> Z.land fb 2 = 0.
Proof.
  intros Hfb Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec i 1) as [->|Hi1]. { rewrite Hb. reflexivity. }
  replace (Z.testbit 2 i) with false. apply Bool.andb_false_r.
  destruct (Z.eq_dec i 0) as [->|Hi0]. reflexivity. symmetry; apply Z.bits_above_log2; cbn; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p1_run fx R M (o sp fb len : Z) :
  getr R (reg 10) = Z_to_bv 64 o -> 4096 <= o -> o mod 8 = 0 ->
  getr R (reg 2) = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0x7fff7f800000 + 96 <= sp -> sp <= 2 ^ 47 -> BG.writable M (sp - 96) 96 ->
  sp <= o -> o + 32 <= 2 ^ 47 ->
  BG.u8_at M o fb -> 0 <= fb < 256 -> Z.testbit fb 1 = false -> BG.u64_at M (o + 8) len -> 0 <= len <= 2 ^ 23 ->
  exists fx' R1 M1, msteps RSEGS (st fx R ADDD M) (st fx' R1 RESIZE M1)
    /\ (forall x, In x KS1 -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 1) = Z_to_bv 64 RET1 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 96)
    /\ getr R1 (reg 8) = Z_to_bv 64 o /\ getr R1 (reg 9) = getr R (reg 11) /\ getr R1 (reg 10) = Z_to_bv 64 o /\ getr R1 (reg 11) = Z_to_bv 64 (len + 1)
    /\ BG.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BG.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8)))
    /\ BG.u64_at M1 (sp - 24) (bv_unsigned (getr R (reg 9)))
    /\ (forall a : word, ~ (sp - 96 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H10 Olo Ao H2 A16 SLO SHI WR Oge Ohi O0 Hfb Bfb O8 Hlen.
  set (Vf := fun k : nat => match k with 33%nat => Z_to_bv 64 fb | 34%nat => Z_to_bv 64 len | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BG.unsigned_lit; lia).
  assert (U10: bv_unsigned (ev E 10) = o) by (cbv [E ev Vf]; rewrite H10; apply BG.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = len) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (HR: regs_ok E PA1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl PA1.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
  assert (HK: know_ok RSEGS E M PA1.kn0).
  { unfold know_ok. cbv delta [PA1.kn0].
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U10. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U10. lia. lia. }
    apply Forall_cons. { eapply (BG.kentry_KDisj_z E M 10 0 (ELit 32) z32 32 2 (-96) (ELit 96) z96 96 o sp U10 U2 z32_ok eq_refl z96_ok eq_refl). lia. }
    apply Forall_cons. { eapply (BSHL.kentry_KWord1_var E M 10 0 33 o fb U10 U33). lia. lia. lia. rewrite Z.add_0_r. exact O0. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U33. lia. }
    apply Forall_cons. { cbn [kentry_ok edenot]. rewrite BSHL.and_lit_val by lia. rewrite U33, (land2_of_bit1 fb) by (lia || exact Bfb). lia. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U10. exact U34. lia. lia. exact O8. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U34. lia. }
    apply Forall_nil. }
  destruct (PA1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
  apply BSHL.nth_error_single in Hnth. subst ps0. change PA1.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
  assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i PA1.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros j k z Hj Hnth Hk Hz. rewrite (BG.out_reg PA1.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact Hz. }
  assert (CELL: forall off k, In (KWord (SA (EVar 2) off) 8 (EVar k)) PA1.cells -> (k < 32)%nat -> BG.u64_at M' (sp + off) (bv_unsigned (getr R (reg k)))).
  { intros off k Hin Hk. eapply (BG.u64_of_KWord E' M' 2 off). apply Hcells. exact Hin. exact A2.
    cbn [edenot]. rewrite AG by lia. destruct k as [|k']; [reflexivity|]. cbv [E ev Vf]. do 35 (try (destruct k' as [|k']; [reflexivity|])). lia. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PA1.regs0 PA1.regs_out 48 KS1 KS1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 1 Hregs) by lia. reflexivity. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 2 Hregs) by lia. change (nth 2 PA1.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-96))).
           cbn [edenot]. rewrite AG by lia. rewrite (BG.word_of_unsigned _ _ U2), BG.alu_add_lit. reflexivity. }
  split. { apply (OUT 8%nat 10%nat); [lia | reflexivity | lia | exact U10]. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 9 Hregs) by lia. change (nth 9 PA1.regs_out (ELit 0)) with (EVar 11). cbn [edenot]. rewrite AG by lia. reflexivity. }
  split. { apply (OUT 10%nat 10%nat); [lia | reflexivity | lia | exact U10]. }
  split. { rewrite (BG.out_reg PA1.regs_out E' R' 11 Hregs) by lia. change (nth 11 PA1.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 34) (ELit 1)).
           cbn [edenot]. rewrite AG by lia. rewrite (BG.word_of_unsigned _ _ U34), BG.alu_add_lit. reflexivity. }
  split. { replace (sp - 8) with (sp + -8) by lia. apply CELL; [cbv delta [PA1.cells]; cbn; tauto | lia]. }
  split. { replace (sp - 16) with (sp + -16) by lia. apply CELL; [cbv delta [PA1.cells]; cbn; tauto | lia]. }
  split. { replace (sp - 24) with (sp + -24) by lia. apply CELL; [cbv delta [PA1.cells]; cbn; tauto | lia]. }
  split. { intros a Ha. apply Hfr. unfold SGP.outside. change PA1.F0 with [(EVar 2, -96, ELit 96)].
           constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BG.unsigned_lit by lia. lia. } constructor. }
  exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_ret1 (R : bvmap 5 word) (M : word -> option byte) (o d sp c8 c16 c24 : Z) : Prop :=
  getr R (reg 8) = Z_to_bv 64 o /\ getr R (reg 9) = Z_to_bv 64 d /\ getr R (reg 2) = Z_to_bv 64 (sp - 96) /\
  BG.u64_at M (sp - 8) c8 /\ BG.u64_at M (sp - 16) c16 /\ BG.u64_at M (sp - 24) c24 /\
  0 <= c8 < 2 ^ 64 /\ 0 <= c16 < 2 ^ 64 /\ 0 <= c24 < 2 ^ 64.

(* [comment removed for export] *)
Lemma p2_run (td : bool) fx R M (o d sp c8 c16 c24 f n qd x0 : Z) :
  at_ret1 R M o d sp c8 c16 c24 -> 0 <= o -> o + 32 <= 2 ^ 47 -> 0 <= d <= 9 -> 1 <= n <= 2 ^ 23 + 1 ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 96 <= sp -> sp <= 2 ^ 47 -> BG.writable M (sp - 96) 96 ->
  o mod 8 = 0 -> sp <= o ->
  BG.u8_at M o f -> 0 <= f < 256 -> Z.testbit f 0 = td -> BG.u64_at M (o + 8) n ->
  (td = true -> BG.u64_at M (o + 24) qd /\ 4096 <= qd /\ qd + 8 <= 2 ^ 47 /\ qd mod 8 = 0 /\ (qd + 8 <= sp - 96 \/ sp <= qd) /\ (qd + 8 <= o \/ o + 32 <= qd)
                /\ BG.writable M qd 8) ->
  (td = false -> BG.writable M (o + 16) 8) ->
  let data := if td then qd else o + 16 in
  BG.u64_at M data x0 -> 0 <= x0 < 2 ^ 64 ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET1 M) (st fx' R3 BR3 M3)
    /\ (forall x, In x KS2 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R3 (reg 8) = Z_to_bv 64 o /\ getr R3 (reg 9) = Z_to_bv 64 (x0 + d)
    /\ getr R3 (reg 10) = Z_to_bv 64 n /\ getr R3 (reg 11) = Z_to_bv 64 data /\ getr R3 (reg 12) = Z_to_bv 64 x0 /\ getr R3 (reg 13) = Z_to_bv 64 2
    /\ BG.u64_at M3 data ((x0 + d) mod 2 ^ 64)
    /\ (forall a : word, ~ (data <= bv_unsigned a < data + 8) -> M3 a = M a) /\ mem_grows M M3.
Proof.
  intros (H8 & H9 & H2 & C8 & C16 & C24 & R8 & R16 & R24) Olo Ohi Hd Hn A16 SLO SHI WR Ao Oge O0 Hf Bf O8 HQ HI data OX Hx0.
  assert (QD: (0 <= qd < 2 ^ 64) \/ td = false). { destruct td. left. destruct (HQ eq_refl) as (_ & X1 & X2 & _). lia. right; reflexivity. }
  set (qd' := if td then qd else 0).
  assert (Hq': 0 <= qd' < 2 ^ 64). { subst qd'. destruct td. destruct QD as [X|X]. lia. discriminate. lia. }
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | 32%nat => Z_to_bv 64 d | 34%nat => Z_to_bv 64 n
                                         | 36%nat => Z_to_bv 64 x0 | 38%nat => Z_to_bv 64 f | 39%nat => Z_to_bv 64 qd' | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U32: bv_unsigned (ev E 32) = d) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = n) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = x0) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U38: bv_unsigned (ev E 38) = f) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U39: bv_unsigned (ev E 39) = qd') by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  pose proof (land1_of_bit0 f td ltac:(lia) Bf) as LT.
  assert (KC: forall K, In K
    [KRange (EVar 2) 140735332483168 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-96)) (ELit 96);
     KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 8;
     KDisj (SA (EVar 35) 0) (ELit 32) (SA (EVar 2) (-96)) (ELit 96);
     KRange (EVar 32) 0 9;
     KWord (SA (EVar 35) 0) 1 (EVar 38); KRange (EVar 38) 0 255;
     KWord (SA (EVar 35) 8) 8 (EVar 34); KRange (EVar 34) 1 8388609] -> kentry_ok RSEGS E M K).
  { intros K HK. cbn in HK.
    repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BG.kentry_KRange_var. exact U2. lia.
    - eapply BG.kentry_KAlign_var. exact U2. lia. lia.
    - eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR.
    - eapply BG.kentry_KRange_var. exact U35. lia.
    - eapply BG.kentry_KAlign_var. exact U35. lia. lia.
    - eapply (BG.kentry_KDisj_z E M 35 0 (ELit 32) z32 32 2 (-96) (ELit 96) z96 96 o sp U35 U2 z32_ok eq_refl z96_ok eq_refl). lia.
    - eapply BG.kentry_KRange_var. exact U32. lia.
    - eapply (BSHL.kentry_KWord1_var E M 35 0 38 o f U35 U38). lia. lia. lia. rewrite Z.add_0_r. exact O0.
    - eapply BG.kentry_KRange_var. exact U38. lia.
    - eapply BG.kentry_KWord_var. exact U35. exact U34. lia. lia. exact O8.
    - eapply BG.kentry_KRange_var. exact U34. lia. }
  assert (KT: forall v, Z.land f 1 = v -> kentry_ok RSEGS E M (KRange (EAlu ALU_AND (EVar 38) (ELit 1)) v v)).
  { intros v Hv. cbn [kentry_ok edenot]. rewrite BSHL.and_lit_val by lia. rewrite U38, Hv. lia. }
  assert (KQ: td = true -> forall K, In K [KWord (SA (EVar 35) 24) 8 (EVar 39); KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 8;
                                          KWr (SA (EVar 39) 0) (ELit 8); KWord (SA (EVar 39) 0) 8 (EVar 36);
                                          KDisj (SA (EVar 39) 0) (ELit 8) (SA (EVar 2) (-96)) (ELit 96); KDisj (SA (EVar 39) 0) (ELit 8) (SA (EVar 35) 0) (ELit 32)]
                         -> kentry_ok RSEGS E M K).
  { intros Htd K HK. destruct (HQ Htd) as (O24 & Q1 & Q2 & Q3 & Q4 & Q5 & QW). assert (Eq: qd' = qd) by (subst qd'; rewrite Htd; reflexivity).
    assert (OXq: BG.u64_at M qd x0). { subst data. rewrite Htd in OX. exact OX. }
    cbn in HK. repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BG.kentry_KWord_var. exact U35. exact U39. lia. lia. rewrite Eq. exact O24.
    - eapply BG.kentry_KRange_var. exact U39. lia.
    - eapply BG.kentry_KAlign_var. exact U39. lia. lia.
    - eapply BG.kentry_KWr_var. exact U39. lia. lia. lia. rewrite Eq, Z.add_0_r. exact QW.
    - eapply BG.kentry_KWord_var. exact U39. exact U36. lia. lia. rewrite Eq, Z.add_0_r. exact OXq.
    - eapply (BG.kentry_KDisj_z E M 39 0 (ELit 8) z8 8 2 (-96) (ELit 96) z96 96 qd' sp U39 U2 z8_ok eq_refl z96_ok eq_refl). lia.
    - eapply (BG.kentry_KDisj_z E M 39 0 (ELit 8) z8 8 35 0 (ELit 32) z32 32 qd' o U39 U35 z8_ok eq_refl z32_ok eq_refl). lia. }
  assert (KI: td = false -> forall K, In K [KWr (SA (EVar 35) 16) (ELit 8); KWord (SA (EVar 35) 16) 8 (EVar 36)] -> kentry_ok RSEGS E M K).
  { intros Htd K HK. assert (OXi: BG.u64_at M (o + 16) x0). { subst data. rewrite Htd in OX. exact OX. }
    cbn in HK. repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BG.kentry_KWr_var. exact U35. lia. lia. lia. exact (HI Htd).
    - eapply BG.kentry_KWord_var. exact U35. exact U36. lia. lia. exact OXi. }
  assert (HRX: forall regs0, regs0 = P2D.regs0 -> regs_ok E regs0 R).
  { intros regs0 ->. apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P2D.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
    rewrite BG.alu_add_lit. exact H2. }
  assert (SAME: P2I.regs0 = P2D.regs0) by reflexivity.
  assert (Edata: (if td then qd' else o + 16) = data). { subst qd' data. destruct td; reflexivity. }
  assert (POST: forall (fx' : FPState) E' (R' : bvmap 5 word) (M' : word -> option byte) (regs0 regs_out : list expr) (cells : list kentry) (F0 : list SGP.region) (KSL : list nat) (eb : expr) (boff : Z),
     regs0 = P2D.regs0 -> BG.kept_ok 48 regs0 regs_out KSL = true -> incl KS2 KSL ->
     env_agree 48 E E' ->
     (forall i e, In (i, e) (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (reg i) = edenot E' e) ->
     (forall a : word, SGP.outside E' F0 a -> M' a = M a) -> F0 = [(eb, boff, ELit 8)] ->
     (forall K, In K cells -> kentry_ok RSEGS E' M' K) -> cells = [KWord (SA eb boff) 8 (EAlu ALU_ADD (EVar 32) (EVar 36))] ->
     bv_unsigned (edenot E eb) + boff = data -> expr_vars_lt 48 eb = true ->
     nth 2 regs_out (ELit 0) = EAlu ALU_ADD (EVar 2) (ELit (-96)) -> nth 8 regs_out (ELit 0) = EVar 35 -> nth 9 regs_out (ELit 0) = EAlu ALU_ADD (EVar 32) (EVar 36) ->
     nth 10 regs_out (ELit 0) = EVar 34 -> nth 11 regs_out (ELit 0) = (if td then EVar 39 else EAlu ALU_ADD (EVar 35) (ELit 16)) ->
     nth 12 regs_out (ELit 0) = EVar 36 -> nth 13 regs_out (ELit 0) = ELit 2 ->
     mem_grows M M' ->
     (forall x, In x KS2 -> getr R' (reg x) = getr R (reg x))
     /\ getr R' (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R' (reg 8) = Z_to_bv 64 o /\ getr R' (reg 9) = Z_to_bv 64 (x0 + d)
     /\ getr R' (reg 10) = Z_to_bv 64 n /\ getr R' (reg 11) = Z_to_bv 64 data /\ getr R' (reg 12) = Z_to_bv 64 x0 /\ getr R' (reg 13) = Z_to_bv 64 2
     /\ BG.u64_at M' data ((x0 + d) mod 2 ^ 64)
     /\ (forall a : word, ~ (data <= bv_unsigned a < data + 8) -> M' a = M a) /\ mem_grows M M').
  { intros fx' E' R' M' regs0 regs_out cells F0 KSL eb boff -> KOK INCL Hag Hregs Hfr -> Hcells -> Heb Hebv N2 N8 N9 N10 N11 N12 N13 Hgr.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
    { intros j k z Hj Hnth Hk Hz. rewrite (BG.out_reg regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact Hz. }
    assert (Heb': bv_unsigned (edenot E' eb) + boff = data). { rewrite (BG.edenot_kept 48 E E') by (auto; exact Hebv). exact Heb. }
    assert (SUM: bv_unsigned (edenot E' (EAlu ALU_ADD (EVar 32) (EVar 36))) = (x0 + d) mod 2 ^ 64).
    { cbn [edenot]. rewrite !AG by lia. rewrite (BG.word_of_unsigned _ _ U32), (BG.word_of_unsigned _ _ U36), BG.alu_add_lit. rewrite Z_to_bv_unsigned.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). f_equal. lia. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' P2D.regs0 regs_out 48 KSL KOK (HRX _ eq_refl) Hag Hregs j (INCL j Hj)). }
    split. { rewrite (BG.out_reg regs_out E' R' 2 Hregs) by lia. rewrite N2. cbn [edenot]. rewrite AG by lia. rewrite (BG.word_of_unsigned _ _ U2), BG.alu_add_lit. reflexivity. }
    split. { apply (OUT 8%nat 35%nat); [lia | exact N8 | lia | exact U35]. }
    split. { rewrite (BG.out_reg regs_out E' R' 9 Hregs) by lia. rewrite N9. apply bv_eq. rewrite SUM, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity. }
    split. { apply (OUT 10%nat 34%nat); [lia | exact N10 | lia | exact U34]. }
    split. { rewrite (BG.out_reg regs_out E' R' 11 Hregs) by lia. rewrite N11. rewrite <- Edata. destruct td.
             - cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U39.
             - cbn [edenot]. rewrite AG by lia. rewrite (BG.word_of_unsigned _ _ U35), BG.alu_add_lit. reflexivity. }
    split. { apply (OUT 12%nat 36%nat); [lia | exact N12 | lia | exact U36]. }
    split. { rewrite (BG.out_reg regs_out E' R' 13 Hregs) by lia. rewrite N13. reflexivity. }
    split. { replace data with (bv_unsigned (edenot E' eb) + boff) by exact Heb'. eapply (BG.u64_of_KWord_e E' M' eb boff). apply Hcells. left; reflexivity. reflexivity. exact SUM. }
    split. { intros a Ha. apply Hfr. unfold SGP.outside. constructor; [|constructor]. unfold estart. cbn [a_base a_off]. rewrite Heb'. change (elenZ E' (ELit 8)) with 8. lia. }
    exact Hgr. }
  destruct td.
  - assert (HK: know_ok RSEGS E M P2D.kn0).
    { unfold know_ok. cbv delta [P2D.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KT; exact LT | apply (KQ eq_refl); cbn; tauto] |]). apply Forall_nil. }
    destruct (P2D.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BSHL.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' P2D.regs0 P2D.regs_out P2D.cells P2D.F0 KS2 (EVar 39) 0 eq_refl KS2d_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells eq_refl);
      try reflexivity. 2: exact Hgr.
    cbn [edenot]. rewrite U39. subst qd' data. lia.
  - assert (HK: know_ok RSEGS E M P2I.kn0).
    { unfold know_ok. cbv delta [P2I.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KT; exact LT | apply (KI eq_refl); cbn; tauto] |]). apply Forall_nil. }
    destruct (P2I.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BSHL.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' P2I.regs0 P2I.regs_out P2I.cells P2I.F0 KS2 (EVar 35) 16 eq_refl KS2i_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells eq_refl);
      try reflexivity. 2: exact Hgr.
    cbn [edenot]. rewrite U35. subst data. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p3_run (zero carry : bool) fx R M (o sp n data x0 s1 : Z) :
  getr R (reg 2) = Z_to_bv 64 (sp - 96) -> getr R (reg 8) = Z_to_bv 64 o ->
  getr R (reg 9) = Z_to_bv 64 s1 -> getr R (reg 10) = Z_to_bv 64 n -> getr R (reg 11) = Z_to_bv 64 data -> getr R (reg 12) = Z_to_bv 64 x0 ->
  getr R (reg 13) = Z_to_bv 64 2 ->
  0 <= o < 2 ^ 64 -> 0 <= s1 < 2 ^ 64 -> 0 <= x0 < 2 ^ 64 -> 0 <= data < 2 ^ 64 ->
  (if zero then n = 1 else 2 <= n <= 2 ^ 23 + 1) ->
  (zero = false -> (if carry then s1 < x0 else x0 <= s1)) ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 96 <= sp -> sp <= 2 ^ 47 -> BG.writable M (sp - 96) 96 ->
  exists fx' R3, msteps RSEGS (st fx R BR3 M) (st fx' R3 (if (negb zero && carry)%bool then LOOP else TAIL) M)
    /\ (forall x, In x KS3 -> getr R3 (reg x) = getr R (reg x))
    /\ ((negb zero && carry)%bool = true -> getr R3 (reg 11) = Z_to_bv 64 (data + 8) /\ getr R3 (reg 12) = Z_to_bv 64 2).
Proof.
  intros H2 H8 H9 H10 H11 H12 H13 Ho Hs1 Hx0 Hdata Hn Hcy A16 SLO SHI WR.
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | 41%nat => Z_to_bv 64 s1 | 34%nat => Z_to_bv 64 n
                                         | 37%nat => Z_to_bv 64 data | 36%nat => Z_to_bv 64 x0 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (Hn': 1 <= n <= 2 ^ 23 + 1) by (destruct zero; lia).
  assert (U41: bv_unsigned (ev E 41) = s1) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = n) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U37: bv_unsigned (ev E 37) = data) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = x0) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (KS: forall K, In K [KRange (EVar 2) 140735332483168 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-96)) (ELit 96)] -> kentry_ok RSEGS E M K).
  { intros K HK. cbn in HK. repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BG.kentry_KRange_var. exact U2. lia.
    - eapply BG.kentry_KAlign_var. exact U2. lia. lia.
    - eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
  assert (KCY: zero = false -> kentry_ok RSEGS E M (KRange (EAlu ALU_SLTU (EVar 41) (EVar 36)) (if carry then 1 else 0) (if carry then 1 else 0))).
  { intros Hz. specialize (Hcy Hz). cbn [kentry_ok]. rewrite (BL.zeval_sound E (EAlu ALU_SLTU (EVar 41) (EVar 36)) (if s1 <? x0 then 1 else 0)).
    destruct carry; destruct (Z.ltb_spec s1 x0); lia.
    cbn [BL.zeval BL.zalu]. unfold BL.uv. rewrite U41, U36. reflexivity. }
  assert (POST: forall (fx' : FPState) E' (R' : bvmap 5 word) (M' : word -> option byte) (regs0 regs_out : list expr) (F0 : list SGP.region) (KSL : list nat) pc',
     regs_ok E regs0 R -> BG.kept_ok 48 regs0 regs_out KSL = true -> incl KS3 KSL -> env_agree 48 E E' ->
     (forall i e, In (i, e) (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (reg i) = edenot E' e) ->
     (forall a : word, SGP.outside E' F0 a -> M' a = M a) -> F0 = [] ->
     ((negb zero && carry)%bool = true -> nth 11 regs_out (ELit 0) = EAlu ALU_ADD (EVar 37) (ELit 8) /\ nth 12 regs_out (ELit 0) = ELit 2) ->
     mem_grows M M' -> msteps RSEGS (st fx R BR3 M) (st fx' R' pc' M') -> pc' = (if (negb zero && carry)%bool then LOOP else TAIL) ->
     exists fx'' R3, msteps RSEGS (st fx R BR3 M) (st fx'' R3 (if (negb zero && carry)%bool then LOOP else TAIL) M)
       /\ (forall x, In x KS3 -> getr R3 (reg x) = getr R (reg x))
       /\ ((negb zero && carry)%bool = true -> getr R3 (reg 11) = Z_to_bv 64 (data + 8) /\ getr R3 (reg 12) = Z_to_bv 64 2)).
  { intros fx' E' R' M' regs0 regs_out F0 KSL pc' HR KOK INCL Hag Hregs Hfr -> NLC Hgr Hms ->.
    assert (MM: M' = M). { apply functional_extensionality. intros a. apply Hfr. constructor. }
    rewrite MM in Hms. exists fx', R'. split. exact Hms.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    split. { intros j Hj. apply (BG.kept_regs E E' R R' regs0 regs_out 48 KSL KOK HR Hag Hregs j (INCL j Hj)). }
    intros HLC. destruct (NLC HLC) as [N11 N12].
    split. { rewrite (BG.out_reg regs_out E' R' 11 Hregs) by lia. rewrite N11. cbn [edenot]. rewrite AG by lia. rewrite (BG.word_of_unsigned _ _ U37), BG.alu_add_lit. reflexivity. }
    rewrite (BG.out_reg regs_out E' R' 12 Hregs) by lia. rewrite N12. reflexivity. }
  destruct zero.
  - assert (HR: regs_ok E P3Z.regs0 R).
    { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P3Z.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BG.alu_add_lit. exact H2. }
    assert (HK: know_ok RSEGS E M P3Z.kn0).
    { unfold know_ok. cbv delta [P3Z.kn0]. repeat (apply Forall_cons; [first [apply KS; cbn; tauto | eapply BG.kentry_KRange_var; [exact U34|lia]] |]). apply Forall_nil. }
    destruct (P3Z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BSHL.nth_error_single in Hnth. subst ps0. change P3Z.NX0 with 48%nat in Hag.
    apply (POST fx' E' R' M' P3Z.regs0 P3Z.regs_out P3Z.F0 KS3 _ HR KS3z_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl ltac:(cbn; intros; discriminate) Hgr Hms eq_refl).
  - destruct carry.
    + assert (HR: regs_ok E P3C.regs0 R).
      { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P3C.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BG.alu_add_lit. exact H2. }
      assert (HK: know_ok RSEGS E M P3C.kn0).
      { unfold know_ok. cbv delta [P3C.kn0]. repeat (apply Forall_cons; [first [apply KS; cbn; tauto | eapply BG.kentry_KRange_var; [exact U34|lia] | apply (KCY eq_refl)] |]). apply Forall_nil. }
      destruct (P3C.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
      apply BSHL.nth_error_single in Hnth. subst ps0. change P3C.NX0 with 48%nat in Hag.
      apply (POST fx' E' R' M' P3C.regs0 P3C.regs_out P3C.F0 KS3 _ HR KS3c_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl ltac:(cbn; intros; split; reflexivity) Hgr Hms eq_refl).
    + assert (HR: regs_ok E P3N.regs0 R).
      { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P3N.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BG.alu_add_lit. exact H2. }
      assert (HK: know_ok RSEGS E M P3N.kn0).
      { unfold know_ok. cbv delta [P3N.kn0]. repeat (apply Forall_cons; [first [apply KS; cbn; tauto | eapply BG.kentry_KRange_var; [exact U34|lia] | apply (KCY eq_refl)] |]). apply Forall_nil. }
      destruct (P3N.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
      apply BSHL.nth_error_single in Hnth. subst ps0. change P3N.NX0 with 48%nat in Hag.
      apply (POST fx' E' R' M' P3N.regs0 P3N.regs_out P3N.F0 KS3 _ HR KS3n_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl ltac:(cbn; intros; discriminate) Hgr Hms eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_ni : expr := EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit (-1)) (EVar 39)).      (* [comment removed for export] *)
Definition z_ni : BL.za := Eval vm_compute in (BL.zc e_ni).
Lemma z_ni_ok : BL.zcomp e_ni = Some z_ni. Proof. vm_compute. reflexivity. Qed.

Lemma iter_run (last wrap : bool) fx R M (sp o Q X : Z) (i n : nat) :
  getr R (reg 2) = Z_to_bv 64 (sp - 96) -> getr R (reg 8) = Z_to_bv 64 o -> 0 <= o < 2 ^ 64 -> 96 <= sp < 2 ^ 64 ->
  getr R (reg 10) = Z_to_bv 64 (Z.of_nat n) -> getr R (reg 11) = Z_to_bv 64 Q -> getr R (reg 12) = Z_to_bv 64 (Z.of_nat i) ->
  4096 <= Q -> Q + 8 <= 2 ^ 47 -> Q mod 8 = 0 ->
  (2 <= n <= 2 ^ 23 + 1)%nat -> (if last then i = n else 2 <= i < n)%nat ->
  BG.writable M Q 8 -> BG.u64_at M Q X -> 0 <= X < 2 ^ 64 -> (last = false -> (wrap = true <-> X = 2 ^ 64 - 1)) ->
  exists fx' R' M',
    msteps RSEGS (st fx R LOOP M) (st fx' R' (if (negb last && wrap)%bool then LOOP else TAIL) M')
    /\ (forall r, In r KSIT -> getr R' (reg r) = getr R (reg r))
    /\ (last = false -> getr R' (reg 11) = Z_to_bv 64 (Q + 8) /\ getr R' (reg 12) = Z_to_bv 64 (Z.of_nat i + 1))
    /\ BG.u64_at M' Q ((X + 1) mod 2 ^ 64)
    /\ (forall a : word, ~ (Q <= bv_unsigned a < Q + 8) -> M' a = M a)
    /\ mem_grows M M'.
Proof.
  intros H2 H8 Ho Hsp H10 H11 H12 Qlo Qhi Qal Hn Hi HW HX RX Hwrap.
  assert (Hi': (2 <= i <= n)%nat) by (destruct last; lia).
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | 32%nat => Z_to_bv 64 (Z.of_nat n) | 37%nat => Z_to_bv 64 Q
                                         | 39%nat => Z_to_bv 64 (Z.of_nat i) | 40%nat => Z_to_bv 64 X | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U32: bv_unsigned (ev E 32) = Z.of_nat n) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U37: bv_unsigned (ev E 37) = Q) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U39: bv_unsigned (ev E 39) = Z.of_nat i) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U40: bv_unsigned (ev E 40) = X) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (KC: forall K, In K [KRange (EVar 37) 4096 140737488355320; KAlign (EVar 37) 8; KWr (SA (EVar 37) 0) (ELit 8); KWord (SA (EVar 37) 0) 8 (EVar 40);
                             KRange (EVar 32) 2 8388609] -> kentry_ok RSEGS E M K).
  { intros K HK. cbn in HK. repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BG.kentry_KRange_var. exact U37. lia.
    - eapply BG.kentry_KAlign_var. exact U37. lia. lia.
    - eapply BG.kentry_KWr_var. exact U37. lia. lia. lia. rewrite Z.add_0_r. exact HW.
    - eapply BG.kentry_KWord_var. exact U37. exact U40. lia. lia. rewrite Z.add_0_r. exact HX.
    - eapply BG.kentry_KRange_var. exact U32. lia. }
  assert (KNL: last = false -> forall K, In K [KRange (EVar 39) 2 8388608; KRange e_ni 1 8388608] -> kentry_ok RSEGS E M K).
  { intros Hl K HK. rewrite Hl in Hi. cbn in HK. repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BG.kentry_KRange_var. exact U39. lia.
    - eapply (BG.kentry_KRange_z E M e_ni z_ni 1 8388608 (Z.of_nat n - Z.of_nat i) z_ni_ok). 2: lia.
      cbn [BL.zden z_ni]. unfold BL.uv. rewrite U32, U39. change 18446744073709551615 with (BL.MM - 1). first [apply BL.esub_val | apply BL.esub_val']. lia. unfold BL.MM; lia. }
  assert (POST: forall (fx' : FPState) E' (R' : bvmap 5 word) (M' : word -> option byte) (regs0 regs_out : list expr) (cells : list kentry) (F0 : list SGP.region) (ec : expr) (pc' : Z),
     regs_ok E regs0 R -> BG.kept_ok 48 regs0 regs_out KSIT = true -> env_agree 48 E E' ->
     (forall i e, In (i, e) (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (reg i) = edenot E' e) ->
     (forall a : word, SGP.outside E' F0 a -> M' a = M a) -> F0 = [(EVar 37, 0, ELit 8)] ->
     (forall K, In K cells -> kentry_ok RSEGS E' M' K) -> cells = [KWord (SA (EVar 37) 0) 8 ec] -> bv_unsigned (edenot E ec) = (X + 1) mod 2 ^ 64 -> expr_vars_lt 48 ec = true ->
     (last = false -> nth 11 regs_out (ELit 0) = EAlu ALU_ADD (EVar 37) (ELit 8) /\ nth 12 regs_out (ELit 0) = EAlu ALU_ADD (EVar 39) (ELit 1)) ->
     mem_grows M M' -> msteps RSEGS (st fx R LOOP M) (st fx' R' pc' M') -> pc' = (if (negb last && wrap)%bool then LOOP else TAIL) ->
     exists fx'' R'' M'',
       msteps RSEGS (st fx R LOOP M) (st fx'' R'' (if (negb last && wrap)%bool then LOOP else TAIL) M'')
       /\ (forall r, In r KSIT -> getr R'' (reg r) = getr R (reg r))
       /\ (last = false -> getr R'' (reg 11) = Z_to_bv 64 (Q + 8) /\ getr R'' (reg 12) = Z_to_bv 64 (Z.of_nat i + 1))
       /\ BG.u64_at M'' Q ((X + 1) mod 2 ^ 64)
       /\ (forall a : word, ~ (Q <= bv_unsigned a < Q + 8) -> M'' a = M a)
       /\ mem_grows M M'').
  { intros fx' E' R' M' regs0 regs_out cells F0 ec pc' HR KOK Hag Hregs Hfr -> Hcells -> Hec Hecv NL Hgr Hms ->.
    exists fx', R', M'. split. exact Hms.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (A37: bv_unsigned (ev E' 37) = Q) by (rewrite AG by lia; exact U37).
    split. { intros j Hj. apply (BG.kept_regs E E' R R' regs0 regs_out 48 KSIT KOK HR Hag Hregs j Hj). }
    split. { intros Hl. destruct (NL Hl) as [N11 N12].
             split. { rewrite (BG.out_reg regs_out E' R' 11 Hregs) by lia. rewrite N11. cbn [edenot]. rewrite AG by lia. rewrite (BG.word_of_unsigned _ _ U37), BG.alu_add_lit. reflexivity. }
             rewrite (BG.out_reg regs_out E' R' 12 Hregs) by lia. rewrite N12. cbn [edenot]. rewrite AG by lia. rewrite (BG.word_of_unsigned _ _ U39), BG.alu_add_lit. reflexivity. }
    split. { replace Q with (Q + 0) at 1 by lia. apply (BG.u64_of_KWord E' M' 37 0 ec Q). apply Hcells. left; reflexivity. exact A37.
             rewrite (BG.edenot_kept 48 E E') by (auto; exact Hecv). exact Hec. }
    split. { intros a Ha. apply Hfr. unfold SGP.outside. constructor; [|constructor]. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite A37. rewrite BG.unsigned_lit by lia. lia. }
    exact Hgr. }
  assert (SUM1: bv_unsigned (edenot E (EAlu ALU_ADD (EVar 40) (ELit 1))) = (X + 1) mod 2 ^ 64).
  { cbn [edenot]. rewrite (BG.word_of_unsigned _ _ U40), BG.alu_add_lit. rewrite Z_to_bv_unsigned. reflexivity. }
  destruct last.
  - (* [comment removed for export] *)
    subst i.
    assert (HR: regs_ok E PIN.regs0 R).
    { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl PIN.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BG.alu_add_lit. exact H2. }
    assert (HK: know_ok RSEGS E M PIN.kn0).
    { unfold know_ok. cbv delta [PIN.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | eapply BG.kentry_KRange_var; [exact U40|lia]] |]). apply Forall_nil. }
    destruct (PIN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & ix & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BSHL.nth_error_single in Hnth. subst ps0. change PIN.NX0 with 48%nat in Hag.
    apply (POST fx' E' R' M' PIN.regs0 PIN.regs_out PIN.cells PIN.F0 (EAlu ALU_ADD (EVar 40) (ELit 1)) _ HR KSIN_ok Hag Hregs Hfr eq_refl Hcells eq_refl SUM1 eq_refl ltac:(intros; discriminate) Hgr Hms eq_refl).
  - destruct wrap.
    + (* [comment removed for export] *)
      assert (EX: X = 2 ^ 64 - 1) by (apply (proj1 (Hwrap eq_refl)); reflexivity).
      assert (HR: regs_ok E PIT.regs0 R).
      { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl PIT.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BG.alu_add_lit. exact H2. }
      assert (HK: know_ok RSEGS E M PIT.kn0).
      { unfold know_ok. cbv delta [PIT.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply (KNL eq_refl); cbn; tauto | eapply BG.kentry_KRange_var; [exact U40|lia]] |]). apply Forall_nil. }
      destruct (PIT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & ix & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
      apply BSHL.nth_error_single in Hnth. subst ps0. change PIT.NX0 with 48%nat in Hag.
      apply (POST fx' E' R' M' PIT.regs0 PIT.regs_out PIT.cells PIT.F0 (ELit 0) _ HR KSIT_ok Hag Hregs Hfr eq_refl Hcells eq_refl
               ltac:(cbn [edenot]; rewrite BG.unsigned_lit by lia; rewrite EX; reflexivity) eq_refl ltac:(intros; split; reflexivity) Hgr Hms eq_refl).
    + (* [comment removed for export] *)
      assert (NX: X <> 2 ^ 64 - 1). { intros EX. pose proof (proj2 (Hwrap eq_refl) EX). discriminate. }
      assert (HR: regs_ok E PIC.regs0 R).
      { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl PIC.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BG.alu_add_lit. exact H2. }
      assert (HK: know_ok RSEGS E M PIC.kn0).
      { unfold know_ok. cbv delta [PIC.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply (KNL eq_refl); cbn; tauto | eapply BG.kentry_KRange_var; [exact U40|lia]] |]). apply Forall_nil. }
      destruct (PIC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & ix & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
      apply BSHL.nth_error_single in Hnth. subst ps0. change PIC.NX0 with 48%nat in Hag.
      apply (POST fx' E' R' M' PIC.regs0 PIC.regs_out PIC.cells PIC.F0 (EAlu ALU_ADD (EVar 40) (ELit 1)) _ HR KSIC_ok Hag Hregs Hfr eq_refl Hcells eq_refl SUM1 eq_refl ltac:(intros; split; reflexivity) Hgr Hms eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition limbs (M : word -> option byte) (q : Z) (f : nat -> Z) (lo hi : nat) : Prop :=
  forall j, (lo <= j < hi)%nat -> BG.u64_at M (q + 8 * Z.of_nat j) (f j).

Lemma limbs_frame M M' q f lo hi (a b : Z) :
  0 <= q -> q + 8 * Z.of_nat hi <= 2 ^ 64 ->
  (forall x : word, ~ (a <= bv_unsigned x < b) -> M' x = M x) ->
  (q + 8 * Z.of_nat hi <= a \/ b <= q + 8 * Z.of_nat lo) ->
  limbs M q f lo hi -> limbs M' q f lo hi.
Proof.
  intros Hq Hhi HF Hd HL j Hj. apply (BG.u64_at_frame M M'). lia. lia. 2: apply HL; auto.
  intros k Hk. apply HF. rewrite BG.unsigned_lit by lia. lia.
Qed.

Lemma mod8_add a k : a mod 8 = 0 -> (a + 8 * k) mod 8 = 0.
Proof. intros H. replace (a + 8 * k) with (a + k * 8) by lia. rewrite Z_mod_plus_full. exact H. Qed.

Lemma Wadd1_mod x : W.add x 1 = (x + 1) mod 2 ^ 64.
Proof. unfold W.add, W.wrap. rewrite M_val. reflexivity. Qed.

Lemma carry_run (k : nat) : forall (j : nat) fx R M (sp o data V d : Z) (len : nat),
  (j + k = len)%nat -> (1 <= j)%nat -> Z.of_nat len <= 2 ^ 23 -> 0 <= V < W.M ^ Z.of_nat len -> 0 <= d <= 9 ->
  4096 <= data -> data mod 8 = 0 -> data + 8 * (Z.of_nat len + 1) <= 2 ^ 47 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 96) -> getr R (reg 8) = Z_to_bv 64 o -> 0 <= o < 2 ^ 64 -> 96 <= sp < 2 ^ 64 ->
  getr R (reg 10) = Z_to_bv 64 (Z.of_nat len + 1) ->
  getr R (reg 11) = Z_to_bv 64 (data + 8 * Z.of_nat j) -> getr R (reg 12) = Z_to_bv 64 (Z.of_nat j + 1) ->
  acarry d V j = 1 ->
  BG.writable M data (8 * (Z.of_nat len + 1)) ->
  limbs M data (wordi (V + d)) 0 j -> limbs M data (wordi V) j (S len) ->
  exists fx' R' M',
    msteps RSEGS (st fx R LOOP M) (st fx' R' TAIL M')
    /\ (forall r, In r KSIT -> getr R' (reg r) = getr R (reg r))
    /\ limbs M' data (wordi (V + d)) 0 (S len)
    /\ (forall a : word, ~ (data + 8 * Z.of_nat j <= bv_unsigned a < data + 8 * (Z.of_nat len + 1)) -> M' a = M a)
    /\ mem_grows M M'.
Proof.
  induction k as [|k IH]; intros j fx R M sp o data V d len Hk Hj Hlen HV Hd Dlo Dal Dhi H2 H8 Ho Hsp H10 H11 H12 AC HW L1 L2.
  - (* [comment removed for export] *)
    assert (Ej: j = len) by lia. subst j.
    assert (WD: Z.of_nat len + 1 = Z.of_nat (len + 1)) by lia.
    assert (X0: wordi V len = 0). { apply wordi_high. lia. apply (proj2 (nwords_le_iff V len ltac:(lia))). lia. }
    destruct (iter_run true false fx R M sp o (data + 8 * Z.of_nat len) 0 (len + 1) (len + 1) H2 H8 Ho Hsp
                ltac:(rewrite <- WD; exact H10) H11 ltac:(rewrite H12; f_equal; lia) ltac:(lia) ltac:(lia)
                ltac:(apply mod8_add; exact Dal) ltac:(lia) ltac:(cbn; lia))
      as (fx' & R' & M' & Hms & Hkept & _ & Hcell & Hfr & Hgr).
    + intros dd m Hdd Hm. replace (data + 8 * Z.of_nat len + dd) with (data + (8 * Z.of_nat len + dd)) by lia. apply HW; lia.
    + rewrite <- X0. apply L2. lia.
    + lia.
    + intros; discriminate.
    + exists fx', R', M'. split. exact Hms. split. exact Hkept.
      split. { intros i Hi. destruct (Nat.eq_dec i len) as [->|NE].
               - rewrite <- (add_top_word d V len ltac:(unfold wordZ; rewrite M_val; lia) HV ltac:(lia)). rewrite AC. exact Hcell.
               - eapply (limbs_frame M M' data (wordi (V + d)) 0 len). lia. lia. exact Hfr. lia. exact L1. lia. }
      split. { intros a Ha. apply Hfr. lia. }
      exact Hgr.
  - (* [comment removed for export] *)
    pose proof (add_limbS d V j ltac:(unfold wordZ; rewrite M_val; lia) ltac:(lia) Hj) as STEP. cbn zeta in STEP. rewrite AC in STEP. cbn [Z.eqb] in STEP.
    destruct STEP as [SV SC]. rewrite Wadd1_mod in SV, SC.
    pose proof (wordi_range V j) as XR. unfold wordZ in XR. rewrite M_val in XR.
    destruct (Z.eq_dec (wordi V j) (2 ^ 64 - 1)) as [WRAP|NOWRAP].
    + (* [comment removed for export] *)
      destruct (iter_run false true fx R M sp o (data + 8 * Z.of_nat j) (wordi V j) (j + 1) (len + 1) H2 H8 Ho Hsp
                  ltac:(rewrite H10; f_equal; lia) H11 ltac:(rewrite H12; f_equal; lia) ltac:(lia) ltac:(lia)
                  ltac:(apply mod8_add; exact Dal) ltac:(lia) ltac:(cbn; lia))
        as (fx1 & R1 & M1 & Hms1 & Hkept1 & HN & Hcell & Hfr1 & Hgr1).
      * intros dd m Hdd Hm. replace (data + 8 * Z.of_nat j + dd) with (data + (8 * Z.of_nat j + dd)) by lia. apply HW; lia.
      * apply L2. lia.
      * lia.
      * intros _. split; intros; [exact WRAP|reflexivity].
      * destruct (HN eq_refl) as [R1_11 R1_12].
        assert (AC': acarry d V (S j) = 1). { rewrite SC. rewrite WRAP. reflexivity. }
        destruct (IH (S j) fx1 R1 M1 sp o data V d len ltac:(lia) ltac:(lia) Hlen HV Hd Dlo Dal Dhi) as (fx' & R' & M' & Hms & Hkept & LL & Hfr & Hgr).
        -- rewrite (Hkept1 2%nat) by (apply L5K.In_of_mem; reflexivity). exact H2.
        -- rewrite (Hkept1 8%nat) by (apply L5K.In_of_mem; reflexivity). exact H8.
        -- exact Ho. -- exact Hsp.
        -- rewrite (Hkept1 10%nat) by (apply L5K.In_of_mem; reflexivity). exact H10.
        -- rewrite R1_11. f_equal. lia.
        -- rewrite R1_12. f_equal. lia.
        -- exact AC'.
        -- change (L5.writable RSEGS M1 data (8 * (Z.of_nat len + 1))). eapply L5.writable_grows. exact Hgr1. exact HW.
        -- intros i Hi. destruct (Nat.eq_dec i j) as [->|NE].
           ++ rewrite <- SV. rewrite WRAP. replace ((2 ^ 64 - 1 + 1) mod 2 ^ 64) with ((wordi V j + 1) mod 2 ^ 64) by (rewrite WRAP; reflexivity). exact Hcell.
           ++ eapply (limbs_frame M M1 data (wordi (V + d)) 0 j). lia. lia. exact Hfr1. lia. exact L1. lia.
        -- eapply (limbs_frame M M1 data (wordi V) (S j) (S len)). lia. lia. exact Hfr1. lia. intros i Hi. apply L2. lia.
        -- exists fx', R', M'. split. eapply msteps_trans; eauto.
           split. { intros r Hr. rewrite Hkept by auto. apply Hkept1; auto. }
           split. exact LL.
           split. { intros a Ha. rewrite Hfr by lia. apply Hfr1. lia. }
           eapply mem_grows_trans; eauto.
    + (* [comment removed for export] *)
      destruct (iter_run false false fx R M sp o (data + 8 * Z.of_nat j) (wordi V j) (j + 1) (len + 1) H2 H8 Ho Hsp
                  ltac:(rewrite H10; f_equal; lia) H11 ltac:(rewrite H12; f_equal; lia) ltac:(lia) ltac:(lia)
                  ltac:(apply mod8_add; exact Dal) ltac:(lia) ltac:(cbn; lia))
        as (fx' & R' & M' & Hms & Hkept & _ & Hcell & Hfr & Hgr).
      * intros dd m Hdd Hm. replace (data + 8 * Z.of_nat j + dd) with (data + (8 * Z.of_nat j + dd)) by lia. apply HW; lia.
      * apply L2. lia.
      * lia.
      * intros _. split; intros HH; [discriminate|contradiction].
      * assert (AC0: acarry d V (S j) = 0).
        { rewrite SC. unfold W.b2z, W.ltu. destruct (Z.ltb_spec ((wordi V j + 1) mod 2 ^ 64) 1); [|reflexivity].
          exfalso. rewrite Z.mod_small in H by lia. lia. }
        exists fx', R', M'. split. exact Hms. split. exact Hkept.
        split. { intros i Hi. destruct (Nat.eq_dec i j) as [->|NE]. { rewrite <- SV. exact Hcell. }
                 destruct (lt_dec i j).
                 - eapply (limbs_frame M M' data (wordi (V + d)) 0 j). lia. lia. exact Hfr. lia. exact L1. lia.
                 - rewrite (proj1 (add_above_carry d V (S j) i ltac:(unfold wordZ; rewrite M_val; lia) ltac:(lia) ltac:(lia) AC0 ltac:(lia))).
                   eapply (limbs_frame M M' data (wordi V) (S j) (S len)). lia. lia. exact Hfr. lia. intros m Hm. apply L2. lia. lia. }
        split. { intros a Ha. apply Hfr. lia. }
        exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p4_run fx R M (o sp : Z) :
  getr R (reg 2) = Z_to_bv 64 (sp - 96) -> getr R (reg 8) = Z_to_bv 64 o -> 0 <= o < 2 ^ 64 ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 96 <= sp -> sp <= 2 ^ 47 -> BG.writable M (sp - 96) 96 ->
  exists fx' R3, msteps RSEGS (st fx R TAIL M) (st fx' R3 REDUCE M)
    /\ (forall x, In x KS4 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 RET2 /\ getr R3 (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R3 (reg 8) = Z_to_bv 64 o /\ getr R3 (reg 10) = Z_to_bv 64 o.
Proof.
  intros H2 H8 Ho A16 SLO SHI WR.
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (HR: regs_ok E P4.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P4.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BG.alu_add_lit. exact H2. }
  assert (HK: know_ok RSEGS E M P4.kn0).
  { unfold know_ok. cbv delta [P4.kn0].
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_nil. }
  destruct (P4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
  apply BSHL.nth_error_single in Hnth. subst ps0. change P4.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (MM: M' = M). { apply functional_extensionality. intros a. apply Hfr. constructor. }
  rewrite MM in Hms. exists fx', R'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' P4.regs0 P4.regs_out 48 KS4 KS4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg P4.regs_out E' R' 1 Hregs) by lia. reflexivity. }
  split. { rewrite (BG.out_reg P4.regs_out E' R' 2 Hregs) by lia. change (nth 2 P4.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-96))).
           cbn [edenot]. rewrite AG by lia. rewrite (BG.word_of_unsigned _ _ U2), BG.alu_add_lit. reflexivity. }
  split. { rewrite (BG.out_reg P4.regs_out E' R' 8 Hregs) by lia. change (nth 8 P4.regs_out (ELit 0)) with (EVar 35). cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U35. }
  rewrite (BG.out_reg P4.regs_out E' R' 10 Hregs) by lia. change (nth 10 P4.regs_out (ELit 0)) with (EVar 35). cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U35.
Qed.

Lemma p5_run fx R M (o sp c8 c16 c24 r : Z) :
  getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 2) = Z_to_bv 64 (sp - 96) ->
  BG.u64_at M (sp - 8) c8 -> BG.u64_at M (sp - 16) c16 -> BG.u64_at M (sp - 24) c24 ->
  0 <= c8 < 2 ^ 64 -> 0 <= c16 < 2 ^ 64 -> 0 <= c24 < 2 ^ 64 ->
  0 <= o < 2 ^ 64 -> sp mod 16 = 0 -> 0x7fff7f800000 + 96 <= sp -> sp <= 2 ^ 47 -> BG.writable M (sp - 96) 96 ->
  c8 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET2 M) (st fx' R3 r M3)
    /\ (forall x, In x KS5 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16 /\ getr R3 (reg 9) = Z_to_bv 64 c24
    /\ getr R3 (reg 10) = Z_to_bv 64 o
    /\ (forall a : word, M3 a = M a) /\ mem_grows M M3.
Proof.
  intros H8 H2 C8 C16 C24 R8 R16 R24 Ho A16 SLO SHI WR Er [Hr He].
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o
                                         | 41%nat => Z_to_bv 64 c8 | 42%nat => Z_to_bv 64 c16 | 43%nat => Z_to_bv 64 c24 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U41: bv_unsigned (ev E 41) = c8) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U42: bv_unsigned (ev E 42) = c16) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c24) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (HR: regs_ok E P5.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P5.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BG.alu_add_lit. exact H2. }
  assert (HK: know_ok RSEGS E M P5.kn0).
  { unfold know_ok. cbv delta [P5.kn0].
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U41. lia. lia. exact C8. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U42. lia. lia. exact C16. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C24. }
    apply Forall_nil. }
  destruct (P5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
  apply BSHL.nth_error_single in Hnth. subst ps0. change P5.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr. constructor. }
  assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i P5.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros j k z Hj Hnth Hk Hz. rewrite (BG.out_reg P5.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact Hz. }
  assert (R1: getr R' (reg 1) = Z_to_bv 64 c8). { apply (OUT 1%nat 41%nat); [lia | reflexivity | lia | exact U41]. }
  exists fx', R', M'. split.
  { eapply msteps_trans. exact Hms. change (SR.ps_pc P5.ps0) with RETI. apply ret_20eb4. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' P5.regs0 P5.regs_out 48 KS5 KS5_ok HR Hag Hregs j Hj). }
  split. exact R1.
  split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
  split. { apply (OUT 8%nat 42%nat); [lia | reflexivity | lia | exact U42]. }
  split. { apply (OUT 9%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
  split. { apply (OUT 10%nat 35%nat); [lia | reflexivity | lia | exact U35]. }
  split. exact MM. exact Hgr.
Qed.

End SCFG_1.
End L5ADDP.
