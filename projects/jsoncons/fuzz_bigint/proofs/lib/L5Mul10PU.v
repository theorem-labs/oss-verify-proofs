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
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore AsanPlanSoundSums Ub0Sums
     Ub0_code_21248_21b5c BigLinkBase BigLinkGlueUb0 BigLinkInlBaseU BigLinkDivBaseU BigLinkMulAlg BigLinkMul BigLinkMulU
     L5Defs L5Core L5CoreKit L5CoreKitU L5CoreSpecsU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5Mul10PU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigFactsBase BigFactsDigits.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5MULPU.
Import L5CSU.
Module P1D := LibSegZ_lcmu1d.
Module P1I := LibSegZ_lcmu1i.
Module PZD := LibSegZ_lcmu2zd.
Module PZI := LibSegZ_lcmu2zi.
Module PPD := LibSegZ_lcmu2pd.
Module PPI := LibSegZ_lcmu2pi.
Module PIT := LibSegZ_lcmuit.
Module PIL := LibSegZ_lcmuil.
Module P3 := LibSegZ_lcmu3.
Module P4 := LibSegZ_lcmu4.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition RET1 : Z := 0x21150.      (* [comment removed for export] *)
Definition LOOP : Z := 0x21188.      (* [comment removed for export] *)
Definition TAIL : Z := 0x21200.      (* [comment removed for export] *)
Definition RET2 : Z := 0x21218.      (* [comment removed for export] *)
Definition RETI : Z := 0x21248.      (* [comment removed for export] *)
Definition REDUCE : Z := 0x21abc.

Definition KS1 : list nat := Eval vm_compute in (BGU.kept_list 48 P1D.regs0 P1D.regs_out).
Lemma KS1d_ok : BGU.kept_ok 48 P1D.regs0 P1D.regs_out KS1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS1i_ok : BGU.kept_ok 48 P1I.regs0 P1I.regs_out KS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS2 : list nat := Eval vm_compute in (BGU.kept_list 48 PPD.regs0 PPD.regs_out).
Lemma KS2pd_ok : BGU.kept_ok 48 PPD.regs0 PPD.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS2pi_ok : BGU.kept_ok 48 PPI.regs0 PPI.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KSZ : list nat := Eval vm_compute in (BGU.kept_list 48 PZD.regs0 PZD.regs_out).
Lemma KSZd_ok : BGU.kept_ok 48 PZD.regs0 PZD.regs_out KSZ = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSZi_ok : BGU.kept_ok 48 PZI.regs0 PZI.regs_out KSZ = true. Proof. vm_compute. reflexivity. Qed.
Definition KSIT : list nat := Eval vm_compute in (BGU.kept_list 48 PIT.regs0 PIT.regs_out).
Lemma KSIT_ok : BGU.kept_ok 48 PIT.regs0 PIT.regs_out KSIT = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSIL_ok : BGU.kept_ok 48 PIL.regs0 PIL.regs_out KSIT = true. Proof. vm_compute. reflexivity. Qed.
Definition KS3 : list nat := Eval vm_compute in (BGU.kept_list 48 P3.regs0 P3.regs_out).
Lemma KS3_ok : BGU.kept_ok 48 P3.regs0 P3.regs_out KS3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS4 : list nat := Eval vm_compute in (BGU.kept_list 64 P4.regs0 P4.regs_out).
Lemma KS4_ok : BGU.kept_ok 64 P4.regs0 P4.regs_out KS4 = true. Proof. vm_compute. reflexivity. Qed.

Definition z8 : BL.za := Eval vm_compute in (BL.zc (ELit 8)).
Definition z32 : BL.za := Eval vm_compute in (BL.zc (ELit 32)).
Definition z96 : BL.za := Eval vm_compute in (BL.zc (ELit 96)).
Lemma z8_ok : BL.zcomp (ELit 8) = Some z8. Proof. vm_compute. reflexivity. Qed.
Lemma z32_ok : BL.zcomp (ELit 32) = Some z32. Proof. vm_compute. reflexivity. Qed.
Lemma z96_ok : BL.zcomp (ELit 96) = Some z96. Proof. vm_compute. reflexivity. Qed.

Lemma ret_21110 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RETI M) (st fx R r M).
Proof. intros H1 Hr He. apply (BDU.ret_to fx R M RETI W_21248 r F_21248 eq_refl D_21248 H1 Hr He). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p1_run (dyn : bool) fx R M (o sp fb len d x0 : Z) :
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 10 -> 4096 <= o -> o mod 8 = 0 ->
  getr R (reg 2) = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0x7fff7f800000 + 96 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 96) 96 ->
  sp <= o -> o + 32 <= 2 ^ 47 ->
  BGU.u8_at M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = dyn -> BGU.u64_at M (o + 8) len -> 0 <= len < 2 ^ 64 ->
  (dyn = true -> BGU.u64_at M (o + 24) d /\ 4096 <= d /\ d + 8 <= sp - 96 /\ d mod 8 = 0) -> (dyn = false -> d = o + 16) ->
  BGU.u64_at M d x0 -> 0 <= x0 < 2 ^ 64 ->
  exists fx' R1 M1, msteps RSEGS (st fx R MUL10 M) (st fx' R1 RESIZE M1)
    /\ (forall x, In x KS1 -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 1) = Z_to_bv 64 RET1 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 96)
    /\ getr R1 (reg 8) = Z_to_bv 64 o /\ getr R1 (reg 9) = Z_to_bv 64 len /\ getr R1 (reg 10) = Z_to_bv 64 o /\ getr R1 (reg 11) = Z_to_bv 64 (len + 1)
    /\ getr R1 (reg 19) = Z_to_bv 64 10 /\ getr R1 (reg 20) = Z_to_bv 64 x0
    /\ BGU.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BGU.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8)))
    /\ BGU.u64_at M1 (sp - 24) (bv_unsigned (getr R (reg 9))) /\ BGU.u64_at M1 (sp - 32) (bv_unsigned (getr R (reg 18)))
    /\ BGU.u64_at M1 (sp - 40) (bv_unsigned (getr R (reg 19))) /\ BGU.u64_at M1 (sp - 48) (bv_unsigned (getr R (reg 20)))
    /\ BGU.u64_at M1 (sp - 56) (bv_unsigned (getr R (reg 21))) /\ BGU.u64_at M1 (sp - 64) (bv_unsigned (getr R (reg 22)))
    /\ BGU.u64_at M1 (sp - 72) (bv_unsigned (getr R (reg 23))) /\ BGU.u64_at M1 (sp - 80) (bv_unsigned (getr R (reg 24)))
    /\ (forall a : word, ~ (sp - 96 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H10 H11 Olo Ao H2 A16 SLO SHI WR Oge Ohi O0 Hfb Bfb O8 Hlen HD HI OX Hx0.
  assert (Dlo: 4096 <= d /\ d + 8 <= 2 ^ 47 /\ d mod 8 = 0).
  { destruct dyn. destruct (HD eq_refl) as (_ & D1 & D2 & D3). lia. rewrite (HI eq_refl). split. lia. split. lia. rewrite <- Z.add_mod_idemp_l by lia. rewrite Ao. reflexivity. }
  set (Vf := fun k : nat => match k with 33%nat => Z_to_bv 64 fb | 34%nat => Z_to_bv 64 len | 36%nat => Z_to_bv 64 x0 | 37%nat => Z_to_bv 64 d | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BGU.unsigned_lit; lia).
  assert (U10: bv_unsigned (ev E 10) = o) by (cbv [E ev Vf]; rewrite H10; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = len) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = x0) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U37: bv_unsigned (ev E 37) = d) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (LO: Z.land fb 1 = (if dyn then 1 else 0)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
    destruct (Z.eq_dec i 0) as [->|Hi0]. { rewrite Bfb. destruct dyn; reflexivity. }
    replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r.
    destruct dyn. symmetry; apply Z.bits_above_log2; cbn; lia. rewrite Z.bits_0. reflexivity. }
  assert (KC: forall K, In K
    [KRange (EVar 2) 140735332483168 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-96)) (ELit 96);
     KRange (EVar 10) 4096 140737488355328; KAlign (EVar 10) 8;
     KDisj (SA (EVar 10) 0) (ELit 32) (SA (EVar 2) (-96)) (ELit 96);
     KWord (SA (EVar 10) 0) 1 (EVar 33); KRange (EVar 33) 0 255; KWord (SA (EVar 10) 8) 8 (EVar 34)] -> kentry_ok RSEGS E M K).
  { intros K HK. cbn in HK.
    repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BGU.kentry_KRange_var. exact U2. lia.
    - eapply BGU.kentry_KAlign_var. exact U2. lia. lia.
    - eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR.
    - eapply BGU.kentry_KRange_var. exact U10. lia.
    - eapply BGU.kentry_KAlign_var. exact U10. lia. lia.
    - eapply (BGU.kentry_KDisj_z E M 10 0 (ELit 32) z32 32 2 (-96) (ELit 96) z96 96 o sp U10 U2 z32_ok eq_refl z96_ok eq_refl). lia.
    - eapply (BDU.kentry_KWord1_var E M 10 0 33 o fb U10 U33). lia. lia. lia. rewrite Z.add_0_r. exact O0.
    - eapply BGU.kentry_KRange_var. exact U33. lia.
    - eapply BGU.kentry_KWord_var. exact U10. exact U34. lia. lia. exact O8. }
  assert (KO: forall v, Z.land fb 1 = v -> kentry_ok RSEGS E M (KRange (EAlu ALU_AND (EVar 33) (ELit 1)) v v)).
  { intros v Hv. cbn [kentry_ok edenot]. rewrite BDU.and_lit_val by lia. rewrite U33, Hv. lia. }
  assert (KD: dyn = true -> forall K, In K [KWord (SA (EVar 10) 24) 8 (EVar 37); KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 8;
                                            KWord (SA (EVar 37) 0) 8 (EVar 36); KDisj (SA (EVar 37) 0) (ELit 8) (SA (EVar 2) (-96)) (ELit 96)] -> kentry_ok RSEGS E M K).
  { intros Hd K HK. destruct (HD Hd) as (O24 & D1 & D2 & D3). cbn in HK.
    repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BGU.kentry_KWord_var. exact U10. exact U37. lia. lia. exact O24.
    - eapply BGU.kentry_KRange_var. exact U37. lia.
    - eapply BGU.kentry_KAlign_var. exact U37. lia. lia.
    - eapply BGU.kentry_KWord_var. exact U37. exact U36. lia. lia. rewrite Z.add_0_r. exact OX.
    - eapply (BGU.kentry_KDisj_z E M 37 0 (ELit 8) z8 8 2 (-96) (ELit 96) z96 96 d sp U37 U2 z8_ok eq_refl z96_ok eq_refl). lia. }
  assert (KI: dyn = false -> kentry_ok RSEGS E M (KWord (SA (EVar 10) 16) 8 (EVar 36))).
  { intros Hd. eapply BGU.kentry_KWord_var. exact U10. exact U36. lia. lia. rewrite <- (HI Hd). exact OX. }
  assert (HRX: forall regs0, regs0 = P1D.regs0 -> regs_ok E regs0 R).
  { intros regs0 ->. apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P1D.regs0 nth edenot ev E Vf]. repeat split; try reflexivity. exact H11. }
  assert (SAME: P1I.regs0 = P1D.regs0) by reflexivity.
  assert (POST: forall (fx' : FPState) E' (R' : bvmap 5 word) (M' : word -> option byte) (regs0 regs_out : list expr) (cells : list kentry) (F0 : list SGP.region) (KSL : list nat),
     regs0 = P1D.regs0 -> BGU.kept_ok 48 regs0 regs_out KSL = true -> incl KS1 KSL ->
     env_agree 48 E E' ->
     (forall i e, In (i, e) (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (reg i) = edenot E' e) ->
     (forall a : word, SGP.outside E' F0 a -> M' a = M a) -> F0 = [(EVar 2, -96, ELit 96)] ->
     (forall K, In K cells -> kentry_ok RSEGS E' M' K) -> cells = P1D.cells -> regs_out = P1D.regs_out ->
     mem_grows M M' ->
     (forall x, In x KS1 -> getr R' (reg x) = getr R (reg x))
     /\ getr R' (reg 1) = Z_to_bv 64 RET1 /\ getr R' (reg 2) = Z_to_bv 64 (sp - 96)
     /\ getr R' (reg 8) = Z_to_bv 64 o /\ getr R' (reg 9) = Z_to_bv 64 len /\ getr R' (reg 10) = Z_to_bv 64 o /\ getr R' (reg 11) = Z_to_bv 64 (len + 1)
     /\ getr R' (reg 19) = Z_to_bv 64 10 /\ getr R' (reg 20) = Z_to_bv 64 x0
     /\ BGU.u64_at M' (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BGU.u64_at M' (sp - 16) (bv_unsigned (getr R (reg 8)))
     /\ BGU.u64_at M' (sp - 24) (bv_unsigned (getr R (reg 9))) /\ BGU.u64_at M' (sp - 32) (bv_unsigned (getr R (reg 18)))
     /\ BGU.u64_at M' (sp - 40) (bv_unsigned (getr R (reg 19))) /\ BGU.u64_at M' (sp - 48) (bv_unsigned (getr R (reg 20)))
     /\ BGU.u64_at M' (sp - 56) (bv_unsigned (getr R (reg 21))) /\ BGU.u64_at M' (sp - 64) (bv_unsigned (getr R (reg 22)))
     /\ BGU.u64_at M' (sp - 72) (bv_unsigned (getr R (reg 23))) /\ BGU.u64_at M' (sp - 80) (bv_unsigned (getr R (reg 24)))
     /\ (forall a : word, ~ (sp - 96 <= bv_unsigned a < sp) -> M' a = M a) /\ mem_grows M M').
  { intros fx' E' R' M' regs0 regs_out cells F0 KSL -> KOK INCL Hag Hregs Hfr -> Hcells -> -> Hgr.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
    assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i P1D.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
    { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg P1D.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
    assert (CELL: forall off k, In (KWord (SA (EVar 2) off) 8 (EVar k)) P1D.cells -> (k < 32)%nat -> Vf k = getr R (reg k) -> BGU.u64_at M' (sp + off) (bv_unsigned (getr R (reg k)))).
    { intros off k Hin Hk HV. eapply (BGU.u64_of_KWord E' M' 2 off). apply Hcells. exact Hin. exact A2.
      cbn [edenot]. rewrite AG by lia. change (ev E k) with (Vf k). rewrite HV. reflexivity. }
    split. { intros j Hj. apply (BGU.kept_regs E E' R R' P1D.regs0 P1D.regs_out 48 KSL KOK (HRX _ eq_refl) Hag Hregs j (INCL j Hj)). }
    split. { rewrite (BGU.out_reg P1D.regs_out E' R' 1 Hregs) by lia. reflexivity. }
    split. { rewrite (BGU.out_reg P1D.regs_out E' R' 2 Hregs) by lia. change (nth 2 P1D.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-96))).
             cbn [edenot]. rewrite (BGU.word_of_unsigned _ _ A2), BGU.alu_add_lit. reflexivity. }
    split. { apply (OUT 8%nat 10%nat); [lia | reflexivity | lia | exact U10]. }
    split. { apply (OUT 9%nat 34%nat); [lia | reflexivity | lia | exact U34]. }
    split. { apply (OUT 10%nat 10%nat); [lia | reflexivity | lia | exact U10]. }
    split. { rewrite (BGU.out_reg P1D.regs_out E' R' 11 Hregs) by lia. change (nth 11 P1D.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 34) (ELit 1)).
             cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U34), BGU.alu_add_lit. reflexivity. }
    split. { rewrite (BGU.out_reg P1D.regs_out E' R' 19 Hregs) by lia. reflexivity. }
    split. { apply (OUT 20%nat 36%nat); [lia | reflexivity | lia | exact U36]. }
    split. { replace (sp - 8) with (sp + -8) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 16) with (sp + -16) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 24) with (sp + -24) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 32) with (sp + -32) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 40) with (sp + -40) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 48) with (sp + -48) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 56) with (sp + -56) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 64) with (sp + -64) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 72) with (sp + -72) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 80) with (sp + -80) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { intros a Ha. apply Hfr. unfold SGP.outside.
             constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
    exact Hgr. }
  destruct dyn.
  - assert (HK: know_ok RSEGS E M P1D.kn0).
    { unfold know_ok. cbv delta [P1D.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KO; exact LO | apply (KD eq_refl); cbn; tauto] |]). apply Forall_nil. }
    destruct (P1D.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' P1D.regs0 P1D.regs_out P1D.cells P1D.F0 KS1 eq_refl KS1d_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells eq_refl eq_refl Hgr).
  - assert (HK: know_ok RSEGS E M P1I.kn0).
    { unfold know_ok. cbv delta [P1I.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KO; exact LO | apply (KI eq_refl)] |]). apply Forall_nil. }
    destruct (P1I.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' P1I.regs0 P1I.regs_out P1I.cells P1I.F0 KS1 eq_refl KS1i_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells eq_refl eq_refl Hgr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_ret1 (R : bvmap 5 word) (M : word -> option byte) (o x0 len sp c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 : Z) : Prop :=
  getr R (reg 8) = Z_to_bv 64 o /\ getr R (reg 9) = Z_to_bv 64 len /\ getr R (reg 19) = Z_to_bv 64 10 /\ getr R (reg 20) = Z_to_bv 64 x0 /\
  getr R (reg 2) = Z_to_bv 64 (sp - 96) /\
  BGU.u64_at M (sp - 8) c8 /\ BGU.u64_at M (sp - 16) c16 /\ BGU.u64_at M (sp - 24) c24 /\ BGU.u64_at M (sp - 32) c32 /\ BGU.u64_at M (sp - 40) c40 /\
  BGU.u64_at M (sp - 48) c48 /\ BGU.u64_at M (sp - 56) c56 /\ BGU.u64_at M (sp - 64) c64 /\ BGU.u64_at M (sp - 72) c72 /\ BGU.u64_at M (sp - 80) c80 /\
  0 <= c8 < 2 ^ 64 /\ 0 <= c16 < 2 ^ 64 /\ 0 <= c24 < 2 ^ 64 /\ 0 <= c32 < 2 ^ 64 /\ 0 <= c40 < 2 ^ 64 /\
  0 <= c48 < 2 ^ 64 /\ 0 <= c56 < 2 ^ 64 /\ 0 <= c64 < 2 ^ 64 /\ 0 <= c72 < 2 ^ 64 /\ 0 <= c80 < 2 ^ 64.

(* [comment removed for export] *)
Lemma p2_run (td zero : bool) fx R M (o x0 len sp c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 f qd nl : Z) :
  at_ret1 R M o x0 len sp c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 -> 0 <= o -> o + 32 <= 2 ^ 47 -> 0 <= x0 < 2 ^ 64 ->
  (if zero then len = 0 else 1 <= len <= 2 ^ 23) ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 96 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 96) 96 ->
  o mod 8 = 0 -> sp <= o ->
  BGU.u8_at M o f -> 0 <= f < 256 -> Z.testbit f 0 = td -> (td = true -> BGU.u64_at M (o + 24) qd /\ 4096 <= qd < 2 ^ 47 /\ qd mod 8 = 0) ->
  BGU.u64_at M (o + 8) nl -> 0 <= nl < 2 ^ 64 ->
  let data := if td then qd else o + 16 in
  exists fx' R3 M3, msteps RSEGS (st fx R RET1 M) (st fx' R3 (if zero then TAIL else LOOP) M3)
    /\ (forall x, In x KS2 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R3 (reg 8) = Z_to_bv 64 o /\ getr R3 (reg 9) = Z_to_bv 64 len
    /\ (zero = false -> getr R3 (reg 18) = Z_to_bv 64 0 /\ getr R3 (reg 21) = Z_to_bv 64 10)
    /\ getr R3 (reg 20) = Z_to_bv 64 x0 /\ getr R3 (reg 22) = Z_to_bv 64 0
    /\ BGU.u64_at M3 (sp - 96) data /\ BGU.u64_at M3 (sp - 88) nl
    /\ (forall a : word, ~ (sp - 96 <= bv_unsigned a < sp - 80) -> M3 a = M a) /\ mem_grows M M3.
Proof.
  intros (H8 & H9 & H19 & H20 & H2 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & R8 & R16 & R24 & R32 & R40 & R48 & R56 & R64 & R72 & R80)
         Olo Ohi Hx0 Hlen A16 SLO SHI WR Ao Oge O0 Hf Bf HQ ONL Hnl.
  assert (QD: 0 <= qd < 2 ^ 64 \/ td = false). { destruct td. left. destruct (HQ eq_refl) as (_ & X & _). lia. right; reflexivity. }
  set (qd' := if td then qd else 0).
  assert (Hq': 0 <= qd' < 2 ^ 64). { subst qd'. destruct td. destruct QD as [X|X]. lia. discriminate. lia. }
  assert (Hlen': 0 <= len <= 2 ^ 23) by (destruct zero; lia).
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | 36%nat => Z_to_bv 64 x0 | 34%nat => Z_to_bv 64 len
                                         | 38%nat => Z_to_bv 64 f | 39%nat => Z_to_bv 64 qd' | 40%nat => Z_to_bv 64 nl | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = x0) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = len) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U38: bv_unsigned (ev E 38) = f) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U39: bv_unsigned (ev E 39) = qd') by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U40: bv_unsigned (ev E 40) = nl) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (LT: Z.land f 1 = (if td then 1 else 0)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
    destruct (Z.eq_dec i 0) as [->|Hi0]. { rewrite Bf. destruct td; reflexivity. }
    replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r.
    destruct td. symmetry; apply Z.bits_above_log2; cbn; lia. rewrite Z.bits_0. reflexivity. }
  assert (KC: forall K, In K
    [KRange (EVar 2) 140735332483168 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-96)) (ELit 96);
     KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 8;
     KDisj (SA (EVar 35) 0) (ELit 32) (SA (EVar 2) (-96)) (ELit 96);
     KRange (EVar 34) 1 8388608;
     KWord (SA (EVar 35) 0) 1 (EVar 38); KRange (EVar 38) 0 255; KWord (SA (EVar 35) 8) 8 (EVar 40)] -> (K = KRange (EVar 34) 1 8388608 -> zero = false) -> kentry_ok RSEGS E M K).
  { intros K HK HZ. cbn in HK.
    repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BGU.kentry_KRange_var. exact U2. lia.
    - eapply BGU.kentry_KAlign_var. exact U2. lia. lia.
    - eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR.
    - eapply BGU.kentry_KRange_var. exact U35. lia.
    - eapply BGU.kentry_KAlign_var. exact U35. lia. lia.
    - eapply (BGU.kentry_KDisj_z E M 35 0 (ELit 32) z32 32 2 (-96) (ELit 96) z96 96 o sp U35 U2 z32_ok eq_refl z96_ok eq_refl). lia.
    - specialize (HZ eq_refl). subst zero. eapply BGU.kentry_KRange_var. exact U34. lia.
    - eapply (BDU.kentry_KWord1_var E M 35 0 38 o f U35 U38). lia. lia. lia. rewrite Z.add_0_r. exact O0.
    - eapply BGU.kentry_KRange_var. exact U38. lia.
    - eapply BGU.kentry_KWord_var. exact U35. exact U40. lia. lia. exact ONL. }
  assert (KT: forall v, Z.land f 1 = v -> kentry_ok RSEGS E M (KRange (EAlu ALU_AND (EVar 38) (ELit 1)) v v)).
  { intros v Hv. cbn [kentry_ok edenot]. rewrite BDU.and_lit_val by lia. rewrite U38, Hv. lia. }
  assert (KQ: td = true -> forall K, In K [KWord (SA (EVar 35) 24) 8 (EVar 39); KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 8] -> kentry_ok RSEGS E M K).
  { intros Htd K HK. destruct (HQ Htd) as (O24 & Q1 & Q2). assert (Eq: qd' = qd) by (subst qd'; rewrite Htd; reflexivity). cbn in HK.
    repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BGU.kentry_KWord_var. exact U35. exact U39. lia. lia. rewrite Eq. exact O24.
    - eapply BGU.kentry_KRange_var. exact U39. rewrite Eq. lia.
    - eapply BGU.kentry_KAlign_var. exact U39. lia. rewrite Eq. lia. }
  assert (HRX: forall regs0, regs0 = (if zero then PZD.regs0 else PPD.regs0) -> regs_ok E regs0 R).
  { intros regs0 ->. destruct zero.
    - apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PZD.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
      rewrite BGU.alu_add_lit. exact H2. rewrite H9, Hlen. reflexivity.
    - apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PPD.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
      rewrite BGU.alu_add_lit. exact H2. }
  assert (SAME: PZI.regs0 = PZD.regs0 /\ PPI.regs0 = PPD.regs0) by (split; reflexivity).
  assert (Edata: (if td then qd' else o + 16) = (if td then qd else o + 16)). { subst qd'. destruct td; reflexivity. }
  assert (POST: forall (fx' : FPState) E' (R' : bvmap 5 word) (M' : word -> option byte) (regs0 regs_out : list expr) (cells : list kentry) (F0 : list SGP.region) (KSL : list nat),
     regs0 = (if zero then PZD.regs0 else PPD.regs0) -> BGU.kept_ok 48 regs0 regs_out KSL = true -> incl KS2 KSL ->
     env_agree 48 E E' ->
     (forall i e, In (i, e) (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (reg i) = edenot E' e) ->
     (forall a : word, SGP.outside E' F0 a -> M' a = M a) -> F0 = [(EVar 2, -96, ELit 16)] ->
     (forall K, In K cells -> kentry_ok RSEGS E' M' K) ->
     cells = [KWord (SA (EVar 2) (-88)) 8 (EVar 40); KWord (SA (EVar 2) (-96)) 8 (if td then EVar 39 else EAlu ALU_ADD (EVar 35) (ELit 16))] ->
     nth 2 regs_out (ELit 0) = EAlu ALU_ADD (EVar 2) (ELit (-96)) -> nth 8 regs_out (ELit 0) = EVar 35 ->
     nth 9 regs_out (ELit 0) = (if zero then ELit 0 else EVar 34) ->
     (zero = false -> nth 18 regs_out (ELit 0) = ELit 0 /\ nth 21 regs_out (ELit 0) = ELit 10) ->
     nth 20 regs_out (ELit 0) = EVar 36 -> nth 22 regs_out (ELit 0) = ELit 0 ->
     mem_grows M M' ->
     (forall x, In x KS2 -> getr R' (reg x) = getr R (reg x))
     /\ getr R' (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R' (reg 8) = Z_to_bv 64 o /\ getr R' (reg 9) = Z_to_bv 64 len
     /\ (zero = false -> getr R' (reg 18) = Z_to_bv 64 0 /\ getr R' (reg 21) = Z_to_bv 64 10)
     /\ getr R' (reg 20) = Z_to_bv 64 x0 /\ getr R' (reg 22) = Z_to_bv 64 0
     /\ BGU.u64_at M' (sp - 96) (if td then qd else o + 16) /\ BGU.u64_at M' (sp - 88) nl
     /\ (forall a : word, ~ (sp - 96 <= bv_unsigned a < sp - 80) -> M' a = M a) /\ mem_grows M M').
  { intros fx' E' R' M' regs0 regs_out cells F0 KSL -> KOK INCL Hag Hregs Hfr -> Hcells -> N2 N8 N9 NL N20 N22 Hgr.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
    assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
    { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
    split. { intros j Hj. apply (BGU.kept_regs E E' R R' _ regs_out 48 KSL KOK (HRX _ eq_refl) Hag Hregs j (INCL j Hj)). }
    split. { rewrite (BGU.out_reg regs_out E' R' 2 Hregs) by lia. rewrite N2. cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U2), BGU.alu_add_lit. reflexivity. }
    split. { apply (OUT 8%nat 35%nat); [lia | exact N8 | lia | exact U35]. }
    split. { rewrite (BGU.out_reg regs_out E' R' 9 Hregs) by lia. rewrite N9. destruct zero. rewrite Hlen. reflexivity.
             cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U34. }
    split. { intros Hz. destruct (NL Hz) as (N18 & N21).
             split. rewrite (BGU.out_reg regs_out E' R' 18 Hregs) by lia. rewrite N18. reflexivity.
             rewrite (BGU.out_reg regs_out E' R' 21 Hregs) by lia. rewrite N21. reflexivity. }
    split. { apply (OUT 20%nat 36%nat); [lia | exact N20 | lia | exact U36]. }
    split. { rewrite (BGU.out_reg regs_out E' R' 22 Hregs) by lia. rewrite N22. reflexivity. }
    split. { replace (sp - 96) with (sp + -96) by lia. eapply (BGU.u64_of_KWord_e E' M' (EVar 2) (-96)). apply Hcells. right; left; reflexivity. cbn [edenot]. exact A2.
             rewrite <- Edata. destruct td. cbn [edenot]. rewrite AG by lia. exact U39.
             cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U35), BGU.alu_add_lit. apply BGU.unsigned_lit. lia. }
    split. { replace (sp - 88) with (sp + -88) by lia. eapply (BGU.u64_of_KWord E' M' 2 (-88)). apply Hcells. left; reflexivity. exact A2. cbn [edenot]. rewrite AG by lia. exact U40. }
    split. { intros a Ha. apply Hfr. unfold SGP.outside. constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
    exact Hgr. }
  destruct zero; destruct td.
  - assert (HK: know_ok RSEGS E M PZD.kn0).
    { unfold know_ok. cbv delta [PZD.kn0]. repeat (apply Forall_cons; [first [apply KC; [cbn; tauto | intros; discriminate] | apply KT; exact LT | apply (KQ eq_refl); cbn; tauto] |]). apply Forall_nil. }
    destruct (PZD.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' PZD.regs0 PZD.regs_out PZD.cells PZD.F0 KS2 eq_refl KSZd_ok ltac:(intros x Hx; L5K.inlist Hx) Hag Hregs Hfr eq_refl Hcells); try reflexivity. intros; discriminate. exact Hgr.
  - assert (HK: know_ok RSEGS E M PZI.kn0).
    { unfold know_ok. cbv delta [PZI.kn0]. repeat (apply Forall_cons; [first [apply KC; [cbn; tauto | intros; discriminate] | apply KT; exact LT] |]). apply Forall_nil. }
    destruct (PZI.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' PZI.regs0 PZI.regs_out PZI.cells PZI.F0 KS2 eq_refl KSZi_ok ltac:(intros x Hx; L5K.inlist Hx) Hag Hregs Hfr eq_refl Hcells); try reflexivity. intros; discriminate. exact Hgr.
  - assert (HK: know_ok RSEGS E M PPD.kn0).
    { unfold know_ok. cbv delta [PPD.kn0]. repeat (apply Forall_cons; [first [apply KC; [cbn; tauto | reflexivity] | apply KT; exact LT | apply (KQ eq_refl); cbn; tauto] |]). apply Forall_nil. }
    destruct (PPD.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' PPD.regs0 PPD.regs_out PPD.cells PPD.F0 KS2 eq_refl KS2pd_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells); try reflexivity. intros _; split; reflexivity. exact Hgr.
  - assert (HK: know_ok RSEGS E M PPI.kn0).
    { unfold know_ok. cbv delta [PPI.kn0]. repeat (apply Forall_cons; [first [apply KC; [cbn; tauto | reflexivity] | apply KT; exact LT] |]). apply Forall_nil. }
    destruct (PPI.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' PPI.regs0 PPI.regs_out PPI.cells PPI.F0 KS2 eq_refl KS2pi_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells); try reflexivity. intros _; split; reflexivity. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_qI : expr := EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit 8) (EVar 40)).         (* [comment removed for export] *)
Definition e_qn : expr := EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 33)) (EVar 35).         (* [comment removed for export] *)
Definition e_bl : expr := EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 33)) (ELit 8).            (* [comment removed for export] *)
Definition e_nI : expr := EAlu ALU_ADD (EVar 33) (EMd M_MUL (ELit (-1)) (EVar 40)).      (* [comment removed for export] *)
Definition ITER7 : list kentry :=
  [KRange (EVar 2) 140735332483168 140737488355328; KAlign (EVar 2) 16; KWord (SA (EVar 2) (-96)) 8 (EVar 35);
   KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 8; KRange e_qn 4096 140737488355320;
   KDisj (SA (EVar 2) (-96)) (ELit 96) (SA (EVar 35) 0) e_bl].
Lemma kn0_IT : PIT.kn0 = ITER7 ++ [KRange (EVar 33) 1 8388608; KRange (EVar 40) 0 8388608; KRange e_nI 2 8388608; KWr (SA e_qI 0) (ELit 8); KWord (SA e_qI 8) 8 (EVar 36)].
Proof. vm_compute. reflexivity. Qed.
Lemma kn0_IL : PIL.kn0 = ITER7 ++ [KRange (EVar 33) 1 8388608; KRange (EVar 40) 0 8388608; KRange e_nI 1 1; KWr (SA e_qI 0) (ELit 8); KWord (SA e_qI 8) 8 (EVar 36)].
Proof. vm_compute. reflexivity. Qed.
Lemma cells_IT : PIT.cells = [KWord (SA e_qI 0) 8 BMU.t_lo]. Proof. vm_compute. reflexivity. Qed.
Lemma cells_IL : PIL.cells = [KWord (SA e_qI 0) 8 BMU.t_lo]. Proof. vm_compute. reflexivity. Qed.
Lemma F0_IT : PIT.F0 = [(e_qI, 0, ELit 8)]. Proof. vm_compute. reflexivity. Qed.
Lemma F0_IL : PIL.F0 = [(e_qI, 0, ELit 8)]. Proof. vm_compute. reflexivity. Qed.
Lemma t_car_IT : nth 22 PIT.regs_out (ELit 0) = BMU.t_car. Proof. vm_compute. reflexivity. Qed.
Lemma t_car_IL : nth 22 PIL.regs_out (ELit 0) = BMU.t_car. Proof. vm_compute. reflexivity. Qed.

Lemma kentry_KWr_e E M b off (a n : Z) :
  bv_unsigned (edenot E b) = a -> 0 <= a + off -> 0 < n < 2 ^ 64 -> a + off + n <= 2 ^ 64 ->
  BGU.writable M (a + off) n -> kentry_ok RSEGS E M (KWr (SA b off) (ELit n)).
Proof.
  intros Ha H1 H2 H3 Hw. cbn [kentry_ok]. unfold flat, elenZ. change (estart E (SA b off)) with (bv_unsigned (edenot E b) + off). rewrite Ha. cbn [edenot].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
  split. lia. intros d m Hd Hm. apply Hw; lia.
Qed.
Lemma kentry_KDisj_e E M b1 off1 n1e (n1 : Z) b2 off2 n2e (n2 a1 a2 : Z) :
  bv_unsigned (edenot E b1) = a1 -> bv_unsigned (edenot E b2) = a2 -> bv_unsigned (edenot E n1e) = n1 -> bv_unsigned (edenot E n2e) = n2 ->
  (a1 + off1 + n1 <= a2 + off2 \/ a2 + off2 + n2 <= a1 + off1) -> kentry_ok RSEGS E M (KDisj (SA b1 off1) n1e (SA b2 off2) n2e).
Proof.
  intros H1 H2 H3 H4 HD. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite H1, H2, H3, H4. lia.
Qed.

Lemma iter_run (last : bool) fx R M (sp data X C NEXT : Z) (I n : nat) :
  getr R (reg 2) = Z_to_bv 64 (sp - 96) -> getr R (reg 9) = Z_to_bv 64 (Z.of_nat n) -> getr R (reg 18) = Z_to_bv 64 (Z.of_nat I) ->
  bv_unsigned (getr R (reg 20)) = X -> getr R (reg 21) = Z_to_bv 64 10 -> bv_unsigned (getr R (reg 22)) = C ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 96 <= sp -> sp <= 2 ^ 47 -> BGU.u64_at M (sp - 96) data ->
  4096 <= data -> data mod 8 = 0 -> data + 8 * (Z.of_nat n + 1) <= 2 ^ 47 -> (data + 8 * (Z.of_nat n + 1) <= sp - 96 \/ sp <= data) ->
  (1 <= n)%nat -> Z.of_nat n <= 2 ^ 23 -> (if last then I + 1 = n else I + 2 <= n)%nat ->
  BGU.writable M (data + 8 * Z.of_nat I) 8 -> BGU.u64_at M (data + 8 * Z.of_nat I + 8) NEXT -> 0 <= NEXT < 2 ^ 64 ->
  exists fx' R' M',
    msteps RSEGS (st fx R LOOP M) (st fx' R' (if last then TAIL else LOOP) M')
    /\ (forall i, In i KSIT -> getr R' (reg i) = getr R (reg i))
    /\ getr R' (reg 18) = Z_to_bv 64 (Z.of_nat I + 1) /\ getr R' (reg 19) = Z_to_bv 64 (Z.of_nat I + 1)
    /\ getr R' (reg 20) = Z_to_bv 64 NEXT /\ getr R' (reg 21) = Z_to_bv 64 10 /\ bv_unsigned (getr R' (reg 22)) = BMA.mcar X C
    /\ BGU.u64_at M' (data + 8 * Z.of_nat I) (BMA.mlo X C)
    /\ (forall a : word, ~ (data + 8 * Z.of_nat I <= bv_unsigned a < data + 8 * Z.of_nat I + 8) -> M' a = M a)
    /\ mem_grows M M'.
Proof.
  intros H2 H9 H18 HX H21 HC A16 SLO SHI VW Dlo Da Dhi DJ Hn1 Hn HI HW HN RN.
  assert (HIn: (I + 1 <= n)%nat) by (destruct last; lia).
  set (V := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 32%nat => getr R (reg 20) | 33%nat => Z_to_bv 64 (Z.of_nat n) | 35%nat => Z_to_bv 64 data
                                        | 36%nat => Z_to_bv 64 NEXT | 40%nat => Z_to_bv 64 (Z.of_nat I) | 41%nat => getr R (reg 22) | _ => getr R (reg k) end).
  set (E := Env V (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbn [E ev V]; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = Z.of_nat n) by (cbn [E ev V]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = data) by (cbn [E ev V]; apply BGU.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = NEXT) by (cbn [E ev V]; apply BGU.unsigned_lit; lia).
  assert (U40: bv_unsigned (ev E 40) = Z.of_nat I) by (cbn [E ev V]; apply BGU.unsigned_lit; lia).
  assert (U32: bv_unsigned (ev E 32) = X) by exact HX.
  assert (U41: bv_unsigned (ev E 41) = C) by exact HC.
  pose proof (BL.bvu_range (getr R (reg 20))) as RX. rewrite HX in RX. pose proof (BL.bvu_range (getr R (reg 22))) as RC. rewrite HC in RC.
  assert (AqI: bv_unsigned (edenot E e_qI) = data + 8 * Z.of_nat I).
  { cbn [edenot e_qI]. rewrite (BGU.word_of_unsigned _ _ U35), (BGU.word_of_unsigned _ _ U40), BGU.md_mul_lit, BGU.alu_add_lit. rewrite BGU.unsigned_lit by lia. lia. }
  assert (Aqn: bv_unsigned (edenot E e_qn) = data + 8 * Z.of_nat n).
  { cbn [edenot e_qn]. rewrite (BGU.word_of_unsigned _ _ U35), (BGU.word_of_unsigned _ _ U33), BGU.md_mul_lit, BGU.alu_add_lit. rewrite BGU.unsigned_lit by lia. lia. }
  assert (Abl: bv_unsigned (edenot E e_bl) = 8 * (Z.of_nat n + 1)).
  { cbn [edenot e_bl]. rewrite (BGU.word_of_unsigned _ _ U33), BGU.md_mul_lit, BGU.alu_add_lit. rewrite BGU.unsigned_lit by lia. lia. }
  assert (AnI: bv_unsigned (edenot E e_nI) = Z.of_nat n - Z.of_nat I).
  { cbn [edenot e_nI]. rewrite (BGU.word_of_unsigned _ _ U40), (BGU.word_of_unsigned _ _ U33), BGU.md_mul_lit, BGU.alu_add_lit.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    replace (Z.of_nat n + -1 * Z.of_nat I) with ((Z.of_nat n - Z.of_nat I) + 0 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  assert (K7: Forall (kentry_ok RSEGS E M) ITER7).
  { unfold ITER7.
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U35. lia. lia. replace (sp + -96) with (sp - 96) by lia. exact VW. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U35. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U35. lia. lia. }
    apply Forall_cons. { cbn [kentry_ok]. rewrite Aqn. lia. }
    apply Forall_cons. { eapply (kentry_KDisj_e E M (EVar 2) (-96) (ELit 96) 96 (EVar 35) 0 e_bl (8 * (Z.of_nat n + 1)) sp data). cbn [edenot]. exact U2. cbn [edenot]. exact U35.
                         cbn [edenot]. apply BGU.unsigned_lit. lia. exact Abl. lia. }
    apply Forall_nil. }
  assert (KR: forall lo hi, lo <= Z.of_nat n - Z.of_nat I <= hi -> Forall (kentry_ok RSEGS E M) [KRange (EVar 33) 1 8388608; KRange (EVar 40) 0 8388608; KRange e_nI lo hi; KWr (SA e_qI 0) (ELit 8); KWord (SA e_qI 8) 8 (EVar 36)]).
  { intros lo hi Hlh.
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U33. lia. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U40. lia. }
    apply Forall_cons. { cbn [kentry_ok]. rewrite AnI. lia. }
    apply Forall_cons. { eapply kentry_KWr_e. exact AqI. lia. lia. lia. rewrite Z.add_0_r. exact HW. }
    apply Forall_cons. { eapply BGU.kentry_KWord_e. exact AqI. cbn [edenot]. exact U36. lia. lia. exact HN. }
    apply Forall_nil. }
  (* [comment removed for export] *)
  assert (POST: forall (fx' : FPState) E' (R' : bvmap 5 word) (M' : word -> option byte) (regs0 regs_out : list expr) (cells : list kentry) (F0 : list SGP.region) (pc' : Z),
     regs_ok E regs0 R -> BGU.kept_ok 48 regs0 regs_out KSIT = true -> env_agree 48 E E' ->
     (forall i e, In (i, e) (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (reg i) = edenot E' e) ->
     (forall a : word, SGP.outside E' F0 a -> M' a = M a) -> F0 = [(e_qI, 0, ELit 8)] ->
     (forall K, In K cells -> kentry_ok RSEGS E' M' K) -> cells = [KWord (SA e_qI 0) 8 BMU.t_lo] ->
     nth 18 regs_out (ELit 0) = EAlu ALU_ADD (EVar 40) (ELit 1) -> nth 19 regs_out (ELit 0) = EAlu ALU_ADD (EVar 40) (ELit 1) ->
     nth 20 regs_out (ELit 0) = EVar 36 -> nth 21 regs_out (ELit 0) = ELit 10 -> nth 22 regs_out (ELit 0) = BMU.t_car ->
     mem_grows M M' -> msteps RSEGS (st fx R LOOP M) (st fx' R' pc' M') -> pc' = (if last then TAIL else LOOP) ->
     exists fx'' R'' M'',
       msteps RSEGS (st fx R LOOP M) (st fx'' R'' (if last then TAIL else LOOP) M'')
       /\ (forall i, In i KSIT -> getr R'' (reg i) = getr R (reg i))
       /\ getr R'' (reg 18) = Z_to_bv 64 (Z.of_nat I + 1) /\ getr R'' (reg 19) = Z_to_bv 64 (Z.of_nat I + 1)
       /\ getr R'' (reg 20) = Z_to_bv 64 NEXT /\ getr R'' (reg 21) = Z_to_bv 64 10 /\ bv_unsigned (getr R'' (reg 22)) = BMA.mcar X C
       /\ BGU.u64_at M'' (data + 8 * Z.of_nat I) (BMA.mlo X C)
       /\ (forall a : word, ~ (data + 8 * Z.of_nat I <= bv_unsigned a < data + 8 * Z.of_nat I + 8) -> M'' a = M a)
       /\ mem_grows M M'').
  { intros fx' E' R' M' regs0 regs_out cells F0 pc' HR KOK Hag Hregs Hfr -> Hcells -> N18 N19 N20 N21 N22 Hgr Hms ->.
    exists fx', R', M'. split. exact Hms.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (AqI': bv_unsigned (edenot E' e_qI) = data + 8 * Z.of_nat I). { rewrite (BGU.edenot_kept 48 E E') by (auto; reflexivity). exact AqI. }
    split. { intros j Hj. apply (BGU.kept_regs E E' R R' regs0 regs_out 48 KSIT KOK HR Hag Hregs j Hj). }
    split. { rewrite (BGU.out_reg regs_out E' R' 18 Hregs) by lia. rewrite N18. cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U40), BGU.alu_add_lit. reflexivity. }
    split. { rewrite (BGU.out_reg regs_out E' R' 19 Hregs) by lia. rewrite N19. cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U40), BGU.alu_add_lit. reflexivity. }
    split. { rewrite (BGU.out_reg regs_out E' R' 20 Hregs) by lia. rewrite N20. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U36. }
    split. { rewrite (BGU.out_reg regs_out E' R' 21 Hregs) by lia. rewrite N21. reflexivity. }
    split. { rewrite (BGU.out_reg regs_out E' R' 22 Hregs) by lia. rewrite N22.
             rewrite (BL.zcomp_sound E' BMU.t_car BMU.z_car BMU.z_car_ok).
             rewrite (BL.zden_agree 48 (BL.uv E') (BL.uv E) BMU.t_car BMU.z_car). 2:{ intros k Hk. unfold BL.uv. rewrite (proj1 Hag k Hk). reflexivity. }
             2: vm_compute; reflexivity. 2: exact BMU.z_car_ok.
             rewrite BMU.t_car_val. unfold BL.uv. rewrite U32, U41. reflexivity.
             unfold BL.uv. rewrite U32. unfold BL.inrange, BL.MM. exact RX.
             unfold BL.uv. rewrite U41. unfold BL.inrange, BL.MM. exact RC. }
    split. { replace (data + 8 * Z.of_nat I) with ((data + 8 * Z.of_nat I) + 0) by lia. apply (BGU.u64_of_KWord_e E' M' e_qI 0 BMU.t_lo _ (BMA.mlo X C)).
             - apply Hcells. left. reflexivity.
             - exact AqI'.
             - rewrite (BL.zcomp_sound E' BMU.t_lo BMU.z_lo BMU.z_lo_ok).
               rewrite (BL.zden_agree 48 (BL.uv E') (BL.uv E) BMU.t_lo BMU.z_lo). 2:{ intros k Hk. unfold BL.uv. rewrite (proj1 Hag k Hk). reflexivity. }
               2: vm_compute; reflexivity. 2: exact BMU.z_lo_ok.
               rewrite BMU.t_lo_val. unfold BL.uv. rewrite U32, U41. reflexivity.
               unfold BL.uv. rewrite U32. unfold BL.inrange, BL.MM. exact RX.
               unfold BL.uv. rewrite U41. unfold BL.inrange, BL.MM. exact RC. }
    split. { intros a Ha. apply Hfr. unfold SGP.outside. constructor; [|constructor]. unfold estart, elenZ. cbn [a_base a_off]. rewrite AqI'. cbn [edenot]. rewrite BGU.unsigned_lit by lia. lia. }
    exact Hgr. }
  destruct last.
  - assert (HR: regs_ok E PIL.regs0 R).
    { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PIL.regs0 nth edenot ev E V]. repeat split; try reflexivity; try assumption.
      rewrite BGU.alu_add_lit. exact H2. }
    assert (HK: know_ok RSEGS E M PIL.kn0). { unfold know_ok. rewrite kn0_IL. apply Forall_app. split. exact K7. apply KR. lia. }
    destruct (PIL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0. change PIL.NX0 with 48%nat in Hag.
    apply (POST fx' E' R' M' PIL.regs0 PIL.regs_out PIL.cells PIL.F0 (SR.ps_pc PIL.ps0) HR KSIL_ok Hag Hregs Hfr F0_IL Hcells cells_IL eq_refl eq_refl eq_refl eq_refl t_car_IL Hgr Hms eq_refl).
  - assert (HR: regs_ok E PIT.regs0 R).
    { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PIT.regs0 nth edenot ev E V]. repeat split; try reflexivity; try assumption.
      rewrite BGU.alu_add_lit. exact H2. }
    assert (HK: know_ok RSEGS E M PIT.kn0). { unfold know_ok. rewrite kn0_IT. apply Forall_app. split. exact K7. apply KR. lia. }
    destruct (PIT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0. change PIT.NX0 with 48%nat in Hag.
    apply (POST fx' E' R' M' PIT.regs0 PIT.regs_out PIT.cells PIT.F0 (SR.ps_pc PIT.ps0) HR KSIT_ok Hag Hregs Hfr F0_IT Hcells cells_IT eq_refl eq_refl eq_refl eq_refl t_car_IT Hgr Hms eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition limbs (M : word -> option byte) (q : Z) (f : nat -> Z) (lo hi : nat) : Prop :=
  forall j, (lo <= j < hi)%nat -> BGU.u64_at M (q + 8 * Z.of_nat j) (f j).

Lemma limbs_frame M M' q f lo hi (a b : Z) :
  0 <= q -> q + 8 * Z.of_nat hi <= 2 ^ 64 ->
  (forall x : word, ~ (a <= bv_unsigned x < b) -> M' x = M x) ->
  (q + 8 * Z.of_nat hi <= a \/ b <= q + 8 * Z.of_nat lo) ->
  limbs M q f lo hi -> limbs M' q f lo hi.
Proof.
  intros Hq Hhi HF Hd HL j Hj. apply (BGU.u64_at_frame M M'). lia. lia. 2: apply HL; auto.
  intros k Hk. apply HF. rewrite BGU.unsigned_lit by lia. lia.
Qed.

Lemma loop_run (k : nat) : forall (i n : nat) fx R M (sp q V : Z),
  (i + k + 1 = n)%nat -> Z.of_nat n <= 2 ^ 23 -> 0 <= V -> 4096 <= q -> q mod 8 = 0 -> q + 8 * (Z.of_nat n + 1) <= 2 ^ 47 ->
  (q + 8 * (Z.of_nat n + 1) <= sp - 96 \/ sp <= q) ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 96 <= sp -> sp <= 2 ^ 47 -> BGU.u64_at M (sp - 96) q ->
  getr R (reg 2) = Z_to_bv 64 (sp - 96) -> getr R (reg 9) = Z_to_bv 64 (Z.of_nat n) -> getr R (reg 18) = Z_to_bv 64 (Z.of_nat i) ->
  bv_unsigned (getr R (reg 20)) = wordi V i -> getr R (reg 21) = Z_to_bv 64 10 -> bv_unsigned (getr R (reg 22)) = mcarry 10 V i ->
  BGU.writable M q (8 * (Z.of_nat n + 1)) ->
  limbs M q (wordi (10 * V)) 0 i -> limbs M q (wordi V) (S i) (S n) ->
  exists fx' R' M',
    msteps RSEGS (st fx R LOOP M) (st fx' R' TAIL M')
    /\ (forall r, In r KSIT -> getr R' (reg r) = getr R (reg r))
    /\ bv_unsigned (getr R' (reg 22)) = mcarry 10 V n
    /\ getr R' (reg 20) = Z_to_bv 64 (wordi V n)
    /\ limbs M' q (wordi (10 * V)) 0 n /\ limbs M' q (wordi V) n (S n)
    /\ (forall a : word, ~ (q + 8 * Z.of_nat i <= bv_unsigned a < q + 8 * Z.of_nat n) -> M' a = M a)
    /\ mem_grows M M'.
Proof.
  induction k as [|k IH]; intros i n fx R M sp q V Hk Hn HV Hq Ha Hqn DJ A16 SLO SHI VW H2 H9 H18 H20 H21 H22 HW L1 L2.
  - (* [comment removed for export] *)
    assert (Hi: (n = i + 1)%nat) by lia.
    destruct (iter_run true fx R M sp q (wordi V i) (mcarry 10 V i) (wordi V n) i n H2 H9 H18 H20 H21 H22 A16 SLO SHI VW Hq Ha Hqn DJ ltac:(lia) Hn ltac:(cbn; lia))
      as (fx' & R' & M' & Hms & Hkept & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Hcell & Hfr & Hgr).
    + intros d m Hd Hm. replace (q + 8 * Z.of_nat i + d) with (q + (8 * Z.of_nat i + d)) by lia. apply HW; lia.
    + replace (q + 8 * Z.of_nat i + 8) with (q + 8 * Z.of_nat n) by lia. apply L2. lia.
    + apply BM.wordi_bound.
    + exists fx', R', M'. destruct (BM.step_vals V i HV) as [E1 E2].
      split. exact Hms. split. exact Hkept.
      split. rewrite Ha5, E2, Hi, Nat.add_1_r. reflexivity.
      split. exact Ha3.
      split. { intros j Hj. destruct (Nat.eq_dec j i) as [->|NE].
               - rewrite <- E1. exact Hcell.
               - eapply (limbs_frame M M' q (wordi (10 * V)) 0 i). lia. lia. exact Hfr. lia. exact L1. lia. }
      split. { eapply (limbs_frame M M' q (wordi V) n (S n)). lia. lia. exact Hfr. lia. intros j Hj. apply L2. lia. }
      split. { intros a Hna. apply Hfr. lia. }
      exact Hgr.
  - (* [comment removed for export] *)
    destruct (iter_run false fx R M sp q (wordi V i) (mcarry 10 V i) (wordi V (S i)) i n H2 H9 H18 H20 H21 H22 A16 SLO SHI VW Hq Ha Hqn DJ ltac:(lia) Hn ltac:(cbn; lia))
      as (fx1 & R1 & M1 & Hms1 & Hkept1 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Hcell & Hfr1 & Hgr1).
    + intros d m Hd Hm. replace (q + 8 * Z.of_nat i + d) with (q + (8 * Z.of_nat i + d)) by lia. apply HW; lia.
    + replace (q + 8 * Z.of_nat i + 8) with (q + 8 * Z.of_nat (S i)) by lia. apply L2. lia.
    + apply BM.wordi_bound.
    + destruct (BM.step_vals V i HV) as [E1 E2].
      destruct (IH (S i) n fx1 R1 M1 sp q V ltac:(lia) Hn HV Hq Ha Hqn DJ A16 SLO SHI) as (fx' & R' & M' & Hms & Hkept & Hb1 & Hb2 & L1' & L2' & Hfr & Hgr).
      * eapply (BGU.u64_at_frame M M1). lia. lia. intros j Hj. apply Hfr1. rewrite BGU.unsigned_lit by lia. lia. exact VW.
      * rewrite (Hkept1 2%nat) by (apply L5K.In_of_mem; reflexivity). exact H2.
      * rewrite (Hkept1 9%nat) by (apply L5K.In_of_mem; reflexivity). exact H9.
      * rewrite Ha1. f_equal. lia.
      * rewrite Ha3. apply BGU.unsigned_lit. apply BM.wordi_bound.
      * exact Ha4.
      * rewrite Ha5. exact E2.
      * change (L5.writable RSEGS M1 q (8 * (Z.of_nat n + 1))). eapply L5.writable_grows. exact Hgr1. exact HW.
      * intros j Hj. destruct (Nat.eq_dec j i) as [->|NE].
        -- rewrite <- E1. exact Hcell.
        -- eapply (limbs_frame M M1 q (wordi (10 * V)) 0 i). lia. lia. exact Hfr1. lia. exact L1. lia.
      * eapply (limbs_frame M M1 q (wordi V) (S (S i)) (S n)). lia. lia. exact Hfr1. lia. intros j Hj. apply L2. lia.
      * exists fx', R', M'. split. eapply msteps_trans; eauto.
        split. { intros r Hr. rewrite Hkept by auto. apply Hkept1; auto. }
        split. exact Hb1. split. exact Hb2. split. exact L1'. split. exact L2'.
        split. { intros a Hna. rewrite Hfr by lia. apply Hfr1. lia. }
        eapply mem_grows_trans; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kn0_P3 : P3.kn0 = [KRange (EVar 2) 140735332483168 140737488355328; KAlign (EVar 2) 16; KWord (SA (EVar 2) (-96)) 8 (EVar 35);
   KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 8; KRange (EVar 33) 0 8388608; KRange e_qn 4096 140737488355320;
   KDisj (SA (EVar 2) (-96)) (ELit 96) (SA (EVar 35) 0) e_bl; KWr (SA e_qn 0) (ELit 8)].
Proof. vm_compute. reflexivity. Qed.
Lemma F0_P3 : P3.F0 = [(e_qn, 0, ELit 8)]. Proof. vm_compute. reflexivity. Qed.
Lemma cells_P3 : P3.cells = [KWord (SA e_qn 0) 8 (EVar 41)]. Proof. vm_compute. reflexivity. Qed.

Lemma p3_run fx R M (o data c sp : Z) (n : nat) :
  getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 (Z.of_nat n) -> bv_unsigned (getr R (reg 22)) = c -> getr R (reg 2) = Z_to_bv 64 (sp - 96) ->
  0 <= o < 2 ^ 64 -> 4096 <= data -> data mod 8 = 0 -> Z.of_nat n <= 2 ^ 23 -> data + 8 * (Z.of_nat n + 1) <= 2 ^ 47 ->
  (data + 8 * (Z.of_nat n + 1) <= sp - 96 \/ sp <= data) ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 96 <= sp -> sp <= 2 ^ 47 -> BGU.u64_at M (sp - 96) data ->
  BGU.writable M (data + 8 * Z.of_nat n) 8 ->
  exists fx' R3 M3, msteps RSEGS (st fx R TAIL M) (st fx' R3 REDUCE M3)
    /\ (forall x, In x KS3 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 RET2 /\ getr R3 (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R3 (reg 8) = Z_to_bv 64 o /\ getr R3 (reg 9) = Z_to_bv 64 (Z.of_nat n)
    /\ getr R3 (reg 10) = Z_to_bv 64 o
    /\ BGU.u64_at M3 (data + 8 * Z.of_nat n) c
    /\ (forall a : word, ~ (data + 8 * Z.of_nat n <= bv_unsigned a < data + 8 * Z.of_nat n + 8) -> M3 a = M a) /\ mem_grows M M3.
Proof.
  intros H8 H9 H22 H2 Ho Dlo Da Hn Dhi DJ A16 SLO SHI VW WD.
  pose proof (BL.bvu_range (getr R (reg 22))) as RC. rewrite H22 in RC.
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 42%nat => Z_to_bv 64 o | 35%nat => Z_to_bv 64 data | 33%nat => Z_to_bv 64 (Z.of_nat n) | 41%nat => getr R (reg 22) | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U42: bv_unsigned (ev E 42) = o) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = data) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = Z.of_nat n) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U41: bv_unsigned (ev E 41) = c) by (cbv [E ev Vf]; exact H22).
  assert (Aqn: bv_unsigned (edenot E e_qn) = data + 8 * Z.of_nat n).
  { cbn [edenot e_qn]. rewrite (BGU.word_of_unsigned _ _ U35), (BGU.word_of_unsigned _ _ U33), BGU.md_mul_lit, BGU.alu_add_lit. rewrite BGU.unsigned_lit by lia. lia. }
  assert (Abl: bv_unsigned (edenot E e_bl) = 8 * (Z.of_nat n + 1)).
  { cbn [edenot e_bl]. rewrite (BGU.word_of_unsigned _ _ U33), BGU.md_mul_lit, BGU.alu_add_lit. rewrite BGU.unsigned_lit by lia. lia. }
  assert (HR: regs_ok E P3.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P3.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
    rewrite BGU.alu_add_lit. exact H2. }
  assert (HK: know_ok RSEGS E M P3.kn0).
  { unfold know_ok. rewrite kn0_P3.
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U35. lia. lia. replace (sp + -96) with (sp - 96) by lia. exact VW. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U35. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U35. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U33. lia. }
    apply Forall_cons. { cbn [kentry_ok]. rewrite Aqn. lia. }
    apply Forall_cons. { eapply (kentry_KDisj_e E M (EVar 2) (-96) (ELit 96) 96 (EVar 35) 0 e_bl (8 * (Z.of_nat n + 1)) sp data). cbn [edenot]. exact U2. cbn [edenot]. exact U35.
                         cbn [edenot]. apply BGU.unsigned_lit. lia. exact Abl. lia. }
    apply Forall_cons. { eapply kentry_KWr_e. exact Aqn. lia. lia. lia. rewrite Z.add_0_r. exact WD. }
    apply Forall_nil. }
  destruct (P3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change P3.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (Aqn': bv_unsigned (edenot E' e_qn) = data + 8 * Z.of_nat n). { rewrite (BGU.edenot_kept 48 E E') by (auto; reflexivity). exact Aqn. }
  assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i P3.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg P3.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' P3.regs0 P3.regs_out 48 KS3 KS3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BGU.out_reg P3.regs_out E' R' 1 Hregs) by lia. reflexivity. }
  split. { rewrite (BGU.out_reg P3.regs_out E' R' 2 Hregs) by lia. change (nth 2 P3.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-96))).
           cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U2), BGU.alu_add_lit. reflexivity. }
  split. { apply (OUT 8%nat 42%nat); [lia | reflexivity | lia | exact U42]. }
  split. { apply (OUT 9%nat 33%nat); [lia | reflexivity | lia | exact U33]. }
  split. { apply (OUT 10%nat 42%nat); [lia | reflexivity | lia | exact U42]. }
  split. { replace (data + 8 * Z.of_nat n) with ((data + 8 * Z.of_nat n) + 0) by lia. apply (BGU.u64_of_KWord_e E' M' e_qn 0 (EVar 41) _ c).
           apply Hcells. change (SR.ps_cells P3.ps0) with P3.cells. rewrite cells_P3. left; reflexivity. exact Aqn'.
           cbn [edenot]. rewrite AG by lia. exact U41. }
  split. { intros a Ha. apply Hfr. change P3.F0 with P3.F0. rewrite F0_P3. unfold SGP.outside. constructor; [|constructor]. unfold estart, elenZ. cbn [a_base a_off]. rewrite Aqn'. cbn [edenot]. rewrite BGU.unsigned_lit by lia. lia. }
  exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p4_run fx R M (o sp c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 r : Z) :
  getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 2) = Z_to_bv 64 (sp - 96) ->
  BGU.u64_at M (sp - 8) c8 -> BGU.u64_at M (sp - 16) c16 -> BGU.u64_at M (sp - 24) c24 -> BGU.u64_at M (sp - 32) c32 -> BGU.u64_at M (sp - 40) c40 ->
  BGU.u64_at M (sp - 48) c48 -> BGU.u64_at M (sp - 56) c56 -> BGU.u64_at M (sp - 64) c64 -> BGU.u64_at M (sp - 72) c72 -> BGU.u64_at M (sp - 80) c80 ->
  0 <= c8 < 2 ^ 64 -> 0 <= c16 < 2 ^ 64 -> 0 <= c24 < 2 ^ 64 -> 0 <= c32 < 2 ^ 64 -> 0 <= c40 < 2 ^ 64 ->
  0 <= c48 < 2 ^ 64 -> 0 <= c56 < 2 ^ 64 -> 0 <= c64 < 2 ^ 64 -> 0 <= c72 < 2 ^ 64 -> 0 <= c80 < 2 ^ 64 ->
  0 <= o < 2 ^ 64 -> sp mod 16 = 0 -> 0x7fff7f800000 + 96 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 96) 96 ->
  c8 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET2 M) (st fx' R3 r M3)
    /\ (forall x, In x KS4 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16 /\ getr R3 (reg 9) = Z_to_bv 64 c24
    /\ getr R3 (reg 18) = Z_to_bv 64 c32 /\ getr R3 (reg 19) = Z_to_bv 64 c40 /\ getr R3 (reg 20) = Z_to_bv 64 c48
    /\ getr R3 (reg 21) = Z_to_bv 64 c56 /\ getr R3 (reg 22) = Z_to_bv 64 c64 /\ getr R3 (reg 23) = Z_to_bv 64 c72 /\ getr R3 (reg 24) = Z_to_bv 64 c80
    /\ getr R3 (reg 10) = Z_to_bv 64 o
    /\ (forall a : word, M3 a = M a) /\ mem_grows M M3.
Proof.
  intros H8 H2 C8 C16 C24 C32 C40 C48 C56 C64 C72 C80 R8 R16 R24 R32 R40 R48 R56 R64 R72 R80 Ho A16 SLO SHI WR Er [Hr He].
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o
                                         | 41%nat => Z_to_bv 64 c8 | 42%nat => Z_to_bv 64 c16 | 43%nat => Z_to_bv 64 c24 | 44%nat => Z_to_bv 64 c32
                                         | 45%nat => Z_to_bv 64 c40 | 46%nat => Z_to_bv 64 c48 | 47%nat => Z_to_bv 64 c56 | 48%nat => Z_to_bv 64 c64
                                         | 49%nat => Z_to_bv 64 c72 | 50%nat => Z_to_bv 64 c80 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U41: bv_unsigned (ev E 41) = c8) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U42: bv_unsigned (ev E 42) = c16) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c24) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c32) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U45: bv_unsigned (ev E 45) = c40) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U46: bv_unsigned (ev E 46) = c48) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U47: bv_unsigned (ev E 47) = c56) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U48: bv_unsigned (ev E 48) = c64) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U49: bv_unsigned (ev E 49) = c72) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U50: bv_unsigned (ev E 50) = c80) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E P4.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P4.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
    rewrite BGU.alu_add_lit. exact H2. }
  assert (HK: know_ok RSEGS E M P4.kn0).
  { unfold know_ok; cbv delta [P4.kn0].
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U41. lia. lia. exact C8. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U42. lia. lia. exact C16. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C24. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C32. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U45. lia. lia. exact C40. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U46. lia. lia. exact C48. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U47. lia. lia. exact C56. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U48. lia. lia. exact C64. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U49. lia. lia. exact C72. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U50. lia. lia. exact C80. }
    apply Forall_nil. }
  destruct (P4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change P4.NX0 with 64%nat in Hag.
  assert (AG: forall k, (k < 64)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr. constructor. }
  assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i P4.regs_out (ELit 0) = EVar k -> (k < 64)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg P4.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
  assert (R1: getr R' (reg 1) = Z_to_bv 64 c8) by (apply (OUT 1%nat 41%nat); [lia | reflexivity | lia | exact U41]).
  exists fx', R', M'. split.
  { eapply msteps_trans. exact Hms. change (SR.ps_pc P4.ps0) with RETI. apply ret_21110. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' P4.regs0 P4.regs_out 64 KS4 KS4_ok HR Hag Hregs j Hj). }
  split. exact R1.
  split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
  split. { apply (OUT 8%nat 42%nat); [lia | reflexivity | lia | exact U42]. }
  split. { apply (OUT 9%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
  split. { apply (OUT 18%nat 44%nat); [lia | reflexivity | lia | exact U44]. }
  split. { apply (OUT 19%nat 45%nat); [lia | reflexivity | lia | exact U45]. }
  split. { apply (OUT 20%nat 46%nat); [lia | reflexivity | lia | exact U46]. }
  split. { apply (OUT 21%nat 47%nat); [lia | reflexivity | lia | exact U47]. }
  split. { apply (OUT 22%nat 48%nat); [lia | reflexivity | lia | exact U48]. }
  split. { apply (OUT 23%nat 49%nat); [lia | reflexivity | lia | exact U49]. }
  split. { apply (OUT 24%nat 50%nat); [lia | reflexivity | lia | exact U50]. }
  split. { apply (OUT 10%nat 35%nat); [lia | reflexivity | lia | exact U35]. }
  split. exact MM. exact Hgr.
Qed.
End SCFG_1.


End L5MULPU.
