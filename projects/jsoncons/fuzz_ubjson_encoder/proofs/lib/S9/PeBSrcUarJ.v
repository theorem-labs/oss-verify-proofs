(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAb PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PmModelFactsA PeStepAB0 PeBSrcKitJ.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMBSUJ.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Definition own13 (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R (reg 8)))
  /\ L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R (reg 18)))
  /\ L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R (reg 20)))
  /\ L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R (reg 22)))
  /\ L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R (reg 24)))
  /\ L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R (reg 25))) /\ L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R (reg 26)))
  /\ L5.u64_at RSEGS M (E - 104) (bv_unsigned (getr R (reg 27))).
Definition ocell13 (E : Z) (a : Z) : Prop := E - 104 <= a < E.
Lemma own13_agree E R M1 M1' : 0 <= E - 104 -> E <= 2 ^ 64 ->
  own13 E R M1 -> (forall a, ocell13 E a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own13 E R M1'.
Proof.
  intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) AG. unfold own13, ocell13 in *.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
Lemma own13_vis E R H M : (forall a, E - 104 <= a < E -> H (Z_to_bv 64 a) = false) -> 0 <= E - 104 -> E <= 2 ^ 64 -> own13 E R M -> own13 E R (mrestrict H M).
Proof.
  intros HV H0 H1 O. apply (own13_agree E R M (mrestrict H M) H0 H1 O). intros a Ha. unfold ocell13 in Ha.
  apply mrestrict_visible. apply HV. exact Ha.
Qed.

Lemma land_m32 x : 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = x - x mod 32.
Proof.
  intros Hx. replace (2 ^ 64 - 32) with (Z.land (Z.ones 64) (Z.lnot (Z.ones 5))) by reflexivity.
  rewrite Z.land_assoc. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 5) with 32. pose proof (Z.div_mod x 32 ltac:(lia)). lia.
Qed.
Lemma andi_m32 x (imm : bv 12) : 0 <= x < 2 ^ 64 -> bv_signed imm = -32 -> v_andi (Z_to_bv 64 x) (bv_signed imm) = Z_to_bv 64 (x - x mod 32).
Proof.
  intros Hx Hi. unfold v_andi. rewrite Hi. rewrite L5.unsigned_lit by lia.
  replace (bv_wrap 64 (-32)) with (2 ^ 64 - 32) by reflexivity. rewrite land_m32 by exact Hx. reflexivity.
Qed.
Lemma andi_to fx R M (pc : Z) (W : bv 32) (rd rs : bv 5) (imm : bv 12) :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (OpImm ALU_AND rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  msteps RSEGS (st fx R pc M) (st fx (regupd R rd (v_andi (getr R rs) (bv_signed imm))) (pc + 4) M).
Proof.
  intros HF HE HD HZ H0 H1. eapply mst_step; [reflexivity| | apply mst_refl].
  rewrite (step_andi RSEGS R (Z_to_bv 64 pc) M (seg_rom RSEGS) W rd rs imm HF HE HD). rewrite HZ.
  f_equal. f_equal. unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity.
Qed.

Lemma andi_sp (R : bvmap 5 word) sp0 (imm : bv 12) : 0 <= sp0 < 2 ^ 64 -> bv_signed imm = -32 -> getr R (reg 2) = Z_to_bv 64 sp0 ->
  let R' := regupd R 2%bv (v_andi (getr R 2%bv) (bv_signed imm)) in
  getr R' (reg 2) = Z_to_bv 64 (sp0 - sp0 mod 32) /\ (forall j, j <> 2%nat -> (j < 32)%nat -> getr R' (reg j) = getr R (reg j)).
Proof.
  intros Hs Hi G R'. split.
  - unfold R'. rewrite <- L5K.rl2. rewrite getr_same by (intros X; discriminate X). rewrite <- L5K.rl2 in G. rewrite G.
    apply andi_m32; assumption.
  - intros j Hj Hl. unfold R'. apply getr_other. intros E. apply Hj. apply (f_equal (@bv_unsigned 5)) in E.
    rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (2%bv : bv 5)) with 2 in E.
    rewrite Z.mod_small in E by lia. lia.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Lemma src_piece_parserB LB FF fb ois s de' rem' sp scr M2 M3 :
  (forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  (forall q m, In (q, m) LB -> q + m <= PMSPA.o_src PeCLayoutB.CADDR_B fb \/ PMSPA.o_src PeCLayoutB.CADDR_B fb + 296 <= q) ->
  PMKB.wapp [(PMSPA.o_src PeCLayoutB.CADDR_B fb + 256, 40)] ->
  PECA.frame_ok5 FF fb -> incl (PM.parser_own s) LB ->
  L5SAR.ek L ar LB FF sp scr [(PMSPA.o_src PeCLayoutB.CADDR_B fb + 256, 40)] M2 M3 -> mem_grows M2 M3 ->
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M2 (PMSPA.o_p PeCLayoutB.CADDR_B fb) ois s ->
  L5.u64_at RSEGS M3 (PMSPA.o_src PeCLayoutB.CADDR_B fb + 264) (PM.sr_qc (PM.p_src s)) -> L5.u64_at RSEGS M3 (PMSPA.o_src PeCLayoutB.CADDR_B fb + 272) PM.CHUNK ->
  L5.u64_at RSEGS M3 (PMSPA.o_src PeCLayoutB.CADDR_B fb + 280) de' -> L5.u64_at RSEGS M3 (PMSPA.o_src PeCLayoutB.CADDR_B fb + 288) rem' ->
  PM.sr_qc (PM.p_src s) <= de' -> 0 <= rem' -> de' + rem' <= PM.sr_qc (PM.p_src s) + PM.CHUNK ->
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M3 (PMSPA.o_p PeCLayoutB.CADDR_B fb) ois (PMSPA.with_src s (PM.SRC (PM.sr_qc (PM.p_src s)) de' rem')).
Proof.
  intros FRB BRB APT WS FOK INC EK MG PA C1 C2 C3 C4 Q1 Q2 Q3.
  unfold PMSPA.o_src, PMSPA.o_p in *. cbn [pa_off_p PeCLayoutB.CADDR_B ADDR_A] in *.
  pose proof FOK as ((rs & Hfb) & F1024).
  assert (OUTO : forall i, ~ (fb + 592 + 24 + 256 <= i < fb + 592 + 24 + 296) -> L5.outside [(fb + 592 + 24 + 256, 40)] i).
  { intros i N r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  assert (OUTB : forall q m, In (q, m) LB -> forall i, q <= i < q + m -> L5.outside [(fb + 592 + 24 + 256, 40)] i).
  { intros q m Hq i Hi. apply OUTO. destruct (APT q m Hq) as [X|X]; lia. }
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PTB & PVEC & _).
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB) by (apply INC; unfold PM.parser_own, PM.src_own; cbn; left; reflexivity).
  assert (VIN : In (PM.p_b s, 32 * 2 ^ PM.p_k s) LB) by (apply INC; unfold PM.parser_own, PM.src_own, PM.vec_own; cbn; right; left; reflexivity).
  apply (PMBSKJ.parser_src_fieldsA M2 M3 (fb + 592) ois s de' rem' PA).
  - destruct (FRB (fb, 5, rs) Hfb). unfold ff_addr in *. cbn in *. lia.
  - destruct (FRB (fb, 5, rs) Hfb). unfold ff_addr, ff_class, ff_bytes in *. cbn in *. lia.
  - apply (PMKB.agA_obj L ar LB FF sp scr _ M2 M3 EK WS FRB (fb + 592) 280 ltac:(apply (PMBSKJ.aobj_fb FF fb); [exact FOK| lia| lia])). intros i Hi. apply OUTO. lia.
  - apply (PMKB.agA_obj L ar LB FF sp scr _ M2 M3 EK WS FRB (fb + 592 + 320) 64 ltac:(apply (PMBSKJ.aobj_fb FF fb); [exact FOK| lia| lia])). intros i Hi. apply OUTO. lia.
  - apply (PMKB.agsh_obj L ar LB FF sp scr _ M2 M3 EK WS FRB (fb + 592 + 280) 40 ltac:(apply (PMBSKJ.aobj_fb FF fb); [exact FOK| lia| lia])).
  - destruct (BRB _ QIN). cbn [fst snd] in *. lia.
  - destruct (BRB _ QIN). cbn [fst snd] in *. lia.
  - apply (PMKB.agA_blk L ar LB FF sp scr _ M2 M3 EK WS BRB _ _ QIN). apply OUTB. exact QIN.
  - destruct (BRB _ VIN). cbn [fst snd] in *. lia.
  - destruct (BRB _ VIN). cbn [fst snd] in *. lia.
  - apply (PMKB.agA_blk L ar LB FF sp scr _ M2 M3 EK WS BRB _ _ VIN). apply OUTB. exact VIN.
  - intros c0 n0 p0 E.
    assert (TIN : In (p0, c0) LB) by (apply INC; unfold PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own; rewrite E; cbn; right; right; left; reflexivity).
    apply (PMKB.agA_blk L ar LB FF sp scr _ M2 M3 EK WS BRB _ _ TIN). apply OUTB. exact TIN.
  - exact MG.
  - replace (fb + 592 + 288) with (fb + 592 + 24 + 264) by lia. exact C1.
  - replace (fb + 592 + 296) with (fb + 592 + 24 + 272) by lia. exact C2.
  - replace (fb + 592 + 304) with (fb + 592 + 24 + 280) by lia. exact C3.
  - replace (fb + 592 + 312) with (fb + 592 + 24 + 288) by lia. exact C4.
  - exact Q1. - exact Q2. - exact Q3.
Qed.
End WithHeap.
End PMBSUJ.
