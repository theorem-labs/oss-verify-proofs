(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PmModelFactsA PmStep PeStepA PmParKit PeASrcKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCSinkA PeShZ PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrame PeCFrameA PeEncKit PeACReset1 PeAEncScalP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_ac2a4_ac2a8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEAENCN.
#[local] Transparent e_end_value.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)).

Abbreviation SBL := 2147450880.

Definition CSK : list nat := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Definition runP (pc0 ra bt : Z) (XA : bvmap 5 word -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 ov -> XA R ->
    L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 SBL -> L5.u32_at RSEGS M 1317376 1 -> 140735332487200 <= sp <= 140737488355328 ->
    sp mod 16 = 0 -> L5.writable RSEGS M (sp - 32) 32 -> 4096 <= ov <= 140737488355272 -> ov mod 8 = 0 ->
    (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) -> L5KA.zeros_at M (ov / 8 + SBL) 7 -> L5.writable RSEGS M ov 56 ->
    ((sp - 32) + 32 <= ov \/ ov + 56 <= (sp - 32)) ->
    L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1 ->
    L5.u64_at RSEGS M (ov + 8) osk -> 4096 <= osk <= 140737488355304 -> osk mod 8 = 0 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 32 <= i < sp - 32 + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pc0 M) (mst fx' R' 0xaf02c M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 ra /\ getr R' (reg 2) = Z_to_bv 64 (sp - 32) /\ getr R' (reg 8) = Z_to_bv 64 ov /\ getr R' (reg 9) = Z_to_bv 64 SBL
      /\ getr R' (reg 10) = Z_to_bv 64 osk /\ getr R' (reg 11) = Z_to_bv 64 (sp - 25)
      /\ L5.u8_at RSEGS M' (sp - 25) bt
      /\ L5.u64_at RSEGS M' (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M' (sp - 16) (bv_unsigned (getr R (reg 8)))
      /\ L5.u64_at RSEGS M' (sp - 8) (bv_unsigned (getr R (reg 1))).

Definition runE0 (pc1 : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov eb r s0v s1v a0v a1v : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= r < 2 ^ 64 -> 0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> 0 <= a0v < 2 ^ 64 -> 0 <= a1v < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 (sp - 32) -> getr R (reg 8) = Z_to_bv 64 ov -> getr R (reg 9) = Z_to_bv 64 SBL -> getr R (reg 10) = Z_to_bv 64 a0v -> getr R (reg 11) = Z_to_bv 64 a1v ->
    L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 SBL -> L5.u32_at RSEGS M 1317376 1 -> 140735332487200 <= sp <= 140737488355328 ->
    sp mod 16 = 0 -> L5.writable RSEGS M (sp - 32) 32 -> 4096 <= ov <= 140737488355272 -> ov mod 8 = 0 ->
    (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) -> L5KA.zeros_at M (ov / 8 + SBL) 7 -> L5.writable RSEGS M ov 56 ->
    ((sp - 32) + 32 <= ov \/ ov + 56 <= (sp - 32)) ->
    L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1 ->
    L5.u64_at RSEGS M (ov + 24) eb -> L5.u64_at RSEGS M (ov + 32) eb -> 0 <= eb <= 140737488355328 ->
    L5.u64_at RSEGS M (sp - 8) r -> L5.u64_at RSEGS M (sp - 16) s0v -> L5.u64_at RSEGS M (sp - 24) s1v -> L5.ra_ok r ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pc1 M) (mst fx' R' r M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = Z_to_bv 64 s0v /\ getr R' (reg 9) = Z_to_bv 64 s1v /\ getr R' (reg 10) = Z_to_bv 64 1.

Definition runE1 (pc1 : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov eb ed cn r s0v s1v a0v a1v : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= ed < 2 ^ 64 -> 0 <= cn < 2 ^ 64 -> 0 <= r < 2 ^ 64 -> 0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 ->
    0 <= a0v < 2 ^ 64 -> 0 <= a1v < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 (sp - 32) -> getr R (reg 8) = Z_to_bv 64 ov -> getr R (reg 9) = Z_to_bv 64 SBL -> getr R (reg 10) = Z_to_bv 64 a0v -> getr R (reg 11) = Z_to_bv 64 a1v ->
    L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 SBL -> L5.u32_at RSEGS M 1317376 1 -> 140735332487200 <= sp <= 140737488355328 ->
    sp mod 16 = 0 -> L5.writable RSEGS M (sp - 32) 32 -> 4096 <= ov <= 140737488355272 -> ov mod 8 = 0 ->
    (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) -> L5KA.zeros_at M (ov / 8 + SBL) 7 -> L5.writable RSEGS M ov 56 ->
    ((sp - 32) + 32 <= ov \/ ov + 56 <= (sp - 32)) ->
    L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1 ->
    L5.u64_at RSEGS M (ov + 24) eb -> L5.u64_at RSEGS M (ov + 32) ed -> 4096 <= eb <= 140737488355328 -> 4120 <= ed <= 140737488355328 -> ed mod 8 = 0 ->
    24 <= ed - eb <= 100000 -> L5.writable RSEGS M (ed - 24) 24 -> (2147446784 + 17592186048512 <= ed - 24 \/ (ed - 24) + 24 <= 2147446784) ->
    L5KA.zeros_at M ((ed - 8) / 8 + SBL) 1 ->
    ((ed - 24) + 24 <= (sp - 32) \/ (sp - 32) + 32 <= (ed - 24)) -> ((ed - 24) + 24 <= ov \/ ov + 56 <= (ed - 24)) -> L5.u64_at RSEGS M (ed - 8) cn ->
    L5.u64_at RSEGS M (sp - 8) r -> L5.u64_at RSEGS M (sp - 16) s0v -> L5.u64_at RSEGS M (sp - 24) s1v -> L5.ra_ok r ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (ed - 8 <= i < ed - 8 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pc1 M) (mst fx' R' r M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = Z_to_bv 64 s0v /\ getr R' (reg 9) = Z_to_bv 64 s1v /\ getr R' (reg 10) = Z_to_bv 64 1
      /\ L5.u64_at RSEGS M' (ed - 8) ((cn + 1) mod 2 ^ 64).

Lemma null_runP : runP 0xac244 0xac28c 90 (fun _ => True).
Proof.
  unfold runP. intros fx R M sp ov osk H1 H2 H3 G2 G10 _ K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17.
  assert (HO : bv_unsigned (getr R (reg 10)) = ov) by (rewrite G10; apply L5.unsigned_lit; exact H2).
  pose proof (PEAENCSP.aenNA_conc fx R M (fun j => match j with 2%nat => sp | 41%nat => osk | _ => 0 end)) as P. cbn beta iota in P. rewrite !HO in P.
  L5SAR.feed P ltac:(first [assumption | unfold PEAENCSP.aligned; assumption]).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & C25 & S24 & S16 & S8).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|].
  split; [intros j Hj; apply KS1; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|].
  split; [exact T1|]. split; [exact T2|]. split; [rewrite T8; exact G10|]. split; [exact T9|]. split; [exact T10|]. split; [exact T11|].
  split; [exact C25|]. split; [exact S24|]. split; [exact S16| exact S8].
Qed.

Lemma null_runE0 : runE0 0xac28c.
Proof.
  unfold runE0. intros fx R M sp ov eb r s0v s1v a0v a1v H1 H2 H3 H4 H5 H6 H7 H8 G2 G8 G9 G10 G11 K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 RA.
  pose proof (PEAENCSP.aenNE0_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 38%nat => eb | 44%nat => r | 45%nat => s0v | 46%nat => s1v
      | 55%nat => a0v | 56%nat => a1v | _ => 0 end)) as P. cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PEAENCSP.aligned; assumption]).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11).
  pose proof RA as (Hr1 & Hr2).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac2f4 W_ac2a4 r F_ac2a4 eq_refl D_ac2a4 T1 ltac:(lia) Hr2) as MSR.
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
  split; [intros j Hj; apply KS1; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|].
  split; [exact T2|]. split; [exact T8|]. split; [exact T9| exact T10].
Qed.

Lemma null_runE1 : runE1 0xac28c.
Proof.
  unfold runE1. intros fx R M sp ov eb ed cn r s0v s1v a0v a1v H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 G2 G8 G9 G10 G11
    K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 RA.
  pose proof RA as (Hr1 & Hr2).
  destruct (Z.eq_dec cn 18446744073709551615) as [CW|CNW].
  - rewrite CW in K26.
    pose proof (PEAENCSP.aenNE1w_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 38%nat => eb | 39%nat => ed | 44%nat => r | 45%nat => s0v | 46%nat => s1v
        | 55%nat => a0v | 56%nat => a1v | _ => 0 end)) as P. cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | unfold PEAENCSP.aligned; assumption]).
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & C8).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac2f4 W_ac2a4 r F_ac2a4 eq_refl D_ac2a4 T1 ltac:(lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
    split; [intros j Hj; apply KS1; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|].
    split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T10|]. rewrite CW. change ((18446744073709551615 + 1) mod 2 ^ 64) with 0. exact C8.
  - pose proof (PEAENCSP.aenNE1_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 38%nat => eb | 39%nat => ed | 42%nat => cn | 44%nat => r | 45%nat => s0v
        | 46%nat => s1v | 55%nat => a0v | 56%nat => a1v | _ => 0 end)) as P. cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | unfold PEAENCSP.aligned; assumption | lia]).
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & C8).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac2f4 W_ac2a4 r F_ac2a4 eq_refl D_ac2a4 T1 ltac:(lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
    split; [intros j Hj; apply KS1; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|].
    split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T10|]. rewrite Z.mod_small by lia. exact C8.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMA.ly_as0 L C LY.

Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.

Lemma ri_perm l1 l2 FF LK cr Aw M V : Permutation l1 l2 -> ri_inv HI l1 FF LK cr Aw M V -> ri_inv HI l2 FF LK cr Aw M V.
Proof.
  intros PERM HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok _ l2 FF FF LK cr Aw M V HH).
  - intros b. split; apply Permutation_in; [exact PERM| apply Permutation_sym; exact PERM].
  - apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_map fst PERM)). apply NoDup_ListNoDup. exact ND.
  - intros f. tauto.
  - rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.

Lemma content_keepA' LB FF sp scr W M M' fb p s str sm op :
  L5SAR.ek L ar LB FF sp scr W M M' -> PMKA.wapp W ->
  (forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  PMSPA.aobjA FF (PMSPA.o_is AD fb) 272 -> (forall i, PMSPA.o_is AD fb + 80 <= i < PMSPA.o_is AD fb + 80 + 24 -> L5.outside W i) ->
  incl (PM.vs_own str) LB -> In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB ->
  (forall q m, In (q, m) LB -> PMKA.blk_out W q m) ->
  PM.iss_at RSEGS AD PMSPA.accA M (PMSPA.o_is AD fb) str sm -> PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op (PMSPA.o_is AD fb) s ->
  PEC.content_ok RSEGS AD M fb p (PM.p_src s) str sm -> PEC.content_ok RSEGS AD M' fb p (PM.p_src s) str sm.
Proof.
  intros EK WAPP FRB BRB AO OW INCS QIN OB IA PA.
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). pose proof VS as (_ & _ & VSF).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _). pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
  apply (PECFA.content_keepA RSEGS AD L ar LB FF sp scr W M M' EK WAPP FRB BRB fb p s str sm AO OW INCS).
  - intros c n q ->. cbn in VSF. destruct VSF as (_ & _ & _ & Hn & Hc & _ & _ & _). split; [lia|]. apply OB. apply INCS. cbn. left. reflexivity.
  - intros n ->. cbn in VSF. lia.
  - exact QIN.
  - apply OB. exact QIN.
  - exact G1.
  - exact G2.
  - exact G3.
Qed.

Lemma enc_bumpA (M M' : word -> option byte) ov fb eb ek rr d :
  PECA.enc_atA RSEGS EE L ar M ov fb (PEC.ENC eb ek (rev rr) d) ->
  0 <= ov -> ov + 56 <= 2 ^ 64 -> (0 < ek -> 0 <= eb /\ eb + PEC.ESZ * PEC.ecap ek <= 2 ^ 64) ->
  PMFA.agA M M' ov 56 ->
  (0 < ek -> forall i, 0 <= i < 2 ^ 64 -> eb <= i < eb + PEC.ESZ * PEC.ecap ek -> ~ PEEK.cc_rng eb rr i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (0 < ek -> PMFA.agsh M M' eb (PEC.ESZ * PEC.ecap ek)) ->
  mem_grows M M' ->
  (forall e2 rr', rr = e2 :: rr' -> L5.u64_at RSEGS M' (eb + PEC.ESZ * Z.of_nat (length rr') + 16) ((ei_cnt e2 + 1) mod TWO64)) ->
  PECA.enc_atA RSEGS EE L ar M' ov fb (PEC.ENC eb ek (rev (PEEK.ebump rr)) d).
Proof.
  intros EA Ho Ho' BB [AGO SHO] AGB SHB MG UCC. unfold PECA.enc_atA in EA |- *. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EA |- *.
  destruct EA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & CC & Hk & Hlen & Hd & Hk0 & HB & HIT). pose proof (PEC.ecap_nonneg ek) as CN.
  rewrite length_rev in Hlen, HB, HIT, V32.
  assert (LEN' : length (rev (PEEK.ebump rr)) = length rr) by (rewrite length_rev; apply PEEK.ebump_length).
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 56 -> L5C.agree_on M M' a n) by (intros a n X1 X2 i Hi; apply AGO; lia).
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [rewrite LEN'; apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V32]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V40]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply SUB; lia|lia|lia| exact V48]|].
  split; [exact (L5.defined_grows M M' _ _ MG D)|]. split; [exact (PMFA.accA_agree M M' ov 56 SHO CC)|].
  split; [exact Hk|]. split; [rewrite LEN'; lia|]. split; [exact Hd|]. split; [exact Hk0|]. split.
  - intros Hp. destruct (HB Hp) as (AL & DB & BR & ACCB & ANB). destruct (BB Hp) as (B0 & B1). pose proof (SHB Hp) as SB'.
    split; [exact AL|]. split; [exact (L5.defined_grows M M' _ _ MG DB)|]. split; [exact BR|]. rewrite LEN'. split.
    + apply (PMFA.accA_agree M M'); [| exact ACCB]. intros x Hx. apply SB'. unfold PEC.ESZ in *. nia.
    + apply (PECFA.annA_agree M M'); [unfold PEC.ESZ in *; nia| exact AL| exact SB'| exact ANB].
  - rewrite LEN'. intros i Hi.
    assert (Hp : 0 < ek).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in Hlen. rewrite Z0 in Hlen. cbn in Hlen. lia. }
    destruct (BB Hp) as (B0 & B1).
    destruct rr as [|e2 rr']; [cbn in Hi; lia|]. cbn [PEEK.ebump rev]. cbn [length rev] in Hi, Hlen, HB, HIT.
    destruct (Nat.lt_ge_cases i (length rr')) as [LT|GE].
    + rewrite app_nth1 by (rewrite length_rev; exact LT). specialize (HIT i ltac:(lia)). rewrite app_nth1 in HIT by (rewrite length_rev; exact LT).
      apply (PECF.eitem_at_agree RSEGS M M'); [| unfold PEC.ESZ in *; lia | unfold PEC.ESZ in *; lia | exact HIT].
      intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [PEEK.cc_rng]. unfold PEC.ESZ in *. lia.
    + assert (EI_ : i = length rr') by lia. subst i. rewrite PEEK.nth_top. specialize (HIT (length rr') ltac:(lia)). rewrite PEEK.nth_top in HIT.
      destruct HIT as (K0c & K8c & _). split; [|split].
      * cbn [ei_kind]. apply (PMF.u32_at_agree RSEGS M M'); [| unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia| exact K0c].
        intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [PEEK.cc_rng]. unfold PEC.ESZ in *. lia.
      * cbn [ei_len]. apply (L5C.u64_at_agree RSEGS M M'); [| unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia| exact K8c].
        intros j Hj. apply (AGB Hp); [unfold PEC.ESZ in *; lia| unfold PEC.ESZ in *; lia|]. cbn [PEEK.cc_rng]. unfold PEC.ESZ in *. lia.
      * cbn [ei_cnt]. exact (UCC e2 rr' eq_refl).
Qed.

Lemma ffroomA_mono h h' FF LK LK2 : PMSPA.ffroomA h FF LK -> incl LK2 LK -> NoDup (map ff_addr (FF ++ LK2)) -> h' <= h -> PMSPA.ffroomA h' FF LK2.
Proof.
  intros FR INC ND Hh kk Hk. specialize (FR kk Hk). rewrite L5SAR.ff_count_app in FR. rewrite L5SAR.ff_count_app.
  pose proof (L5SAR.ff_count_incl kk LK2 LK INC (L5SAR.nodup_of_map_app_r FF LK2 ND)) as C2. lia.
Qed.

Section Call.
Variables (pc0 ra bt : Z) (XA : bvmap 5 word -> Prop).
Hypothesis RUNP : runP pc0 ra bt XA.
Hypothesis RUNE0 : runE0 ra.
Hypothesis RUNE1 : runE1 ra.
Hypothesis RAOK : L5.ra_ok ra.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z).
Variables (xstk : list pstate) (xpos : Z) (xmore xdone xhalt : bool) (xdepth : Z) (xec : bool) (xestk : list eitem) (xedepth xlo xhi : Z) (xbad : bool).
Variables (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Let X : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad.

Let XS (a : Z) : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + a) (xhi + a) xbad.
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 4.
Hypothesis FRM : PMSPA.ffroomA 4 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis HXA : XA R.
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis POK : PECSPA.payload_ok p.
Hypothesis MP : PECSPA.mp_enc p X.
Hypothesis HB1 : PESKA.spa_hb P (xhi + 1).
Hypothesis CRED : PMSP.credit_le (PECA.pot_encA L ar P en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (e_end_value (XS 1)) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Let LB : list (Z * Z) := PEC.owned s en k ++ LBX.

Let LBc0 : list (Z * Z) := PM.parser_own s ++ LBX.

Let LBY : list (Z * Z) := PM.parser_own s ++ PEC.enc_own en ++ LBX.

Let Ws : list L5.range := [(PESK.o_sink EE fb, 24)].

Definition csk (Ri : bvmap 5 word) : Prop := forall j, In j CSK -> getr Ri (reg j) = getr R (reg j).

Local Ltac name_objs :=
  set (op := PMSPA.o_p AD fb) in *; set (ov := PMSPA.o_v AD fb) in *; set (oec := PMSPA.o_ec AD fb) in *; set (ois := PMSPA.o_is AD fb) in *;
  set (osk := PESK.o_sink EE fb) in *;
  assert (Eop : op = fb + 592) by reflexivity; assert (Eov : ov = fb + 496) by reflexivity; assert (Eoec : oec = fb + 1120) by reflexivity;
  assert (Eois : ois = fb + 96) by reflexivity; assert (Eosk : osk = fb + 432) by reflexivity.

Local Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH; change (20480 / 8) with 2560 in STKSH;
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2); pose proof RAOK as (Hra1 & Hra2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp; rewrite L5K.rl3 in Rgp; rewrite L5K.rl4 in Rtp;
  pose proof FOK as ((rs & Hfb) & Fal);
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & _);
  pose proof (WF _ Hfb) as (F1 & F2 & F3 & F4 & F5 & F6); cbn [ff_addr ff_class fst snd] in F1, F2, F3, F4, F5, F6; change (ff_bytes 5) with 2048 in F1, F2, F3, F4, F5, F6;
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP; unfold FS_BYTES in F1, F2, F3, F4, F5, F6, FSAPP, FSCEIL, FSIMG.

Lemma AOF a n : fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n.
Proof. intros H1 H2. destruct FOK as ((rs & Hfb) & Fal). exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. Qed.
Lemma FB8 j : (fb + 8 * j) mod 8 = 0.
Proof.
  destruct FOK as (_ & Fal). pose proof (Z.div_mod fb 2048 ltac:(lia)) as E0. rewrite Fal, Z.add_0_r in E0. rewrite E0.
  replace (2048 * (fb / 2048) + 8 * j) with ((256 * (fb / 2048) + j) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma SP16 j : (sp - 16 * j) mod 8 = 0.
Proof.
  pose proof (Z.div_mod sp 32 ltac:(lia)) as E0. rewrite SP32, Z.add_0_r in E0. rewrite E0.
  replace (32 * (sp / 32) - 16 * j) with ((4 * (sp / 32) - 2 * j) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma A16' : sp mod 16 = 0.
Proof. pose proof (Z.div_mod sp 32 ltac:(lia)) as E0. rewrite SP32, Z.add_0_r in E0. rewrite E0. replace (32 * (sp / 32)) with ((2 * (sp / 32)) * 16) by lia. apply Z_mod_mult. Qed.
Lemma ws_wenc a : L5.outside (PEC.W_enc AD EE fb) a -> L5.outside Ws a.
Proof. intros O r0 [<-|[]]. apply O. unfold PEC.W_enc. cbn [app]. right; left; reflexivity. Qed.
Lemma ws_wapp : PMKA.wapp Ws.
Proof.
  entry_facts. unfold Ws. apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd pe_off_sink PeCLayoutA.EADDR_A]. unfold PESK.o_sink. cbn [pe_off_sink PeCLayoutA.EADDR_A].
  unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - F1 F2 FSAPP. lia.
Qed.

Definition inv (Mi : word -> option byte) (mdi : Model) (LKi : list fframe) (Awi : list (Z * Z)) (cri : credit) (ki : PESK.sink) (a : Z) : Prop :=
  L5.u64_at RSEGS Mi (sp - 8) r /\ L5.u64_at RSEGS Mi (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS Mi (sp - 24) (bv_unsigned (getr R (reg 9)))
  /\ L5CA.astk ar Mi sp 20480 /\ shadow_zero Mi (sp - 20480) 2560
  /\ model_rt model mdi /\ L5CA.amodel_ok Awi mdi /\ incl LKi LK /\ incl Aw Awi
  /\ ri_inv HI (PEC.owned s en ki ++ LBX) FF LKi cri Awi Mi (vml_of mdi)
  /\ PECA.enc_atA RSEGS EE L ar Mi (PMSPA.o_v AD fb) fb en /\ PESKA.sink_atA RSEGS L ar P Mi (PESK.o_sink EE fb) ki
  /\ xlo + a <= PESK.sk_z ki <= xhi + a
  /\ L5SAR.ek L ar LBc0 FF sp 20480 Ws M Mi /\ L5SAR.dk L ar LBc0 FF sp 20480 M Mi
  /\ PMSP.credit_keep cr cri (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en ki).

Lemma keepf Mi : L5SAR.ek L ar LBc0 FF sp 20480 Ws M Mi ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mi (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s /\ PM.iss_at RSEGS AD PMSPA.accA Mi (PMSPA.o_is AD fb) str sm
  /\ L5.u64_at RSEGS Mi (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) /\ PMSTA.base_okA RSEGS AD Mi /\ PESTA.err_okA RSEGS AD AAD EE Mi e
  /\ PEC.content_ok RSEGS AD Mi fb p (PM.p_src s) str sm /\ PECA.ec_stateA RSEGS AD Mi fb xec cat /\ PMSPA.accA Mi (PMSPA.o_p AD fb) PECA.RDR_BYTES.
Proof.
  intros EK. entry_facts. name_objs.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR). cbn [s_ec X] in ECS.
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (BRc0 : forall x, In x LBc0 -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by (intros x Hx; apply BRB; apply INC0; exact Hx).
  assert (PINC : incl (PM.parser_own s) LBc0) by (unfold LBc0; apply incl_appl; apply incl_refl).
  assert (SINC : incl (PM.vs_own str) LBc0) by (unfold LBc0; apply incl_appr; exact INCS).
  pose proof ws_wapp as WAPP.
  assert (OUT : forall i, ~ (osk <= i < osk + 24) -> L5.outside Ws i) by (intros i N r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; clear - N; lia).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model osk 24 sp 20480 HH (PMKA.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & _).
  assert (OUTB : forall q m, In (q, m) LBc0 -> PMKA.blk_out Ws q m).
  { intros q m Hq i Hi. destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m osk 24 HH (INC0 _ Hq) AOSK) as [Xa|Xa]; apply OUT; clear - Xa Hi; lia. }
  assert (OUTO : forall a m, (a + m <= osk \/ osk + 24 <= a) -> forall i, a <= i < a + m -> L5.outside Ws i) by (intros a m Xa i Hi; apply OUT; clear - Xa Hi; lia).
  assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBc0) by (apply PINC; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (SDEP : forall a, PMST.dep AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside Ws a).
  { intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OUT. clear - DI K1; lia. }
  split.
  { apply (PMKA.parser_keepA RSEGS AD L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB BRc0 op ois s (AOF op 384 ltac:(lia) ltac:(lia)) PINC); [| | | | exact PA].
    - apply OUTO. clear - Eop Eosk; lia.
    - apply OUTB. exact Iq.
    - apply OUTB. apply PINC. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
    - intros c n q E1. apply OUTB. apply PINC. unfold PM.parser_own, PM.vs_own. rewrite E1. right; right; left. reflexivity. }
  split.
  { apply (PMKA.iss_keepA RSEGS AD L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB BRc0 ois str sm (AOF ois 272 ltac:(lia) ltac:(lia)) SINC); [| | exact IA].
    - apply OUTO. clear - Eois Eosk; lia.
    - intros c n0 q E1. refine (OUTB q c _). apply SINC. unfold PM.vs_own. rewrite E1. left. reflexivity. }
  split.
  { apply (PMKA.u64_keepA RSEGS L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF]. apply OUTO. clear - Eop Eosk; lia. }
  split.
  { change (PMSTA.base_okA RSEGS PMA.AD Mi). apply (PMASK.base_keep L ar C LY LBc0 FF sp 20480 Ws M Mi EK); [| exact BASE]. intros a Ha. apply OUT. clear - Ha K1; lia. }
  split.
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBc0 FF sp 20480 Ws M Mi EK e PECSA.addrs_wf_A); [exact SDEP| exact ERR]. }
  split.
  { apply (content_keepA' LBc0 FF sp 20480 Ws M Mi fb p s str sm op EK WAPP FRB BRc0 (AOF ois 272 ltac:(lia) ltac:(lia))); [| exact SINC| exact Iq| exact OUTB| exact IA| exact PA| exact CONT].
    fold ois. apply OUTO. clear - Eois Eosk; lia. }
  split.
  { apply (PECFA.ec_state_keepA RSEGS AD L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB fb xec cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
    fold oec. apply OUTO. clear - Eoec Eosk; lia. }
  exact (PMKA.acc_keepA' L ar LBc0 FF sp 20480 Ws M Mi EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACCR).
Qed.

Lemma inv_cpre Mi mdi LKi Awi cri ki a lo hi : inv Mi mdi LKi Awi cri ki a -> lo = xlo + a -> hi = xhi + a ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth lo hi xbad) s str sm en ki e cat.
Proof.
  intros (T8 & T16 & T24 & ASTKi & SZi & MRTi & AMi & ILKi & IAWi & HHi & EAi & SKAi & CLi & EKi & DKi & CKi) Hlo Hhi.
  destruct (keepf Mi EKi) as (PA' & IA' & VREF' & BASE' & ERR' & CONT' & ECS' & ACCR').
  destruct CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & ECI & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad). cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad] in *.
  unfold PECA.crun_preA.
  split; [exact PA'|]. split; [exact IA'|]. split; [exact EAi|]. split; [exact VREF'|]. split; [exact SKAi|].
  split; [exact BASE'|]. split; [exact ERR'|]. split; [exact TBOK|]. split; [exact CONT'|].
  split.
  { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad].
    split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
    split; [exact Lestk|]. split; [exact Ledepth|]. split; [clear - CLi Hlo Hhi; lia| exact Lbad]. }
  cbn [s_ec]. split; [exact ECS'|]. split; [exact ECI| exact ACCR'].
Qed.

Lemma pb_call (a pv h : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  inv Mq mdq LKq Awq crq kq a -> PESKA.spa_hb P h -> xhi + a <= h -> sp - 32 <= pv -> pv + 1 <= sp ->
  getr Rq (reg 1) = Z_to_bv 64 ra -> getr Rq (reg 2) = Z_to_bv 64 (sp - 32) ->
  getr Rq (reg 10) = Z_to_bv 64 (PESK.o_sink EE fb) -> getr Rq (reg 11) = Z_to_bv 64 pv -> csk Rq ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 k2, inv M2 md2 LK2 Aw2 cr2 k2 (a + 1) -> regs_preserved Rq R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R2 ra M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq 0xaf02c Mq mdq) K.
Proof.
  intros INV HBh Ha PV1 PV2 Q1 Q2 Q10 Q11 QCS KX. entry_facts. name_objs.
  pose proof INV as (T8 & T16 & T24 & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  set (LBq := PEC.owned s en kq ++ LBX) in HHq.
  assert (PERMq : Permutation LBq (PESK.sink_own kq ++ LBY)) by (unfold LBq, LBY, PEC.owned; rewrite <- !app_assoc; apply PEEK.perm4).
  pose proof (ri_perm _ _ FF LKq crq Awq Mq _ PERMq HHq) as HHY.
  assert (XINCq : incl LBc0 LBY) by (unfold LBc0, LBY; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINCq : incl (PEC.enc_own en) LBY) by (unfold LBY; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (BRBY : forall x, In x LBY -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
  { intros x Hx. apply (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHY). apply in_or_app. right. exact Hx. }
  assert (FRBq : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply AOF; clear - Eosk; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & KBIG & _).
  pose proof SKAq as (_ & _ & _ & _ & _ & KZCq & KCAPq & KC0q & KBLKq).
  pose proof EAq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EKq' & _).
  pose proof (PMA.ly_cost L C LY) as (KPM & BLIN & BOV).
  assert (PEN : 0 <= fst (PMSPA.scA L (PEC.pot_estack (PMSPA.HV L ar) (PEC.en_k en))) /\ 0 <= snd (PMSPA.scA L (PEC.pot_estack (PMSPA.HV L ar) (PEC.en_k en)))).
  { unfold PMSPA.scA, PEC.pot_estack, PEC.ESZ, PMSPA.HV, LibIfaceAB.heap_view. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead]. rewrite KPM, BOV, BLIN.
    assert (P2 : 2 ^ PEC.en_k en <= 2 ^ 12) by (apply Z.pow_le_mono_r; clear - EKq'; lia). clear - EKq' P2. split; nia. }
  pose proof PB as PBX. unfold PESKA.push_back_specA in PBX. cbn [pe_push_back EE PeCLayoutA.EADDR_A] in PBX.
  apply (PBX PMODE fxq Rq Mq mdq K LBY FF LKq Awq crq osk pv (sp - 32) ra kq HHY AMq K0); clear PBX.
  {
    split; [rewrite L5K.rl1; exact Q1|]. split; [exact RAOK|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split.
    - apply (L5SAR.astk_sub ar Mq Mq sp 20480 32 12288 ASTKq); [intros w D; exact D| clear; lia| clear; lia| clear; lia|].
      replace (sp - 32) with (sp - 16 * 2) by lia. apply PMKA.mod16_8' || idtac.
      replace (sp - 16 * 2) with (sp + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact A16'.
    - apply (PMKA.shadow_zero_sub Mq (sp - 20480) 2560); [| | clear; lia| clear; lia| clear; lia| exact SZq].
      + replace (sp - 20480) with (sp - 16 * 1280) by lia. apply SP16.
      + replace (sp - 32 - 12288) with (sp - 16 * 770) by lia. apply SP16. }
  { apply (ffroomA_mono 4 0 FF LK LKq FRM ILKq NDFq). clear; lia. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. exact Q11. }
  { exact SKAq. }
  { exact AOSK. }
  { exact K8. }
  {
    split; [apply (L5.defined_sub Mq (sp - 20480) 20480 pv 1 SDEFq); clear - PV1 PV2; lia|].
    split; [apply (PESHZ.bat0_of_shadow_zero Mq (sp - 20480) 2560 pv SZq); [replace (sp - 20480) with (sp - 16 * 1280) by lia; apply SP16| clear - PV1; lia| clear - PV2; lia]|].
    split; [right; clear - K2 SLO PV1; lia|]. left. split; [exact PV1| clear - PV2 SHI; lia]. }
  { intros ZC. apply (PESKA.spao_next L P PO (PESK.sk_c kq) h KCAPq); [intros Hc; exact (proj1 (proj2 (proj2 (proj2 (proj2 (KBLKq Hc))))))| exact HBh| clear - ZC CLq Ha; lia]. }
  { unfold PMSP.credit_le, PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CRED, CKq |- *. cbn [fst snd] in CRED, CKq |- *. clear - CRED CKq PEN. lia. }
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 b2 RP2 SKA2 HP2 CK2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2. set (k2 := PESK.sk_push kq b2) in *.

  assert (OWs : forall a0, sp - 20480 <= a0 < sp -> L5.outside Ws a0).
  { intros a0 Ha0 r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. clear - Ha0 K2 SLO; lia. }
  assert (FRAME12 : forall a0, sp - 32 <= a0 < sp -> M2 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT; lia| intros Y; clear - Ha0 Y; lia].
    - apply OWs. clear - Ha0; lia. }
  assert (EK12 : L5SAR.ek L ar LBY FF sp 20480 Ws Mq M2).
  { apply (L5SAR.ek_callee L ar LBY [] FF [] sp 20480 (sp - 32) 12288 Ws Ws Mq M2 HP2); [clear; lia| clear; lia| intros a0 _ O; exact O]. }
  assert (DK12 : L5SAR.dk L ar LBY FF sp 20480 Mq M2) by (apply (L5SAR.dk_callee L ar LBY [] FF [] sp 20480 (sp - 32) 12288 Ws Mq M2 HP2); clear; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (PMKA.astk_after_ahpres L ar LBY FF Mq M2 sp 20480 (sp - 32) 12288 Ws ASTKq HP2); [clear; lia| clear; lia| clear; lia| exact STOP]. }
  pose proof ws_wapp as WAPP.
  assert (SZ2 : shadow_zero M2 (sp - 20480) 2560).
  { apply (PMKA.stksh_keepA L ar LBY FF sp 20480 Ws Mq M2 EK12 WAPP (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact SZq].
    replace (sp - 20480) with (sp - 16 * 1280) by lia. apply SP16. }
  assert (SV : forall a0 v, sp - 32 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS Mq a0 v -> L5.u64_at RSEGS M2 a0 v).
  { intros a0 v H1 H2 U. apply (L5C.u64_at_agree RSEGS Mq M2); [intros i Hi; apply FRAME12; clear - Hi H1 H2; lia| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  assert (OUTO : forall a1 m, (a1 + m <= osk \/ osk + 24 <= a1) -> forall i, a1 <= i < a1 + m -> L5.outside Ws i).
  { intros a1 m Xa i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. clear - Xa Hi; lia. }
  assert (OUTBY : forall q m, In (q, m) LBY -> PMKA.blk_out Ws q m).
  { intros q m Hq. destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m osk 24 HHY (in_or_app _ _ _ (or_intror Hq)) AOSK) as [Xa|Xa];
      (intros i Hi; apply (OUTO q m); [clear - Xa; lia| exact Hi]). }
  apply (KX fx2 R2 M2 md2 LK2 Aw2 cr2 k2); [| exact RP2].
  unfold inv. split; [apply SV; [lia|lia|exact T8]|]. split; [apply SV; [lia|lia|exact T16]|]. split; [apply SV; [lia|lia|exact T24]|].
  split; [exact ASTK2|]. split; [exact SZ2|].
  split; [exact (L5LZ.model_rt_trans model mdq md2 MRTq MRT2)|]. split; [exact AM2|].
  split; [intros x Hx; apply ILKq; apply ILK2; exact Hx|]. split; [intros x Hx; apply IAW2; apply IAWq; exact Hx|].
  split; [refine (ri_perm _ _ FF LK2 cr2 Aw2 M2 _ _ HH2); unfold PEC.owned, LBY; rewrite <- !app_assoc; apply Permutation_sym; apply PEEK.perm4|].
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar LBY FF sp 20480 Ws Mq M2 EK12 WAPP FRBq BRBY ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [| exact EINCq| | exact EAq].
    - apply OUTO. clear - Eov Eosk; lia.
    - intros Hp. apply OUTBY. apply EINCq. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
  split; [exact SKA2|].
  split; [unfold k2, PESK.sk_push; destruct (PESK.sk_z kq <? PESK.sk_c kq); cbn [PESK.sk_z]; clear - CLq; lia|].
  split; [exact (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M2 EKq (PMKA.ek_sublb L ar LBY LBc0 FF sp 20480 Ws Mq M2 XINCq EK12))|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M2 DKq (PMKA.dk_sublb L ar LBY LBc0 FF sp 20480 Mq M2 XINCq DK12))|].
  unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CKq, CK2 |- *. cbn [fst snd] in CKq, CK2 |- *. clear - CKq CK2. lia.
Qed.

Lemma ev_tail (xs : list eitem) (fxq : FPState) Rq Mq mdq LKq Awq crq kq : xs = xestk ->
  inv Mq mdq LKq Awq crq kq 1 ->
  getr Rq (reg 2) = Z_to_bv 64 (sp - 32) -> getr Rq (reg 8) = Z_to_bv 64 (PMSPA.o_v AD fb) -> getr Rq (reg 9) = Z_to_bv 64 SBL -> csk Rq ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq ra Mq mdq) K.
Proof.
  intros HXS INV Q2 Q8 Q9 QCS. entry_facts. name_objs.
  pose proof INV as (T8 & T16 & T24 & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  pose proof AMq as (Mhq & MIq). pose proof ASTKq as (A16q & SLOq & SHIq & _ & SDEFq & SUPq).
  set (LBq := PEC.owned s en kq ++ LBX) in HHq.

  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & ECI & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad X] in Lmore, Ldone, Ldepth, Lstk, Lpos, Lestk, Ledepth, Lz, Lbad.
  destruct MP as (_ & _ & FA & _). cbn [s_estk X] in FA. rewrite <- HXS in FA, Lestk.
  pose proof KONT as KT. unfold e_end_value in KT. cbn [s_estk XS] in KT. rewrite <- HXS in KT.

  assert (EN : en = PEC.ENC (PEC.en_b en) (PEC.en_k en) (PEC.en_stk en) (PEC.en_depth en)) by (destruct en; reflexivity).
  pose proof EAq as EAq'. rewrite EN in EAq'.
  pose proof EAq' as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & EACC & EK & ELEN & EDEP & EKB & EBLK & EITEMS).
  set (eb := PEC.en_b en) in *. set (ek := PEC.en_k en) in *. set (estk := PEC.en_stk en) in *. set (edepth := PEC.en_depth en) in *.
  cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EV24, EV32, EV40, EV48, EACC, EK, ELEN, EDEP, EKB, EBLK, EITEMS. cbn [PEC.en_stk PEC.en_depth] in Lestk, Ledepth.
  pose proof (PEC.ecap_nonneg ek) as CN. unfold PEC.ESZ in EV32, EV40, ELEN, EBLK, EITEMS.

  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq HHq) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _).
  set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKA.aobj_of_aobjA FF ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2' & Q3 & Q4 & Q5) & QBIG & QDEF & QVIS & QSHV & QCL & QSHCL).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF osk 24 (AOF osk 24 ltac:(lia) ltac:(lia)) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & _) & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C Mq LYa ST) as (GOT & CSB & CUAR & _).
  assert (IC0 : L5.img_clear MV 1253376 1286144) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (CSBv : L5.u64_at RSEGS MV 1317368 SBL) by (apply (proj2 (L5A.u64_at_vis H Mq 1317368 SBL (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (CUARv : L5.u32_at RSEGS MV 1317376 1) by (apply (proj2 (L5A.u32_at_vis H Mq 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (CVv : forall a0 m0, ov <= a0 -> a0 + m0 <= ov + 56 -> L5A.avis H a0 m0) by (intros a0 m0 X1 X2; eapply L5A.avis_sub; [exact QVIS| lia| lia]).
  assert (U24 : L5.u64_at RSEGS MV (ov + 24) eb) by (apply (proj2 (L5A.u64_at_vis H Mq (ov + 24) eb (CVv (ov + 24) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV24).
  assert (U32 : L5.u64_at RSEGS MV (ov + 32) (eb + 24 * Z.of_nat (length estk))).
  { apply (proj2 (L5A.u64_at_vis H Mq (ov + 32) _ (CVv (ov + 32) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact EV32. }
  pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq ov 56 HHq (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m ltac:(lia) ltac:(reflexivity) EACC) as Zov.
  unfold SB in Zov. change (56 / 8) with 7 in Zov. fold H MV in Zov.
  assert (D8 : forall j, (ov + 8 * j) / 8 = ov / 8 + j).
  { intros j. rewrite <- Q5 at 1. replace (ov / 8 * 8 + 8 * j) with ((ov / 8 + j) * 8) by lia. apply Z.div_mul. clear; lia. }
  assert (ZG : forall j, 0 <= j < 7 -> L5KA.zeros_at MV ((ov + 8 * j) / 8 + SBL) 1).
  { intros j Hj. rewrite D8. intros i Hi. replace (ov / 8 + j + SBL + i) with (ov / 8 + SBL + (j + i)) by lia. apply Zov. lia. }
  pose proof (ZG 1 ltac:(lia)) as Z8. pose proof (ZG 3 ltac:(lia)) as Z24. pose proof (ZG 4 ltac:(lia)) as Z32.
  replace (ov + 8 * 1) with (ov + 8) in Z8 by lia. replace (ov + 8 * 3) with (ov + 24) in Z24 by lia. replace (ov + 8 * 4) with (ov + 32) in Z32 by lia.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LKq crq Awq Mq mdq sp 20480 32 HHq ASTKq ltac:(lia)) as (_ & _ & SWR).
  assert (QWR : L5.writable RSEGS MV ov 56).
  { apply (proj2 (L5A.writable_vis H Mq ov 56 QVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact QDEF| lia| lia]. }
  assert (SVV : forall a0 v, sp - 32 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS Mq a0 v -> L5.u64_at RSEGS MV a0 v).
  { intros a0 v Ha1 Ha2 U. apply (proj2 (L5A.u64_at_vis H Mq a0 v (VIS a0 8 ltac:(clear - Ha1 SLO; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact U. }
  pose proof (SVV (sp - 8) r ltac:(lia) ltac:(lia) T8) as Y8. pose proof (SVV (sp - 16) _ ltac:(lia) ltac:(lia) T16) as Y16. pose proof (SVV (sp - 24) _ ltac:(lia) ltac:(lia) T24) as Y24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8. pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9.
  pose proof (bv_unsigned_in_range 64 (getr Rq (reg 10))) as B10. pose proof (bv_unsigned_in_range 64 (getr Rq (reg 11))) as B11.
  change (bv_modulus 64) with (2 ^ 64) in B8, B9, B10, B11.
  assert (G10 : getr Rq (reg 10) = Z_to_bv 64 (bv_unsigned (getr Rq (reg 10)))) by (symmetry; apply PMPK.word_id).
  assert (G11 : getr Rq (reg 11) = Z_to_bv 64 (bv_unsigned (getr Rq (reg 11)))) by (symmetry; apply PMPK.word_id).

  assert (REGS : forall R3, (forall j, In j CSK -> getr R3 (reg j) = getr Rq (reg j)) -> getr R3 (reg 2) = Z_to_bv 64 sp ->
            getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9))) -> regs_preserved R R3).
  { intros R3 KS3 T2 T8' T9'. apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite T2; exact (eq_sym Rsp) | rewrite T8'; apply PMPK.word_id | rewrite T9'; apply PMPK.word_id
                                            | rewrite (KS3 _) by inl; apply QCS; inl ] |]). destruct Hj. }
  unfold PMSPA.cfg.
  destruct xs as [|e1 rr].
  -
    rewrite Lestk in U32. cbn [rev length Z.of_nat Z.mul] in U32. rewrite Z.add_0_r in U32.
    assert (EB : 0 <= eb <= 2 ^ 47).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [rewrite (EKB Z0); clear; lia|]. destruct (EBLK ltac:(lia)) as (_ & _ & BR0 & _). destruct BR0 as (X1 & _ & _ & _ & X5 & _). clear - X1 X5 SPT CN; lia. }
    destruct (RUNE0 fxq Rq MV sp ov eb r (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9))) (bv_unsigned (getr Rq (reg 10))) (bv_unsigned (getr Rq (reg 11))))
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T2 & T8' & T9' & T10');
      [ clear - SLO SHI SPT; lia | clear - Q1 Q3; lia | clear - EB; lia | clear - Hr1; lia | exact B8 | exact B9 | exact B10 | exact B11
      | exact Q2 | exact Q8 | exact Q9 | exact G10 | exact G11 | exact IC0 | exact CSBv | exact CUARv | clear - SLO SHI SPT; lia | exact A16' | exact SWR
      | clear - Q1 Q3; lia | exact Q8m | exact QBIG | exact Zov | exact QWR | clear - Q2' SLO; lia | exact Z8 | exact Z24 | exact Z32
      | exact U24 | exact U32 | clear - EB; lia | exact Y8 | exact Y16 | exact Y24 | exact RAok |].
    apply (L5SAR.apiece_ro L ar C HI LYa HIok LBq FF LKq crq Awq Mq mdq fxq fx3 Rq ra R3 r M3v K HHq AMq MS3 MG3 FRZ3).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 AG3. pose proof (L5SAR.mem_eq_of_agree Mq M3 AG3) as EM. subst M3.
    apply (KT fx3 R3 Mq md3 LKq Awq en kq e crq).
    + exact (REGS R3 KS3 T2 T8' T9').
    + exact (inv_cpre Mq mdq LKq Awq crq kq 1 _ _ INV eq_refl eq_refl).
    + intros E1; exact E1.
    + change (PMSPA.pm_scr 4) with 20480. apply (L5SAR.ahpres_of L ar LBc0 FF sp 20480 _ M Mq); [| exact SDEFq| exact DKq].
      apply (L5SAR.ek_W L ar LBc0 FF sp 20480 _ Ws M Mq EKq). exact ws_wenc.
    + exact CKq.
    + exact (L5LZ.model_rt_trans model mdq md3 MRTq MRT3).
    + exact ILKq.
    + exact IAWq.
    + exact AM3.
    + exact HH3.
  -
    assert (HLEN : length estk = Datatypes.S (length rr)) by (rewrite Lestk, length_rev; reflexivity).
    rewrite HLEN in U32, ELEN, EITEMS, EBLK. rewrite Nat2Z.inj_succ in U32, ELEN, EBLK.
    set (m := Z.of_nat (length rr)) in *.
    assert (M0 : 0 <= m) by (unfold m; clear; lia).
    assert (EKP : 0 < ek) by (destruct (Z.eq_dec ek 0) as [Z0|NZ]; [exfalso; unfold PEC.ecap in ELEN; rewrite Z0 in ELEN; cbn in ELEN; clear - ELEN M0; lia| clear - EK NZ; lia]).
    destruct (EBLK EKP) as (EBAL & EBDEF & EBR & EBACC & EBANN). destruct EBR as (EB1 & EB2 & EB3 & EB4 & EB5 & EB6).
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in EB2. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in EB6.
    assert (ECAPB : PEC.ecap ek <= 2048).
    { clear - EK EKP. unfold PEC.ecap. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; lia. }
    assert (BINe : In (eb, 24 * PEC.ecap ek) (PEC.enc_own en)).
    { unfold PEC.enc_own. fold ek eb. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
    assert (BINq : In (eb, 24 * PEC.ecap ek) LBq).
    { unfold LBq, PEC.owned. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact BINe. }

    pose proof (EITEMS (length rr) ltac:(clear; lia)) as TOP. rewrite Lestk in TOP. cbn [rev] in TOP. rewrite PEEK.nth_top in TOP. fold m in TOP.
    destruct TOP as (TK & TL & TC).
    assert (E1OK : ei_ok e1) by (inversion FA; assumption). destruct e1 as [kd ln cn]. cbn [ei_kind ei_len ei_cnt] in TK, TL, TC, E1OK, KT.
    unfold ei_ok in E1OK. cbn [ei_kind ei_len ei_cnt] in E1OK. unfold MAX_ITEMS, TWO64 in E1OK.
    set (ed := eb + 24 * (m + 1)).
    assert (ALend : ed mod 8 = 0) by (unfold ed; apply PEEK.al8_item; exact EBAL).
    replace (eb + 24 * m + 16) with (ed - 8) in TC by (unfold ed; clear; lia).
    assert (OVA : eb + 24 * PEC.ecap ek <= ov \/ ov + 56 <= eb) by exact (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ eb (24 * PEC.ecap ek) ov 56 HHq BINq (AOF ov 56 ltac:(lia) ltac:(lia))).
    assert (BV : forall a0 n0, eb <= a0 -> a0 + n0 <= eb + 24 * PEC.ecap ek -> L5A.avis H a0 n0) by (intros a0 n0 X1 X2; exact (VBLK eb (24 * PEC.ecap ek) a0 n0 BINq X1 X2)).
    assert (WRit : L5.writable RSEGS MV (ed - 24) 24).
    { apply (proj2 (L5A.writable_vis H Mq (ed - 24) 24 (BV (ed - 24) 24 ltac:(unfold ed; lia) ltac:(unfold ed; lia)) ltac:(unfold ed; lia) ltac:(unfold ed; lia))).
      apply (L5.writable_sub _ Mq eb (24 * PEC.ecap ek)); [apply (L5C.writable_of_defined RSEGS); [exact EBDEF| lia| lia]| unfold ed; lia| unfold ed; lia]. }
    assert (TCv : L5.u64_at RSEGS MV (ed - 8) cn).
    { apply (proj2 (L5A.u64_at_vis H Mq (ed - 8) cn (BV (ed - 8) 8 ltac:(unfold ed; lia) ltac:(unfold ed; lia)) ltac:(unfold ed; lia) ltac:(unfold ed; lia))). exact TC. }
    assert (AL8 : (ed - 8) mod 8 = 0) by (replace (ed - 8) with (ed + (-1) * 8) by lia; rewrite Z_mod_plus_full; exact ALend).
    assert (ACC8 : PMSPA.accA Mq (ed - 8) 8) by (intros x Hx; apply EBACC; unfold ed in Hx; clear - Hx M0; lia).
    pose proof (PMKA.blk_shadow_vis L ar C HI LYa HIok LBq FF LKq crq Awq Mq mdq eb (24 * PEC.ecap ek) (ed - 8) 8 HHq BINq ltac:(unfold ed; lia) ltac:(unfold ed; lia) AL8
                  ltac:(clear; lia) ltac:(reflexivity) ACC8) as ZC.
    unfold SB in ZC. change (8 / 8) with 1 in ZC. fold H MV in ZC.
    replace (eb + 24 * (m + 1)) with ed in U32 by reflexivity.
    destruct (RUNE1 fxq Rq MV sp ov eb ed cn r (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9))) (bv_unsigned (getr Rq (reg 10))) (bv_unsigned (getr Rq (reg 11))))
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T2 & T8' & T9' & T10' & C8);
      [ clear - SLO SHI SPT; lia | clear - Q1 Q3; lia | clear - EB1 EB5 SPT CN; lia | unfold ed; clear - EB1 EB5 SPT CN M0 ELEN; lia | clear - E1OK; lia | clear - Hr1; lia
      | exact B8 | exact B9 | exact B10 | exact B11
      | exact Q2 | exact Q8 | exact Q9 | exact G10 | exact G11 | exact IC0 | exact CSBv | exact CUARv | clear - SLO SHI SPT; lia | exact A16' | exact SWR
      | clear - Q1 Q3; lia | exact Q8m | exact QBIG | exact Zov | exact QWR | clear - Q2' SLO; lia | exact Z8 | exact Z24 | exact Z32
      | exact U24 | exact U32 | clear - EB1 EB5 SPT CN; lia | unfold ed; clear - EB1 EB5 SPT CN M0 ELEN; lia | exact ALend
      | unfold ed; clear - M0 ELEN ECAPB; lia | exact WRit | unfold ed; clear - EB6 M0 ELEN; lia | exact ZC
      | unfold ed; clear - EB5 SLO M0 ELEN; lia | unfold ed; clear - OVA M0 ELEN; lia | exact TCv
      | exact Y8 | exact Y16 | exact Y24 | exact RAok |].
    apply (L5SAR.apiece L ar C HI LYa HIok LBq FF LKq crq Awq Mq mdq fxq fx3 Rq ra R3 r M3v (fun a0 => ed - 8 <= a0 < ed - 8 + 8) K HHq AMq MS3 MG3).
    { intros a0 Ha0 Hn. apply FRZ3; [exact Ha0| exact Hn]. }
    { intros a0 Ha0 Wa. split.
      - unfold aclientw, aclient_g. left. exists (eb, 24 * PEC.ecap ek). split; [exact BINq|]. cbn [fst snd]. unfold ed in Wa. clear - Wa M0 ELEN; lia.
      - unfold ed in Wa. clear - Wa EB2 M0 ELEN CN; lia. }
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H M3 = M3v) in VIS3.
    assert (C8' : L5.u64_at RSEGS M3 (ed - 8) ((cn + 1) mod 2 ^ 64)).
    { apply (proj1 (L5A.u64_at_vis H M3 (ed - 8) _ (BV (ed - 8) 8 ltac:(unfold ed; lia) ltac:(unfold ed; lia)) ltac:(unfold ed; lia) ltac:(unfold ed; lia))). rewrite VIS3. exact C8. }

    set (LBr := PESK.sink_own kq ++ LBc0).
    assert (PERMr : Permutation LBq (PEC.enc_own en ++ LBr)).
    { unfold LBq, LBr, LBc0, PEC.owned. rewrite <- !app_assoc. etransitivity; [apply Permutation_app_swap_app|]. apply Permutation_app_head. apply Permutation_app_swap_app. }
    pose proof (ri_perm _ _ FF LKq crq Awq Mq _ PERMr HHq) as HHr.
    assert (EK23r : L5SAR.ek L ar LBr FF sp 20480 [] Mq M3).
    { apply (L5SAR.ek_piece L ar LBr FF sp 20480 [] Mq M3 (fun a0 => ed - 8 <= a0 < ed - 8 + 8) FR3).
      intros a0 Ha0 Hc _ Xa. exact (PMARS1.own_not_aclient L ar C HI HIok (PEC.enc_own en) LBr FF LKq crq Awq Mq _ eb (24 * PEC.ecap ek) a0 sp 20480 HHr BINe ltac:(unfold ed in Xa; clear - Xa M0 ELEN; lia) Hc). }
    assert (INCr : incl LBc0 LBr) by (unfold LBr; apply incl_appr; apply incl_refl).
    assert (EK23 : L5SAR.ek L ar LBc0 FF sp 20480 Ws Mq M3).
    { apply (L5SAR.ek_W L ar LBc0 FF sp 20480 Ws [] Mq M3); [exact (PMKA.ek_sublb L ar LBr LBc0 FF sp 20480 [] Mq M3 INCr EK23r)| intros a0 _ r0 []]. }
    pose proof (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M3 EKq EK23) as EKT.
    assert (DK23 : L5SAR.dk L ar LBc0 FF sp 20480 Mq M3) by (apply L5SAR.dk_grows; exact MGM3).
    assert (SHM3 : forall a0 n0, 0 <= a0 -> a0 + n0 <= 2 ^ 47 -> PMFA.agsh Mq M3 a0 n0).
    { intros a0 n0 Ha Hn0 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
      apply FR3; [clear - SX; lia| intros Y; unfold ed in Y; clear - Y SX EB6 M0 ELEN CN; lia]. }
    assert (BRBr : forall x, In x LBr -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
    { intros x Hx. apply (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHr). apply in_or_app. right. exact Hx. }
    assert (FRBq : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
    assert (EA3 : PECA.enc_atA RSEGS EE L ar M3 ov fb (PEC.ENC eb ek (rev (PEEK.ebump (EI kd ln cn :: rr))) edepth)).
    { apply (enc_bumpA Mq M3 ov fb eb ek (EI kd ln cn :: rr) edepth); [rewrite <- Lestk; exact EAq'| lia| lia| intros _; unfold PEC.ESZ; clear - EB1 EB5 SPT CN; lia| | | | exact MGM3|].
      - split; [| apply SHM3; clear - Q1 Q3; lia]. intros i Hi. apply FR3; [clear - Hi Q1 Q3; lia|]. intros Y. unfold ed in Y. clear - Y Hi OVA M0 ELEN. lia.
      - intros _ i Hi Ri Ni. apply FR3; [exact Hi|]. cbn [PEEK.cc_rng length] in Ni. fold m in Ni. unfold PEC.ESZ in Ni. unfold ed. clear - Ni. lia.
      - intros _. apply SHM3; unfold PEC.ESZ; clear - EB1 EB5 SPT CN; lia.
      - intros e2 rr' Hc. injection Hc as <- <-. cbn [ei_cnt]. fold m. unfold PEC.ESZ, TWO64. replace (eb + 24 * m + 16) with (ed - 8) by (unfold ed; clear; lia). exact C8'. }
    cbn [PEEK.ebump ei_kind ei_len ei_cnt] in EA3.
    assert (SKA3 : PESKA.sink_atA RSEGS L ar P M3 osk kq).
    { apply (PECFA.sink_keepA RSEGS L ar LBr FF sp 20480 [] Mq M3 EK23r PMKA.wapp_nil FRBq BRBr P osk kq (AOF osk 24 ltac:(lia) ltac:(lia))); [intros i _ r0 []| | intros _ i _ r0 []| exact SKAq].
      unfold LBr. apply incl_appl. apply incl_refl. }
    assert (ASTK3 : L5CA.astk ar M3 sp 20480) by exact (L5SAR.astk_grows ar Mq M3 sp 20480 ASTKq MGM3).
    pose proof ASTK3 as (_ & _ & _ & _ & SDEF3 & _).
    destruct (keepf M3 EKT) as (PA3 & IA3 & VREF3 & BASE3 & ERR3 & CONT3 & ECS3 & ACC3).
    apply (KT fx3 R3 M3 md3 LKq Awq (PEC.ENC eb ek (rev rr ++ [EI kd ln ((cn + 1) mod TWO64)]) edepth) kq e crq).
    + exact (REGS R3 KS3 T2 T8' T9').
    + unfold PECA.crun_preA. fold op ov ois osk.
      split; [exact PA3|]. split; [exact IA3|]. split; [unfold TWO64; exact EA3|]. split; [exact VREF3|]. split; [exact SKA3|].
      split; [exact BASE3|]. split; [exact ERR3|]. split; [exact TBOK|]. split; [exact CONT3|].
      split.
      { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth rev w_estk XS].
        split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
        split; [reflexivity|]. split; [exact Ledepth|]. split; [clear - CLq; lia| exact Lbad]. }
      cbn [s_ec w_estk XS]. split; [exact ECS3|]. split; [exact ECI| exact ACC3].
    + intros E1; exact E1.
    + change (PMSPA.pm_scr 4) with 20480. apply (L5SAR.ahpres_of L ar LBc0 FF sp 20480 _ M M3); [| exact SDEF3| exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M3 DKq DK23)].
      apply (L5SAR.ek_W L ar LBc0 FF sp 20480 _ Ws M M3 EKT). exact ws_wenc.
    + unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CKq |- *. cbn [fst snd PEC.en_k] in CKq |- *. change (PEC.en_k en) with ek in CKq |- *. clear - CKq. lia.
    + exact (L5LZ.model_rt_trans model mdq md3 MRTq MRT3).
    + exact ILKq.
    + exact IAWq.
    + exact AM3.
    + exact HH3.
Qed.

Lemma scalar1_core : srealizes RSEGS SCFG (PMSPA.cfg RSEGS R pc0 M model) K.
Proof.
  entry_facts. name_objs. pose proof AM as (Mh & MI).
  pose proof CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad X] in Lmore, Ldone, Ldepth, Lstk, Lpos, Lestk, Ledepth, Lz, Lbad.
  pose proof A10 as B10. rewrite L5K.rl10 in B10.
  assert (Q8m : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 sp 20480 HH (PMKA.aobj_of_aobjA FF ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2' & Q3 & Q4 & Q5) & QBIG & QDEF & QVIS & QSHV & QCL & QSHCL).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model osk 24 sp 20480 HH (PMKA.aobj_of_aobjA FF osk 24 (AOF osk 24 ltac:(lia) ltac:(lia)) K8) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & K4 & K5) & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (IC0 : L5.img_clear MV 1253376 1286144) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (CSBv : L5.u64_at RSEGS MV 1317368 SBL) by (apply (proj2 (L5A.u64_at_vis H M 1317368 SBL (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (CUARv : L5.u32_at RSEGS MV 1317376 1) by (apply (proj2 (L5A.u32_at_vis H M 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (CVv : forall a0 m0, ov <= a0 -> a0 + m0 <= ov + 56 -> L5A.avis H a0 m0) by (intros a0 m0 X1 X2; eapply L5A.avis_sub; [exact QVIS| lia| lia]).
  pose proof EA as (_ & EV8 & _ & _ & _ & _ & _ & EDEF & EACC & EK & _). fold osk in EV8.
  assert (U8 : L5.u64_at RSEGS MV (ov + 8) osk) by (apply (proj2 (L5A.u64_at_vis H M (ov + 8) osk (CVv (ov + 8) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EV8).
  pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 HH (AOF ov 56 ltac:(lia) ltac:(lia)) Q8m ltac:(lia) ltac:(reflexivity) EACC) as Zov.
  unfold SB in Zov. change (56 / 8) with 7 in Zov. fold H MV in Zov.
  assert (D8 : forall j, (ov + 8 * j) / 8 = ov / 8 + j).
  { intros j. rewrite <- Q5 at 1. replace (ov / 8 * 8 + 8 * j) with ((ov / 8 + j) * 8) by lia. apply Z.div_mul. clear; lia. }
  assert (ZG : forall j, 0 <= j < 7 -> L5KA.zeros_at MV ((ov + 8 * j) / 8 + SBL) 1).
  { intros j Hj. rewrite D8. intros i Hi. replace (ov / 8 + j + SBL + i) with (ov / 8 + SBL + (j + i)) by lia. apply Zov. lia. }
  pose proof (ZG 1 ltac:(lia)) as Z8. pose proof (ZG 3 ltac:(lia)) as Z24. pose proof (ZG 4 ltac:(lia)) as Z32.
  replace (ov + 8 * 1) with (ov + 8) in Z8 by lia. replace (ov + 8 * 3) with (ov + 24) in Z24 by lia. replace (ov + 8 * 4) with (ov + 32) in Z32 by lia.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 20480 32 HH ASTK ltac:(lia)) as (_ & _ & SWR).
  assert (QWR : L5.writable RSEGS MV ov 56).
  { apply (proj2 (L5A.writable_vis H M ov 56 QVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact QDEF| lia| lia]. }

  destruct (RUNP fx R MV sp ov osk) as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & C25 & S24 & S16 & S8);
    [ clear - SLO SHI SPT; lia | clear - Q1 Q3; lia | clear - K1 K3; lia | exact Rsp | exact B10 | exact HXA | exact IC0 | exact CSBv | exact CUARv
    | clear - SLO SHI SPT; lia | exact A16' | exact SWR | clear - Q1 Q3; lia | exact Q8m | exact QBIG | exact Zov | exact QWR | clear - Q2' SLO; lia
    | exact Z8 | exact Z24 | exact Z32 | exact U8 | clear - K1 K3; lia | exact K8 |].
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R pc0 R1 0xaf02c M1v (fun a0 => sp - 32 <= a0 < sp - 32 + 32) K HH AM MS1 MG1).
  { intros a0 Ha0 Hn. apply FRZ1; [exact Ha0| exact Hn]. }
  { intros a0 Ha0 Wa. split.
    - unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
    - clear - Wa SLO SPT; lia. }
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.

  assert (Hr : bv_unsigned (getr R (reg 1)) = r) by (rewrite Rra; apply L5.unsigned_lit; clear - Hr1; lia).
  assert (S8' : L5.u64_at RSEGS M1 (sp - 8) r).
  { rewrite <- Hr. apply (proj1 (L5A.u64_at_vis H M1 (sp - 8) _ (VIS (sp - 8) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact S8. }
  assert (S16' : L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (reg 8)))).
  { apply (proj1 (L5A.u64_at_vis H M1 (sp - 16) _ (VIS (sp - 16) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact S16. }
  assert (S24' : L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (reg 9)))).
  { apply (proj1 (L5A.u64_at_vis H M1 (sp - 24) _ (VIS (sp - 24) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact S24. }

  assert (EK01n : L5SAR.ek L ar LB FF sp 20480 [] M M1).
  { apply (PMKA.ek_own_frame L ar C HI LYa HIok LB FF LK cr Aw M M1 _ sp 20480 [] (sp - 32) (sp - 32 + 32) HH SPT); [clear - SLO; lia| clear; lia| clear; lia| exact FR1]. }
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINC : incl (PEC.enc_own en) LB) by (unfold LB, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (KINC : incl (PESK.sink_own k) LB) by (unfold LB, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (ASTK1 : L5CA.astk ar M1 sp 20480) by exact (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1).
  assert (SZ1 : shadow_zero M1 (sp - 20480) 2560).
  { apply (PMKA.stksh_keepA L ar LB FF sp 20480 [] M M1 EK01n PMKA.wapp_nil (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
    replace (sp - 20480) with (sp - 16 * 1280) by lia. apply SP16. }
  assert (EA1 : PECA.enc_atA RSEGS EE L ar M1 ov fb en).
  { apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp 20480 [] M M1 EK01n PMKA.wapp_nil FRB BRB ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact EINC| intros _ i _ r0 []| exact EA]. }
  assert (SKA1 : PESKA.sink_atA RSEGS L ar P M1 osk k).
  { apply (PECFA.sink_keepA RSEGS L ar LB FF sp 20480 [] M M1 EK01n PMKA.wapp_nil FRB BRB P osk k (AOF osk 24 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact KINC| intros _ i _ r0 []| exact SKA]. }

  assert (INV1 : inv M1 md1 LK Aw cr k 0).
  { unfold inv. split; [exact S8'|]. split; [exact S16'|]. split; [exact S24'|]. split; [exact ASTK1|]. split; [exact SZ1|].
    split; [exact MRT1|]. split; [exact AM1|]. split; [apply incl_refl|]. split; [apply incl_refl|]. split; [exact HH1|].
    split; [exact EA1|]. split; [exact SKA1|]. split; [clear - Lz; lia|].
    split; [apply (L5SAR.ek_W L ar LBc0 FF sp 20480 Ws [] M M1); [exact (PMKA.ek_sublb L ar LB LBc0 FF sp 20480 [] M M1 INC0 EK01n)| intros a0 _ r0 []]|].
    split; [apply L5SAR.dk_grows; exact MGM1|]. unfold PMSP.credit_keep. clear. lia. }

  apply (pb_call 0 (sp - 25) (xhi + 1) fx1 R1 M1 md1 LK Aw cr k INV1 HB1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) T1 T2 T10 T11 KS1).
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 RP2.

  apply (ev_tail xestk fx2 R2 M2 md2 LK2 Aw2 cr2 k2 eq_refl INV2).
  - rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl. exact T2.
  - rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl. exact T8.
  - rewrite (L5SAR.cs_of_preserved R1 R2 9 RP2) by inl. exact T9.
  - intros j Hj. rewrite (L5SAR.cs_of_preserved R1 R2 j RP2) by (clear - Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl). exact (KS1 j Hj).
Qed.
End Call.

Theorem v_null_ok : PECSA.v_null_spec L ar HI P.
Proof.
  unfold PECSA.v_null_spec, PECSPA.v_null_spec, PECSPA.eslot_spec. cbn [pe_null EE PeCLayoutA.EADDR_A].
  intros PMODE [] fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 _ CPRE INCS POK MP NB HB CRED KONT.
  destruct X as [xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad].
  assert (ESC : e_scalar 1 1 (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad)
          = e_end_value (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + 1) (xhi + 1) xbad)) by reflexivity.
  rewrite ESC in HB, KONT. rewrite eev_hi in HB. cbn [s_hi] in HB.
  exact (scalar1_core 0xac244 0xac28c 90 (fun _ => True) null_runP null_runE0 null_runE1 ltac:(split; [clear; lia| reflexivity]) PMODE
           fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
           HH AM K0 ENT FRM FRS FOK SP32 A10 I CPRE INCS MP HB CRED KONT).
Qed.
End WithHeap.
End PEAENCN.
