(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5CoreSpecsAS8 L5StepARS8 L5CoreBRS8 L5ADetailHRS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PnStatics PmModelFactsA PmStep PeStepA PmParStep PmParKit PeASrcKit PeAParKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeShZ PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrameA PeEncKit PeACReset1 PeCEPushSpecsA PeSEncBeg PeAEncKitG PeAEncBgnP1 PeAEncBgnP2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_ac050_ac054 Ea0_code_ab960_ab964 Ea0_code_aadfc_aae00 Ea0_code_aba78_aba7c.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEAENCBG.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)).
Abbreviation SBL := 2147450880.
Abbreviation EPUSH := 0xb0de0.
Abbreviation EPUSQ := 0xae3ec.
Abbreviation PBPC := 0xaf02c.
Abbreviation MKPC := 0xae310.
Abbreviation PLPC := 0xae710.

Definition CSKa : list nat := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition CSKl : list nat := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma wid (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma wrng (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.

Definition sfacts (FR sp : Z) (M : word -> option byte) : Prop :=
  L5.img_clear M 1253376 1286144 /\ L5.u64_at RSEGS M 1317368 SBL /\ L5.u32_at RSEGS M 1317376 1
  /\ 140735332487168 + 20480 <= sp <= 140737488355328 /\ sp mod 16 = 0 /\ L5.writable RSEGS M (sp - FR) FR.
Definition efacts (FR sp ov osk : Z) (M : word -> option byte) : Prop :=
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at M (ov / 8 + SBL) 7
  /\ L5.writable RSEGS M ov 56 /\ ((sp - FR) + FR <= ov \/ ov + 56 <= (sp - FR))
  /\ L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 16) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 48) / 8 + SBL) 1
  /\ L5.u64_at RSEGS M (ov + 8) osk /\ 4096 <= osk <= 140737488355304 /\ osk mod 8 = 0 /\ L5.u32_at RSEGS M (ov + 16) MAX_DEPTH.

Definition runA (E0 EPRA KD : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk d r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= d < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 ov -> getr R (reg 1) = Z_to_bv 64 r ->
    sfacts 32 sp M -> efacts 32 sp ov osk M -> L5.u32_at RSEGS M (ov + 48) d -> 0 <= d <= 1023 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 32 <= i < sp - 32 + 32) -> ~ (ov + 48 <= i < ov + 52) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R E0 M) (mst fx' R' EPUSH M')
      /\ (forall j, In j CSKa -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 EPRA /\ getr R' (reg 2) = Z_to_bv 64 (sp - 32) /\ getr R' (reg 8) = Z_to_bv 64 ov /\ getr R' (reg 9) = Z_to_bv 64 SBL
      /\ getr R' (reg 10) = Z_to_bv 64 (ov + 24) /\ getr R' (reg 11) = Z_to_bv 64 (sp - 32)
      /\ L5.u32_at RSEGS M' (sp - 32) KD /\ L5.u32_at RSEGS M' (ov + 48) (d + 1)
      /\ L5.u64_at RSEGS M' (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M' (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS M' (sp - 8) r.

Definition runE (E0 MKRA : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk oec r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 ov -> getr R (reg 13) = Z_to_bv 64 oec -> getr R (reg 1) = Z_to_bv 64 r ->
    sfacts 32 sp M -> efacts 32 sp ov osk M -> L5.u32_at RSEGS M (ov + 48) 1024 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 32 <= i < sp - 32 + 32) -> ~ (ov + 48 <= i < ov + 52) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R E0 M) (mst fx' R' MKPC M')
      /\ (forall j, In j CSKa -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 MKRA /\ getr R' (reg 2) = Z_to_bv 64 (sp - 32) /\ getr R' (reg 8) = Z_to_bv 64 ov /\ getr R' (reg 9) = Z_to_bv 64 SBL
      /\ getr R' (reg 10) = Z_to_bv 64 oec /\ getr R' (reg 11) = Z_to_bv 64 11
      /\ L5.u32_at RSEGS M' (ov + 48) 1025
      /\ L5.u64_at RSEGS M' (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M' (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS M' (sp - 8) r.

Definition lregs (R : bvmap 5 word) (sp ov : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 32) /\ getr R (reg 8) = Z_to_bv 64 ov /\ getr R (reg 9) = Z_to_bv 64 SBL.

Definition runP (RA1 PBRA MK : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 ->
    lregs R sp ov -> sfacts 32 sp M -> efacts 32 sp ov osk M ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 25 <= i < sp - 25 + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R RA1 M) (mst fx' R' PBPC M')
      /\ (forall j, In j CSKa -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 PBRA /\ getr R' (reg 10) = Z_to_bv 64 osk /\ getr R' (reg 11) = Z_to_bv 64 (sp - 25)
      /\ lregs R' sp ov /\ L5.u8_at RSEGS M' (sp - 25) MK.

Definition runR (RPC : Z) : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp r : Z),
    0 <= sp < 2 ^ 64 -> getr R (reg 2) = Z_to_bv 64 (sp - 32) -> sfacts 32 sp M ->
    L5.u64_at RSEGS M (sp - 8) r -> L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R0 (reg 8))) -> L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R0 (reg 9))) ->
    getr R0 (reg 1) = Z_to_bv 64 r -> getr R0 (reg 2) = Z_to_bv 64 sp -> L5.ra_ok r -> (forall j, In j CSKa -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R RPC M) (mst fx' R' r M')
      /\ getr R' (reg 10) = Z_to_bv 64 1 /\ regs_preserved R0 R'.

Ltac gks KS := intros j Hj; apply KS; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl.
Ltac feedP P := L5SAR.feed P ltac:(first [assumption | unfold PEABGNP1.aligned; assumption | unfold PEABGNP2.aligned; assumption | apply wid | apply wrng | L5SAR.greg | L5SAR.gmem | lia]).
Ltac greg1 KS :=
  first [ assumption
        | lazymatch goal with |- getr ?R1 (reg ?n) = _ =>
            first [ lazymatch goal with H : getr R1 (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end
                  | rewrite (KS n) by inl; lazymatch goal with H : getr _ (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end ] end ].

Ltac midV R sp ov n oec osk d r R0 :=
  constr:(fun j : nat => match j with 2%nat => sp | 10%nat => ov | 11%nat => n | 13%nat => oec | 14%nat => oec | 41%nat => osk | 43%nat => d | 64%nat => r
     | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9)) | 67%nat => bv_unsigned (getr R0 (reg 18))
     | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end).

Ltac runA_tac CONC :=
  intros fx R M sp ov osk d r Hsp Hov Hosk Hd Hr G2 G10 G1 SF EF U48 HD;
  unfold sfacts in SF; decompose [and] SF; unfold efacts in EF; decompose [and] EF;
  let V := midV R sp ov 0 0 osk d r R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P;
  rewrite G10 in P; rewrite !(L5.unsigned_lit ov) in P by (clear - Hov; lia);
  feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia]|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|];
  repeat split; first [greg1 KS | assumption | rewrite G1, L5.unsigned_lit by (clear - Hr; lia); assumption
                      | lazymatch goal with |- L5.u64_at _ _ _ r => lazymatch goal with H : L5.u64_at _ _ (sp - 8) _ |- _ => rewrite G1, (L5.unsigned_lit r) in H by (clear - Hr; lia); exact H end end ].
Lemma u_runA_a : runA 0xabff4 0xac064 3. Proof. runA_tac PEABGNP1.aqBaA_conc. Qed.
Lemma u_runA_o : runA 0xab904 0xab974 1. Proof. runA_tac PEABGNP1.aqBoA_conc. Qed.

Ltac runE_tac CONC :=
  intros fx R M sp ov osk oec r Hsp Hov Hosk Hoec Hr G2 G10 G13 G1 SF EF U48;
  unfold sfacts in SF; decompose [and] SF; unfold efacts in EF; decompose [and] EF;
  let V := midV R sp ov 0 oec osk 1024 r R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P;
  rewrite G10 in P; rewrite !(L5.unsigned_lit ov) in P by (clear - Hov; lia);
  feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia]|];
  split; [exact MS1|]; rewrite G13 in P; decompose [and] P; split; [gks KS|];
  repeat split; first [greg1 KS | assumption
                      | lazymatch goal with |- L5.u64_at _ _ _ r => lazymatch goal with H : L5.u64_at _ _ (sp - 8) _ |- _ => rewrite G1, (L5.unsigned_lit r) in H by (clear - Hr; lia); exact H end end ].
Lemma u_runE_a : runE 0xabff4 0xac0b0. Proof. runE_tac PEABGNP1.aqBaE_conc. Qed.
Lemma u_runE_o : runE 0xab904 0xab9c0. Proof. runE_tac PEABGNP1.aqBoE_conc. Qed.

Ltac runP_tac CONC :=
  intros fx R M sp ov osk Hsp Hov Hosk (G2 & G8 & G9) SF EF;
  unfold sfacts in SF; decompose [and] SF; unfold efacts in EF; decompose [and] EF;
  let V := midV R sp ov 0 0 osk 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1; apply FRZ1; [exact Hi| clear - N1; lia]|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|]; unfold lregs; repeat split; first [greg1 KS | assumption].
Lemma u_runP_a : runP 0xac064 0xac08c 91. Proof. runP_tac PEABGNP1.aqBaP_conc. Qed.
Lemma u_runP_o : runP 0xab974 0xab99c 123. Proof. runP_tac PEABGNP1.aqBoP_conc. Qed.

Lemma regs_end (R R0 R3 : bvmap 5 word) (sp : Z) :
  (forall j, In j CSKa -> getr R3 (reg j) = getr R (reg j)) -> (forall j, In j CSKa -> getr R (reg j) = getr R0 (reg j)) ->
  getr R0 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 1) = getr R0 (reg 1) ->
  getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) -> regs_preserved R0 R3.
Proof.
  intros KS3 QCS Rsp T2 T1 T8 T9. apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
  repeat (destruct Hj as [<-|Hj]; [first [ rewrite T2; exact (eq_sym Rsp) | rewrite T8; apply Z_to_bv_bv_unsigned | rewrite T9; apply Z_to_bv_bv_unsigned
                                          | rewrite (KS3 _) by inl; apply QCS; inl ] |]). destruct Hj.
Qed.

Ltac runR_tac CONC RET Wr Fr Dr :=
  intros fx R R0 M sp r Hsp G2 SF S8 S16 S24 Hra R0sp RA QCS;
  unfold sfacts in SF; decompose [and] SF; pose proof RA as (Hr1 & Hr2);
  let V := midV R sp 0 0 0 0 0 r R0 in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & T10);
  let MSR := fresh "MSR" in
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 RET Wr _ Fr eq_refl Dr T1 ltac:(clear - Hr1; lia) Hr2) as MSR;
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi; apply FRZ1; exact Hi|];
  split; [eapply msteps_trans; [exact MS1| exact MSR]|]; split; [exact T10|];
  apply (regs_end R R0 R1 sp); [gks KS| exact QCS| exact R0sp| exact T2| rewrite T1, Hra; reflexivity| exact T8| exact T9].
Lemma u_runR_a : runR 0xac08c. Proof. runR_tac PEABGNP1.aqBaR_conc 0xac0a0 W_ac050 F_ac050 D_ac050. Qed.
Lemma u_runR_o : runR 0xab99c. Proof. runR_tac PEABGNP1.aqBoR_conc 0xab9b0 W_ab960 F_ab960 D_ab960. Qed.
Lemma u_runX_a : runR 0xac0b0. Proof. runR_tac PEABGNP1.aqBaX_conc 0xac0a0 W_ac050 F_ac050 D_ac050. Qed.
Lemma u_runX_o : runR 0xab9c0. Proof. runR_tac PEABGNP1.aqBoX_conc 0xab9b0 W_ab960 F_ab960 D_ab960. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMA.ly_as0 L C LY.
Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.
Hypothesis MKEC : PECSA.make_ec_spec L ar HI.
Hypothesis PUTL : PECSA.put_length_spec L ar HI P.
Hypothesis EPK : PECEPX.epush_k_spec RSEGS AD EE L ar HI.

Section Slot.
Variables (E0 EPRA PBRA MKRA KD MK : Z).
Hypothesis RAS : L5.ra_ok EPRA /\ L5.ra_ok PBRA /\ L5.ra_ok MKRA.
Hypothesis HKD : 0 <= KD <= 3.
Hypothesis HMK : 0 <= MK <= 255.
Hypothesis RUNA : runA E0 EPRA KD.
Hypothesis RUNE : runE E0 MKRA.
Hypothesis RUNP : runP EPRA PBRA MK.
Hypothesis RUNR : runR PBRA.
Hypothesis RUNX : runR MKRA.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z).
Variables (xstk : list pstate) (xpos : Z) (xmore xdone xhalt : bool) (xdepth : Z) (xec : bool) (xestk : list eitem) (xedepth xlo xhi : Z) (xbad : bool).
Variables (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Let X : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad.
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 4.
Hypothesis FRM : PMSPA.ffroomA 4 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis A13 : getr R (reg 13) = Z_to_bv 64 (PMSPA.o_ec AD fb).
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis POK : PECSPA.payload_ok p.
Hypothesis MP : PECSPA.mp_encb p X.
Hypothesis NBAD : s_bad (e_begin_indef KD X) = false.
Hypothesis HB : PESKA.spa_hb P (s_hi (e_begin_indef KD X)).
Hypothesis CRED : PMSP.credit_le (PECA.pot_encA L ar P en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (e_begin_indef KD X) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Definition FC (Mx : word -> option byte) : Prop :=
  L5.u64_at RSEGS Mx (sp - 8) r /\ L5.u64_at RSEGS Mx (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS Mx (sp - 24) (bv_unsigned (getr R (reg 9))).
Lemma FC_frame M1 M2 : (forall a, sp - 32 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.
Proof.
  intros AG (C8 & C16 & C24). pose proof ENT as (_ & _ & _ & _ & _ & ASTK & _). change (PMSPA.pm_scr 4) with 20480 in ASTK. pose proof ASTK as (_ & SLO & SHI & SPT & _).
  assert (SV : forall a0 w, sp - 32 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1 a0 w -> L5.u64_at RSEGS M2 a0 w).
  { intros a0 w H1 H2 U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AG; clear - Hi H1 H2; lia| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  unfold FC. split; [apply SV; [clear; lia| clear; lia| exact C8]|]. split; [apply SV; [clear; lia| clear; lia| exact C16]| apply SV; [clear; lia| clear; lia| exact C24]].
Qed.

Lemma FC_but M1 M2 lo hi : hi <= sp - 24 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.
Proof.
  intros Hhi AG (C8 & C16 & C24). pose proof ENT as (_ & _ & _ & _ & _ & ASTK & _). change (PMSPA.pm_scr 4) with 20480 in ASTK. pose proof ASTK as (_ & SLO & SHI & SPT & _).
  assert (SV : forall a0 w, sp - 24 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1 a0 w -> L5.u64_at RSEGS M2 a0 w).
  { intros a0 w H1 H2 U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AG; [clear - Hi H1 H2 SLO SHI SPT; lia| clear - Hi H1 Hhi; lia]| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  unfold FC. split; [apply SV; [clear; lia| clear; lia| exact C8]|]. split; [apply SV; [clear; lia| clear; lia| exact C16]| apply SV; [clear; lia| clear; lia| exact C24]].
Qed.
Lemma HFR : 32 = 32 \/ 32 = 64 \/ 32 = 80 \/ 32 = 96. Proof. left; reflexivity. Qed.
Lemma HNB : 0 <= 1. Proof. clear; lia. Qed.
Lemma CSK3 : In 3%nat CSKa. Proof. inl. Qed.
Lemma CSK4 : In 4%nat CSKa. Proof. inl. Qed.
Lemma CSKall j : In j CSKa -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.
Lemma MPE : PECSPA.mp_enc p X. Proof. exact (proj1 MP). Qed.

Lemma pre_facts : Forall ei_ok xestk /\ 0 <= xedepth <= MAX_DEPTH /\ Z.of_nat (length xestk) <= MAX_DEPTH /\ PEC.en_stk en = rev xestk /\ PEC.en_depth en = xedepth /\ xbad = false /\ xlo <= xhi.
Proof.
  destruct MP as ((LOHI & BADX & FA & ED) & ELEN). cbn [s_lo s_hi s_bad s_estk s_edepth X] in LOHI, BADX, FA, ED, ELEN.
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (_ & _ & _ & _ & _ & Lestk & Ledepth & _). cbn [s_estk s_edepth X] in Lestk, Ledepth.
  split; [exact FA|]. split; [exact ED|]. split; [exact ELEN|]. split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact BADX| exact LOHI].
Qed.

Lemma XF_err : xedepth = MAX_DEPTH -> e_begin_indef KD X = ST xstk xpos xmore xdone xhalt xdepth true xestk (xedepth + 1) (xlo + 0) (xhi + 0) xbad.
Proof. intros E. rewrite (PESENCB.e_begin_indef_err KD X) by (cbn [s_edepth X]; rewrite E; unfold MAX_DEPTH; lia). unfold X. cbn. rewrite !Z.add_0_r. reflexivity. Qed.
Lemma XF_ok : xedepth + 1 <= MAX_DEPTH -> e_begin_indef KD X = ST xstk xpos xmore xdone xhalt xdepth xec (EI KD 0 0 :: xestk) (xedepth + 1) (xlo + 1) (xhi + 1) xbad.
Proof. intros E. rewrite (PESENCB.e_begin_indef_ok KD X) by (cbn [s_edepth X]; exact E). unfold X. cbn. reflexivity. Qed.

#[local] Abbreviation K_vis_entry := (PEAEKG.vis_entry L ar C HI P LY HIok 32 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK SP32 A10 CPRE).
#[local] Abbreviation K_startw := (PEAEKG.inv_startw L ar C HI P LY HIok 32 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK SP32 FC CPRE).
#[local] Abbreviation K_vis := (PEAEKG.vis_facts L ar C HI P LY HIok 32 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC).
#[local] Abbreviation K_frame := (PEAEKG.inv_frame L ar C HI P LY HIok 32 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC).
#[local] Abbreviation K_epush := (PEAEKG.epush_call L ar C HI P LY HIok PO 32 CSKa HFR CSK3 CSK4 R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRS FOK SP32 FC FC_frame (e_begin_indef KD X) CPRE INCS CRED KONT).
#[local] Abbreviation K_pb := (PEAEKG.pb_call L ar C HI P LY HIok PO PB 32 CSKa HFR CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb xlo xhi s en k HH K0 ENT FRM FRS FOK SP32 FC FC_frame CRED).
#[local] Abbreviation K_mkec := (PEAEKG.mkec_call L ar C HI P LY HIok MKEC 32 CSKa HFR CSK3 CSK4 R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP32 FC FC_frame (e_begin_indef KD X) CPRE INCS MPE KONT).
#[local] Abbreviation K_fro := (PEAEKG.finish_ro L ar C HI P LY HIok 32 HFR R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK FC (e_begin_indef KD X) CPRE INCS KONT).
#[local] Abbreviation K_ferr := (PEAEKG.finish_err L ar C HI P LY HIok 32 HFR R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK FC (e_begin_indef KD X) CPRE INCS KONT).
#[local] Abbreviation INV := (PEAEKG.inv L ar HI P M model LBX FF LK Aw cr sp fb xlo xhi s en k FC).

Lemma main : srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R E0 M model) K.
Proof.
  destruct pre_facts as (FA & ED & ELEN & HSTK & HED & HBADX & LOHI).
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp.
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & F3 & F4 & F5 & F6). cbn [ff_addr ff_class fst snd] in F1, F2, F3, F4, F5, F6. change (ff_bytes 5) with 2048 in F1, F2, F3, F4, F5, F6.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. unfold FS_BYTES in F1, F2, F3, F4, F5, F6, FSAPP, FSCEIL, FSIMG. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  destruct K_vis_entry as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z16 & Z48 & U8v & KR & K8 & KO & U16 & U48 & HDEP & G2 & G10 & G1 & RAr & RB).
  cbv beta in RB. set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *. set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *. set (oec := PMSPA.o_ec AD fb) in *.
  assert (Eov : ov = fb + 496) by reflexivity. assert (Eoec : oec = fb + 1120) by reflexivity.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & _).
  assert (AOV : PMSPA.aobjA FF ov 56) by (apply (PEAEKG.AOF FF fb FOK); clear - Eov; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 sp 20480 HH (PMKA.aobj_of_aobjA FF ov 56 AOV O8) ltac:(clear; lia) ltac:(reflexivity)) as ((Q1 & Q2' & Q3 & Q4 & Q5) & QBIG & QDEF & QVIS & _).
  assert (SP0 : 0 <= sp < 2 ^ 64) by (clear - SPR; lia). assert (OVR : 0 <= ov < 2 ^ 64) by (clear - OR; lia). assert (OKR : 0 <= osk < 2 ^ 64) by (clear - KR; lia).
  assert (OECR : 0 <= oec < 2 ^ 64) by (clear - OR Eov Eoec; lia). assert (RR : 0 <= r < 2 ^ 64) by (clear - Hr1; lia).
  assert (SF : sfacts 32 sp MV) by (split; [exact IC0|]; split; [exact CSBv|]; split; [exact CUARv|]; split; [exact SPR|]; split; [exact A16'| exact SWR]).
  assert (EF : efacts 32 sp ov osk MV).
  { split; [exact OR|]. split; [exact O8|]. split; [exact OBIG|]. split; [exact Zov|]. split; [exact OWR|]. split; [exact ODJ|]. split; [exact Z8|]. split; [exact Z16|]. split; [exact Z48|].
    split; [exact U8v|]. split; [exact KR|]. split; [exact K8| exact U16]. }
  rewrite HDEP in U48.
  unfold PMSPA.cfg.
  destruct (Z_le_gt_dec xedepth 1023) as [DOK|DERR].
  -
    destruct (RUNA fx R MV sp ov osk xedepth r SP0 OVR OKR ltac:(clear - ED; unfold MAX_DEPTH in ED; lia) RR G2 G10 G1 SF EF U48 ltac:(clear - ED DOK; lia))
      as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & UKD & UD1 & C24 & C16 & C8).
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R E0 R1 EPUSH M1v (fun a0 => (sp - 32 <= a0 < sp - 32 + 32) \/ (ov + 48 <= a0 < ov + 52)) K HH AM MS1 MG1).
    { intros a0 Ha0 Hn. apply FRZ1; [exact Ha0| intros Y; apply Hn; left; exact Y| intros Y; apply Hn; right; exact Y]. }
    { intros a0 Ha0 [Wa|Wa].
      - split; [| clear - Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
      - split; [| clear - Wa Eov F1 F2 F6 FSIMG; lia]. unfold aclientw, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|].
        cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. split; [clear - Wa Eov; lia| intros Y; clear - Wa Y Eov; lia]. }
    intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
    assert (FCM1 : FC M1).
    { rewrite <- VIS1 in C8, C16, C24. unfold FC. split; [apply RB; [clear; lia| clear; lia| exact C8]|]. split; [apply RB; [clear; lia| clear; lia| exact C16]| apply RB; [clear; lia| clear; lia| exact C24]]. }
    assert (UD1' : L5.u32_at RSEGS M1 (ov + 48) (xedepth + 1)).
    { rewrite <- VIS1 in UD1. exact (proj1 (L5A.u32_at_vis H M1 (ov + 48) _ (L5A.avis_sub H ov 56 (ov + 48) 4 QVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - OR; lia) ltac:(clear - OR; lia)) UD1). }
    pose proof (K_startw M1 md1 (xedepth + 1) MGM1 ltac:(intros i Hi N1 N2; apply FR1; [exact Hi| intros [Y|Y]; [exact (N1 Y)| exact (N2 Y)]]) FCM1 HH1 AM1 MRT1 UD1' ltac:(clear - ED DOK; unfold MAX_DEPTH in *; lia)) as INV1.
    assert (QCS1 : forall j, In j CSKa -> getr R1 (reg j) = getr R (reg j)) by (intros jj Hjj; exact (KS1 jj Hjj)).

    pose proof EPK as EPX. unfold PECEPX.epush_k_spec in EPX.
    assert (UKD' : L5.u32_at RSEGS M1 (sp - 32) KD).
    { rewrite <- VIS1 in UKD. exact (proj1 (L5A.u32_at_vis H M1 (sp - 32) KD (VIS (sp - 32) 4 ltac:(clear - SLO; lia) ltac:(clear - SHI SPT; lia)) ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia)) UKD). }
    pose proof INV1 as (_ & ASTK1 & SZ1 & _).
    apply (K_epush 0xb0de0 0 EPRA (PECEPA.ecells_k RSEGS ar) (EI KD 0 0) fx1 R1 M1 md1 LK Aw cr k _ EPX INV1
             ltac:(cbn [PEC.en_stk]; rewrite HSTK, length_rev; exact ELEN) (proj1 RAS) T1 T2 T10 QCS1).
    {
      exists (sp - 32), KD. split; [exact T11|]. split; [clear - A16; Lia.lia|].
      split. { unfold PMSPA.accA, aacc. intros a Ha. left. apply (PESHZ.bat0_of_shadow_zero M1 (sp - 20480) 2560 a SZ1); [apply (PEAEKG.SPd8 sp SP32); reflexivity| clear - Ha; lia| clear - Ha; lia]. }
      split. { split; [right; clear - SHI SPT; lia| clear - ODJ; lia]. }
      split; [apply (PESHZ.bat0_of_shadow_zero M1 (sp - 20480) 2560 (sp - 32) SZ1); [apply (PEAEKG.SPd8 sp SP32); reflexivity| clear; lia| clear; lia]|].
      split; [exact UKD'|]. split; [exact HKD| reflexivity]. }
    intros fx2 R2 M2 md2 LK2 Aw2 cr2 en2 INV2 HSTK2 HED2 RP12. cbn [PEC.en_stk PEC.en_depth] in HSTK2, HED2.

    pose proof (K_vis M2 md2 LK2 Aw2 cr2 k 0 en2 INV2) as VF2. cbv beta in VF2.
    destruct VF2 as (IC2 & CSB2 & CUAR2 & _ & _ & SWR2 & _ & _ & _ & Zov2 & OWR2 & _ & Z82 & Z162 & Z482 & U82 & _ & _ & _ & U162 & U482 & _ & RB2 & FC2).
    set (H2 := ahid Aw2 md2) in *. set (MV2 := mrestrict H2 M2) in *.
    assert (SF2 : sfacts 32 sp MV2) by (split; [exact IC2|]; split; [exact CSB2|]; split; [exact CUAR2|]; split; [exact SPR|]; split; [exact A16'| exact SWR2]).
    assert (EF2 : efacts 32 sp ov osk MV2).
    { split; [exact OR|]. split; [exact O8|]. split; [exact OBIG|]. split; [exact Zov2|]. split; [exact OWR2|]. split; [exact ODJ|]. split; [exact Z82|]. split; [exact Z162|]. split; [exact Z482|].
      split; [exact U82|]. split; [exact KR|]. split; [exact K8| exact U162]. }
    pose proof (fun jj Hjj => L5SAR.cs_of_preserved R1 R2 jj RP12 Hjj) as Rc.
    assert (LR2 : lregs R2 sp ov) by (split; [rewrite (Rc 2%nat) by inl; exact T2|]; split; [rewrite (Rc 8%nat) by inl; exact T8| rewrite (Rc 9%nat) by inl; exact T9]).
    assert (QCS2 : forall j, In j CSKa -> getr R2 (reg j) = getr R (reg j)) by (intros jj Hjj; rewrite (Rc jj (CSKall jj Hjj)); exact (QCS1 jj Hjj)).
    destruct (RUNP fx2 R2 MV2 sp ov osk SP0 OVR OKR LR2 SF2 EF2) as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & U1 & U10 & U11 & LR3 & UB).
    pose proof INV2 as (_ & _ & _ & _ & AM2 & _ & _ & HH2 & _).
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 md2 fx2 fx3 R2 EPRA R3 PBPC M3v (fun a0 => sp - 25 <= a0 < sp - 25 + 1) K HH2 AM2 MS3 MG3).
    { intros a0 Ha0 Hn. apply FRZ3; [exact Ha0| exact Hn]. }
    { intros a0 Ha0 Wa. split; [| clear - Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia]. }
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    pose proof (K_frame M2 M3 md2 md3 LK2 Aw2 cr2 k 0 (sp - 25) (sp - 25 + 1) en2 INV2 ltac:(clear; lia) ltac:(clear; lia) MGM3 FR3 (FC_but M2 M3 (sp - 25) (sp - 25 + 1) ltac:(clear; lia) FR3 FC2) HH3 AM3 MRT3) as INV3.
    assert (QCS3 : forall j, In j CSKa -> getr R3 (reg j) = getr R (reg j)) by (intros jj Hjj; rewrite (KS3 jj Hjj); exact (QCS2 jj Hjj)).

    pose proof HB as HB1. rewrite (XF_ok ltac:(clear - DOK; unfold MAX_DEPTH; lia)) in HB1. cbn [s_hi] in HB1.
    apply (K_pb 0 (sp - 25) (xhi + 1) PBRA fx3 R3 M3 md3 LK2 Aw2 cr2 k en2 INV3 HB1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) (proj1 (proj2 RAS)) U1 (proj1 LR3) U10 U11 QCS3).
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 RP34.

    pose proof (K_vis M4 md4 LK4 Aw4 cr4 k4 (0 + 1) en2 INV4) as VF4. cbv beta in VF4.
    destruct VF4 as (IC4 & CSB4 & CUAR4 & _ & _ & SWR4 & _ & _ & _ & Zov4 & OWR4 & _ & Z84 & Z164 & Z484 & U84 & _ & _ & _ & U164 & U484 & _ & RB4 & FC4).
    set (H4 := ahid Aw4 md4) in *. set (MV4 := mrestrict H4 M4) in *.
    assert (SF4 : sfacts 32 sp MV4) by (split; [exact IC4|]; split; [exact CSB4|]; split; [exact CUAR4|]; split; [exact SPR|]; split; [exact A16'| exact SWR4]).
    assert (EF4 : efacts 32 sp ov osk MV4).
    { split; [exact OR|]. split; [exact O8|]. split; [exact OBIG|]. split; [exact Zov4|]. split; [exact OWR4|]. split; [exact ODJ|]. split; [exact Z84|]. split; [exact Z164|]. split; [exact Z484|].
      split; [exact U84|]. split; [exact KR|]. split; [exact K8| exact U164]. }
    pose proof (fun jj Hjj => L5SAR.cs_of_preserved R3 R4 jj RP34 Hjj) as Rc4.
    assert (LR4 : lregs R4 sp ov) by (destruct LR3 as (I2 & I8 & I9); split; [rewrite (Rc4 2%nat) by inl; exact I2|]; split; [rewrite (Rc4 8%nat) by inl; exact I8| rewrite (Rc4 9%nat) by inl; exact I9]).
    assert (QCS4 : forall j, In j CSKa -> getr R4 (reg j) = getr R (reg j)) by (intros jj Hjj; rewrite (Rc4 jj (CSKall jj Hjj)); exact (QCS3 jj Hjj)).
    destruct FC4 as (C84 & C164 & C244).
    destruct (RUNR fx4 R4 R MV4 sp r SP0 (proj1 LR4) SF4 (RB4 (sp - 8) r ltac:(clear; lia) ltac:(clear; lia) C84) (RB4 (sp - 16) (bv_unsigned (getr R (reg 8))) ltac:(clear; lia) ltac:(clear; lia) C164) (RB4 (sp - 24) (bv_unsigned (getr R (reg 9))) ltac:(clear; lia) ltac:(clear; lia) C244)
                Rra Rsp RAok ltac:(intros jj Hjj; exact (QCS4 jj Hjj))) as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & T105 & RP5).
    exact (K_fro 1 PBRA fx4 R4 M4 md4 LK4 Aw4 cr4 k4 fx5 R5 M5v en2 (EI KD 0 0 :: xestk) (xedepth + 1) INV4 ltac:(rewrite HSTK2, HSTK; cbn [rev]; reflexivity) ltac:(rewrite HED2; reflexivity)
             (XF_ok ltac:(clear - DOK; unfold MAX_DEPTH; lia)) MS5 MG5 FRZ5 RP5).
  -
    assert (D1024 : xedepth = 1024) by (clear - ED DERR; unfold MAX_DEPTH in ED; lia). rewrite D1024 in U48.
    destruct (RUNE fx R MV sp ov osk oec r SP0 OVR OKR OECR RR G2 G10 A13 G1 SF EF U48)
      as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & UD1 & C24 & C16 & C8).
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R E0 R1 MKPC M1v (fun a0 => (sp - 32 <= a0 < sp - 32 + 32) \/ (ov + 48 <= a0 < ov + 52)) K HH AM MS1 MG1).
    { intros a0 Ha0 Hn. apply FRZ1; [exact Ha0| intros Y; apply Hn; left; exact Y| intros Y; apply Hn; right; exact Y]. }
    { intros a0 Ha0 [Wa|Wa].
      - split; [| clear - Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
      - split; [| clear - Wa Eov F1 F2 F6 FSIMG; lia]. unfold aclientw, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|].
        cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. split; [clear - Wa Eov; lia| intros Y; clear - Wa Y Eov; lia]. }
    intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
    assert (FCM1 : FC M1).
    { rewrite <- VIS1 in C8, C16, C24. unfold FC. split; [apply RB; [clear; lia| clear; lia| exact C8]|]. split; [apply RB; [clear; lia| clear; lia| exact C16]| apply RB; [clear; lia| clear; lia| exact C24]]. }
    assert (UD1' : L5.u32_at RSEGS M1 (ov + 48) 1025).
    { rewrite <- VIS1 in UD1. exact (proj1 (L5A.u32_at_vis H M1 (ov + 48) _ (L5A.avis_sub H ov 56 (ov + 48) 4 QVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - OR; lia) ltac:(clear - OR; lia)) UD1). }
    pose proof (K_startw M1 md1 1025 MGM1 ltac:(intros i Hi N1 N2; apply FR1; [exact Hi| intros [Y|Y]; [exact (N1 Y)| exact (N2 Y)]]) FCM1 HH1 AM1 MRT1 UD1' ltac:(unfold MAX_DEPTH; clear; lia)) as INV1.
    assert (QCS1 : forall j, In j CSKa -> getr R1 (reg j) = getr R (reg j)) by (intros jj Hjj; exact (KS1 jj Hjj)).
    apply (K_mkec 0 MKRA 11 fx1 R1 M1 md1 LK Aw cr k _ INV1 (proj2 (proj2 RAS)) ltac:(clear; lia) T1 T2 T10 T11 QCS1).
    intros fx2 R2 M2 md2 LK2 Aw2 INV2 RP12.

    pose proof (PEAEKG.vis_facts_e L ar C HI P LY HIok 32 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC M2 md2 LK2 Aw2 cr k 0 _ 11 INV2) as VF2. cbv beta in VF2.
    destruct VF2 as (IC2 & CSB2 & CUAR2 & _ & _ & SWR2 & RB2 & FC2).
    set (H2 := ahid Aw2 md2) in *. set (MV2 := mrestrict H2 M2) in *.
    assert (SF2 : sfacts 32 sp MV2) by (split; [exact IC2|]; split; [exact CSB2|]; split; [exact CUAR2|]; split; [exact SPR|]; split; [exact A16'| exact SWR2]).
    pose proof (fun jj Hjj => L5SAR.cs_of_preserved R1 R2 jj RP12 Hjj) as Rc.
    assert (G2' : getr R2 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (Rc 2%nat) by inl; exact T2).
    assert (QCS2 : forall j, In j CSKa -> getr R2 (reg j) = getr R (reg j)) by (intros jj Hjj; rewrite (Rc jj (CSKall jj Hjj)); exact (QCS1 jj Hjj)).
    destruct FC2 as (C82 & C162 & C242).
    destruct (RUNX fx2 R2 R MV2 sp r SP0 G2' SF2 (RB2 (sp - 8) r ltac:(clear; lia) ltac:(clear; lia) C82) (RB2 (sp - 16) (bv_unsigned (getr R (reg 8))) ltac:(clear; lia) ltac:(clear; lia) C162) (RB2 (sp - 24) (bv_unsigned (getr R (reg 9))) ltac:(clear; lia) ltac:(clear; lia) C242)
                Rra Rsp RAok ltac:(intros jj Hjj; exact (QCS2 jj Hjj))) as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & T105 & RP5).
    exact (K_ferr 0 MKRA fx2 R2 M2 md2 LK2 Aw2 cr k fx5 R5 M5v (PEC.ENC (PEC.en_b en) (PEC.en_k en) (PEC.en_stk en) 1025) 11 xestk (xedepth + 1) INV2 ltac:(clear; lia)
             ltac:(cbn [PEC.en_stk]; exact HSTK) ltac:(cbn [PEC.en_depth]; rewrite D1024; reflexivity) (XF_err ltac:(rewrite D1024; reflexivity)) MS5 MG5 FRZ5 RP5).
Qed.
End Call.
End Slot.

Local Ltac row E0 EPRA PBRA MKRA KD MK uA uE uP uR uX :=
  intros PMODE a fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 A13 CPRE INCS POK MP NB HB CRED KONT;
  rewrite L5K.rl13 in A13; destruct X as [xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad];
  refine (main E0 EPRA PBRA MKRA KD MK ltac:(unfold L5.ra_ok; clear; lia) ltac:(clear; lia) uA uE uP uR uX PMODE fx R M model K LBX FF LK Aw cr sp r fb cat p
            xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 A13 CPRE INCS MP HB CRED KONT).

Theorem v_begin_arr_ok : PECSA.v_begin_arr_spec L ar HI P.
Proof.
  unfold PECSA.v_begin_arr_spec, PECSPA.v_begin_arr_spec, PECSPA.eslot_spec, PECSPA.args_t3. cbn [pe_begin_arr EE PeCLayoutA.EADDR_A].
  row 0xabff4 0xac064 0xac08c 0xac0b0 3 91 u_runA_a u_runE_a u_runP_a u_runR_a u_runX_a.
Qed.

Theorem v_begin_obj_ok : PECSA.v_begin_obj_spec L ar HI P.
Proof.
  unfold PECSA.v_begin_obj_spec, PECSPA.v_begin_obj_spec, PECSPA.eslot_spec, PECSPA.args_t3. cbn [pe_begin_obj EE PeCLayoutA.EADDR_A].
  row 0xab904 0xab974 0xab99c 0xab9c0 1 123 u_runA_o u_runE_o u_runP_o u_runR_o u_runX_o.
Qed.
End WithHeap.

End PEAENCBG.
