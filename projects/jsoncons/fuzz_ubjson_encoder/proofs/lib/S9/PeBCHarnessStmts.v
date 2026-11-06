(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx LibIface LibIfaceAB LibIfaceAE L5Defs L5Core L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA PnLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA PmSpecs PmSpecsA PeSpecsAb PeStepAB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCStatics PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeTopAL PeCTopB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEBCH.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.

Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64.
Proof. unfold U. pose proof (bv_unsigned_in_range _ (getr R (reg k))) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Definition FR5 : Z := 1152.
Definition RFR : Z := 160.
Abbreviation STK := PECTB.STK.

Definition tfrk (S : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (U R 1) /\ L5.u64_at RSEGS M (S - 16) (U R 8) /\ L5.u64_at RSEGS M (S - 24) (U R 9)
  /\ L5.u64_at RSEGS M (S - 32) (U R 18) /\ L5.u64_at RSEGS M (S - 40) (U R 19) /\ L5.u64_at RSEGS M (S - 48) (U R 20) /\ L5.u64_at RSEGS M (S - 56) (U R 21)
  /\ L5.u64_at RSEGS M (S - 64) (U R 22) /\ L5.u64_at RSEGS M (S - 72) (U R 23) /\ L5.u64_at RSEGS M (S - 80) (U R 24) /\ L5.u64_at RSEGS M (S - 88) (U R 25)
  /\ L5.u64_at RSEGS M (S - 96) (U R 26) /\ L5.u64_at RSEGS M (S - 104) (U R 27).
Definition tocell (S : Z) (a : Z) : Prop := S - 104 <= a < S.
Lemma tfrk_agree S R M1 M1' : 4096 <= S - 104 -> S <= 2 ^ 47 -> tfrk S R M1 -> (forall a, tocell S a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> tfrk S R M1'.
Proof.
  intros HS1 HS2 T AG.
  assert (K : forall o v, 8 <= o <= 104 -> L5.u64_at RSEGS M1 (S - o) v -> L5.u64_at RSEGS M1' (S - o) v).
  { intros o v Ho Hv. apply (L5C.u64_at_agree RSEGS M1 M1'); [| lia| lia| exact Hv]. intros i Hi. apply AG. unfold tocell. lia. }
  destruct T as (T1 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27).
  repeat split; apply K; try assumption; lia.
Qed.

Definition rinvH (R0 Rc : bvmap 5 word) (V2 F SB : Z) : Prop :=
  getr Rc (reg 2) = Z_to_bv 64 V2 /\ getr Rc (reg 3) = getr R0 (reg 3) /\ getr Rc (reg 4) = getr R0 (reg 4)
  /\ getr Rc (reg 8) = Z_to_bv 64 (U R0 2 + 0) /\ getr Rc (reg 9) = Z_to_bv 64 V2
  /\ getr Rc (reg 19) = Z_to_bv 64 (F / 8 + SB) /\ getr Rc (reg 21) = Z_to_bv 64 (F + 96)
  /\ getr Rc (reg 26) = Z_to_bv 64 F /\ getr Rc (reg 27) = Z_to_bv 64 SB.
Definition HIDX : list nat := [2; 3; 4; 8; 9; 19; 21; 26; 27]%nat.
Lemma rinvH_keep R0 Ra Rb V2 F SB : rinvH R0 Ra V2 F SB -> (forall k, In k HIDX -> getr Rb (reg k) = getr Ra (reg k)) -> rinvH R0 Rb V2 F SB.
Proof.
  intros (X2 & X3 & X4 & X8 & X9 & X19 & X21 & X26 & X27) K. unfold rinvH.
  rewrite (K 2%nat), (K 3%nat), (K 4%nat), (K 8%nat), (K 9%nat), (K 19%nat), (K 21%nat), (K 26%nat), (K 27%nat) by (cbn; tauto).
  repeat split; assumption.
Qed.
Lemma rinvH_ks R0 Ra Rb V2 F SB (KSL : list nat) : rinvH R0 Ra V2 F SB -> (forall k, In k KSL -> getr Rb (reg k) = getr Ra (reg k)) ->
  incl HIDX KSL -> rinvH R0 Rb V2 F SB.
Proof. intros RI KS INC. apply (rinvH_keep R0 Ra Rb V2 F SB RI). intros k Hk. apply KS. apply INC. exact Hk. Qed.
Lemma rinvH_pres R0 Ra Rb V2 F SB : rinvH R0 Ra V2 F SB -> regs_preserved Ra Rb -> rinvH R0 Rb V2 F SB.
Proof.
  intros RI RP. apply (rinvH_keep R0 Ra Rb V2 F SB RI). intros k Hk. apply RP. unfold callee_saved_idx.
  unfold HIDX in Hk. repeat (destruct Hk as [<-|Hk]; [cbn; tauto|]). destruct Hk.
Qed.

Definition WF : list L5.range := map (fun iv => (fst iv, snd iv - fst iv)) PNTAL.foot_b.
Lemma WF_eq : WF = [(0x678780, 2); (0x6789b0, 2); (0x6789b2, 1854); (0x679818, 88); (0x69a1d0, 544)].
Proof. unfold WF. rewrite PNTAL.foot_b_eq. reflexivity. Qed.
Lemma wapp_WF : PMKB.wapp WF.
Proof. intros r Hr. rewrite WF_eq in Hr. cbn in Hr. unfold BIGSHADOW_LO, BIGSHADOW_HI. repeat (destruct Hr as [<-|Hr]; [cbn; lia|]). destruct Hr. Qed.

Section Call.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface) (P : PESKA.sink_policyA).
Variable payload : list byte.
Variable F : Z.

Definition n : Z := Z.of_nat (length payload).
Definition p : list Z := map bv_unsigned payload.
Abbreviation HV := (PMSPA.HV L ar).
Abbreviation scA := (PMSPA.scA L).
Abbreviation accA := PMSPA.accA.
Abbreviation vstr_at := (PM.vstr_at RSEGS accA).
Abbreviation iss_at := (PM.iss_at RSEGS AD accA).
Abbreviation parser_at := (PM.parser_at RSEGS AD accA PMSPA.annA).
Abbreviation enc_atA := (PECA.enc_atA RSEGS EE L ar).
Abbreviation sink_atA := (PESKA.sink_atA RSEGS L ar P).

Definition P0A : credit := PEC.credit_add (scA (PM.pot_call HV n)) (PEC.credit_add (scA (PEC.pot_estack HV 0)) (PESKA.spa_pot P 0)).

Definition restA1 : credit := PEC.credit_add (scA (PM.cost1 HV (n + 32))) (PEC.credit_add (scA (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV 32)))
                                (PEC.credit_add (scA (PM.pot_parser HV (PMSPA.pst_reset (PMSPA.parser_init 0 0)))) (PEC.credit_add (scA (PEC.pot_estack HV 0)) (PESKA.spa_pot P 0)))).
Definition restA2 : credit := PEC.credit_add (scA (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV 32)))
                                (PEC.credit_add (scA (PM.pot_parser HV (PMSPA.pst_reset (PMSPA.parser_init 0 0)))) (PEC.credit_add (scA (PEC.pot_estack HV 0)) (PESKA.spa_pot P 0))).
Definition restA3 : credit := PEC.credit_add (scA (PM.pot_parser HV (PMSPA.pst_reset (PMSPA.parser_init 0 0)))) (PEC.credit_add (scA (PEC.pot_estack HV 0)) (PESKA.spa_pot P 0)).
Lemma restA3_pot_allA qc b : restA3 = PECA.pot_allA L ar P (PMSPA.pst_reset (PMSPA.parser_init qc b)) PEC.enc0 PESK.sink0.
Proof. reflexivity. Qed.

Definition hs_pay (M : word -> option byte) (s : PM.vstr) : Prop :=
  vstr_at M (F + 32) s /\ PM.vs_size s = n /\ L5.bytes_at RSEGS M (PM.vs_data (F + 32) s) p /\ (forall c n' q, s = PM.VLong c n' q -> 23 <= n').

Definition his_pay (M : word -> option byte) (s2 : PM.vstr) (sm : PM.strm) : Prop :=
  iss_at M (F + 96) s2 sm /\ PM.vs_size s2 = n /\ PM.sm_g sm = PM.vs_data (F + 176) s2 /\ PM.sm_st sm = 0 /\ L5.bytes_at RSEGS M (PM.vs_data (F + 176) s2) p.

Definition hse0 (M : word -> option byte) : Prop := sink_atA M (F + 432) PESK.sink0 /\ enc_atA M (F + 496) F PEC.enc0.

Definition hrun0 (M : word -> option byte) (qc b : Z) (s2 : PM.vstr) (sm : PM.strm) (e : bool) (cat : Z) : Prop :=
  PECA.crun_preA RSEGS AD AAD EE L ar P M F p UbjRef.init (PMSPA.pst_reset (PMSPA.parser_init qc b)) s2 sm PEC.enc0 PESK.sink0 e cat.

Definition hparsed (M : word -> option byte) (s' : PM.pst) (s2 : PM.vstr) (sm' : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool) (nn : nat) : Prop :=
  parser_at M (F + 592) (F + 96) s' /\ iss_at M (F + 96) s2 sm' /\ enc_atA M (F + 496) F en /\ sink_atA M (F + 432) k
  /\ PMSTA.base_okA RSEGS AD M /\ PESTA.err_okA RSEGS AD AAD EE M e /\ L5.defined M (F + 1120) 16
  /\ halted (run nn p UbjRef.init) = true /\ s_lo (run nn p UbjRef.init) <= PESK.sk_z k <= s_hi (run nn p UbjRef.init).

Lemma frame_ok5_of (FF : list fframe) (rs : Z) : In (F, 5, rs) FF -> F mod 2048 = 0 -> PECA.frame_ok5 FF F.
Proof. intros H1 H2. split; [exists rs; exact H1| exact H2]. Qed.
End Call.
End PEBCH.
