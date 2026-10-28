(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5CoreSpecsAB0S9 L5StepARB0S9 L5CoreBRB0S9 L5ADetailHRB0S9.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAb PnStatics PmModelFactsA PmStep PeStepAB0 PmParStep PmParKit PeBSrcKit PeBParKit LibIfaceAB.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCFrameA PeCValSpecA PeCRdValD PeCRdKeyD PeBCReset1 PeBSrcRead1 PmBUarK PmBUar PeBRdKeyP.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_b8e04_b8e08.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBCRDKEY.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.

Definition own (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R (reg 8)))
  /\ L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R (reg 18)))
  /\ L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R (reg 20)))
  /\ L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R (reg 22)))
  /\ L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R (reg 24)))
  /\ L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R (reg 25))) /\ L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R (reg 26))).
Definition ocell (E : Z) (a : Z) : Prop := E - 96 <= a < E.
Lemma own_agree E R M1 M1' : 0 <= E - 96 -> E <= 2 ^ 64 ->
  own E R M1 -> (forall a, ocell E a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own E R M1'.
Proof.
  intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12) AG. unfold own, ocell in *.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.

Definition zrun (pc0 : Z) : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (E op ov oec F fl : Z),
  0 <= E < 2 ^ 64 -> 0 <= op < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 1))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 8))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 9))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 18))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 19))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 20))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 21))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 22))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 23))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 24))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 25))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 26))) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (E - 128) -> getr R (reg 8) = Z_to_bv 64 E -> getr R (reg 9) = Z_to_bv 64 (E - 128) -> getr R (reg 18) = Z_to_bv 64 F -> getr R (reg 19) = Z_to_bv 64 op -> getr R (reg 20) = Z_to_bv 64 oec -> getr R (reg 21) = Z_to_bv 64 ov -> getr R (reg 24) = Z_to_bv 64 F -> getr R (reg 25) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= E <= 140737488355328 -> E mod 32 = 0 -> L5.writable RSEGS M (E - 128) 128 -> 6930432 <= op <= 140737488354944 ->
  op mod 8 = 0 -> (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784) -> L5KA.zeros_at M ((op / 8) + 2147450880) 3 -> L5KA.zeros_at M (((op + 32) / 8) + 2147450880) 44 ->
  L5KA.zeros_at M (((op + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M op 384 -> ((E - 128) + 128 <= op \/ op + 384 <= (E - 128)) -> (op + 384 <= F \/ F + 64 <= op) ->
  (op + 384 <= fl \/ fl + 1 <= op) -> (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880)) -> 6930432 <= F <= 140737488355264 -> F mod 32 = 0 ->
  L5.defined M F 64 -> L5.writable RSEGS M F 64 -> (2147446784 + 17592186048512 <= F \/ F + 64 <= 2147446784) -> L5.writable RSEGS M ((F / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M (F + 56) fl -> 4096 <= fl <= 140737488355327 -> L5.writable RSEGS M fl 1 -> (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) ->
  (F + 64 <= fl \/ fl + 1 <= F) -> ((E - 128) + 128 <= F \/ F + 64 <= (E - 128)) -> ((E - 128) + 128 <= fl \/ fl + 1 <= (E - 128)) -> (op + 384 <= F \/ F + 64 <= op) ->
  (op + 384 <= fl \/ fl + 1 <= op) -> (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880)) -> L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R0 (reg 1))) -> L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R0 (reg 8))) ->
  L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R0 (reg 9))) -> L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R0 (reg 18))) -> L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R0 (reg 19))) -> L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R0 (reg 20))) ->
  L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R0 (reg 21))) -> L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R0 (reg 22))) -> L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R0 (reg 23))) -> L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R0 (reg 24))) ->
  L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R0 (reg 25))) -> L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R0 (reg 26))) ->
    exists fx' R' M', mem_grows M M'
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 9) -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 8) -> i <> fl ->
          M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 0xb8e54) M' (seg_rom RSEGS))
    /\ (forall j, In j [3; 4; 27]%nat -> getr R' (reg j) = getr R (reg j))
    /\ (forall j, In j [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%nat -> getr R' (reg j) = getr R0 (reg j))
    /\ getr R' (reg 2) = Z_to_bv 64 E /\ L5.u8_at RSEGS M' fl 0 /\ L5.u8_at RSEGS M' (op + 8) 0.

Ltac zrun_tac Z_conc :=
  intros fx R R0 M E op ov oec F fl; intros;
  let P := fresh "P" in
  pose proof (Z_conc fx R M (fun j => match j with 2%nat => E | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
        | 64%nat => bv_unsigned (getr R0 (reg 1)) | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9))
        | 67%nat => bv_unsigned (getr R0 (reg 18)) | 68%nat => bv_unsigned (getr R0 (reg 19)) | 69%nat => bv_unsigned (getr R0 (reg 20))
        | 70%nat => bv_unsigned (getr R0 (reg 21)) | 71%nat => bv_unsigned (getr R0 (reg 22)) | 72%nat => bv_unsigned (getr R0 (reg 23))
        | 73%nat => bv_unsigned (getr R0 (reg 24)) | 74%nat => bv_unsigned (getr R0 (reg 25)) | 75%nat => bv_unsigned (getr R0 (reg 26)) | _ => 0 end)) as P;
  cbn beta iota in P;
  L5SAR.feed P ltac:(first [assumption | unfold PEBRDKEYP.aligned; assumption]);
  let fx' := fresh "fx'" in let R' := fresh "R'" in let M' := fresh "M'" in
  destruct P as (fx' & R' & M' & ?MG & _ & ?FRZ & ?MS & ?KS & ?E1 & ?E2 & ?E8 & ?E9 & _ & _ & ?E18 & ?E19 & ?E20 & ?E21 & ?E22 & ?E23 & ?E24 & ?E25 & ?E26 & ?FL0
                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & ?MO0 & _);
  exists fx', R', M';
  split; [assumption|];
  split; [intros i Hi N1 N2 N3 N4; match goal with FZ : forall i : Z, 0 <= i < 2 ^ 64 -> _ |- _ => apply FZ end;
          [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia]|];
  split; [assumption|];
  split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with KS0 : forall x, In x _ -> _ |- _ => apply KS0; inl end|]); destruct Hj|];
  split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr _ (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj|];
  split; [assumption|]; split; assumption.

Lemma z1_run : zrun 0xb8da4. Proof. unfold zrun. zrun_tac PEBRDKEYP.arkZ1_conc. Qed.
Lemma z7_run : zrun 0xb8d78. Proof. unfold zrun. zrun_tac PEBRDKEYP.arkZ7_conc. Qed.
Lemma z12_run : zrun 0xb8f04. Proof. unfold zrun. zrun_tac PEBRDKEYP.arkZ12_conc. Qed.
Definition krun : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (E op ov oec F fl : Z),
  0 <= E < 2 ^ 64 -> 0 <= op < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 1))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 8))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 9))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 18))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 19))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 20))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 21))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 22))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 23))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 24))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 25))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 26))) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (E - 128) -> getr R (reg 8) = Z_to_bv 64 E -> getr R (reg 9) = Z_to_bv 64 (E - 128) -> getr R (reg 18) = Z_to_bv 64 F -> getr R (reg 19) = Z_to_bv 64 op -> getr R (reg 20) = Z_to_bv 64 oec -> getr R (reg 21) = Z_to_bv 64 ov -> getr R (reg 24) = Z_to_bv 64 F -> getr R (reg 25) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= E <= 140737488355328 -> E mod 32 = 0 -> L5.writable RSEGS M (E - 128) 128 -> 6930432 <= op <= 140737488354944 ->
  op mod 8 = 0 -> (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784) -> L5KA.zeros_at M ((op / 8) + 2147450880) 3 -> L5KA.zeros_at M (((op + 32) / 8) + 2147450880) 44 ->
  L5KA.zeros_at M (((op + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M op 384 -> ((E - 128) + 128 <= op \/ op + 384 <= (E - 128)) -> (op + 384 <= F \/ F + 64 <= op) ->
  (op + 384 <= fl \/ fl + 1 <= op) -> (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880)) -> 6930432 <= F <= 140737488355264 -> F mod 32 = 0 ->
  L5.defined M F 64 -> L5.writable RSEGS M F 64 -> (2147446784 + 17592186048512 <= F \/ F + 64 <= 2147446784) -> L5.writable RSEGS M ((F / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M (F + 56) fl -> 4096 <= fl <= 140737488355327 -> L5.writable RSEGS M fl 1 -> (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) ->
  (F + 64 <= fl \/ fl + 1 <= F) -> ((E - 128) + 128 <= F \/ F + 64 <= (E - 128)) -> ((E - 128) + 128 <= fl \/ fl + 1 <= (E - 128)) -> (op + 384 <= F \/ F + 64 <= op) ->
  (op + 384 <= fl \/ fl + 1 <= op) -> (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880)) -> L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R0 (reg 1))) -> L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R0 (reg 8))) ->
  L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R0 (reg 9))) -> L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R0 (reg 18))) -> L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R0 (reg 19))) -> L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R0 (reg 20))) ->
  L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R0 (reg 21))) -> L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R0 (reg 22))) -> L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R0 (reg 23))) -> L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R0 (reg 24))) ->
  L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R0 (reg 25))) -> L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R0 (reg 26))) -> L5.u8_at RSEGS M (op + 16) 0 ->
    exists fx' R' M', mem_grows M M'
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 9) -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 8) -> i <> fl ->
          M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 0xb8ea8) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 0xb8e54) M' (seg_rom RSEGS))
    /\ (forall j, In j [3; 4; 27]%nat -> getr R' (reg j) = getr R (reg j))
    /\ (forall j, In j [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%nat -> getr R' (reg j) = getr R0 (reg j))
    /\ getr R' (reg 2) = Z_to_bv 64 E /\ L5.u8_at RSEGS M' fl 0 /\ L5.u8_at RSEGS M' (op + 8) 1.

Ltac krun_tac Z_conc :=
  intros fx R R0 M E op ov oec F fl; intros;
  let P := fresh "P" in
  pose proof (Z_conc fx R M (fun j => match j with 2%nat => E | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
        | 64%nat => bv_unsigned (getr R0 (reg 1)) | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9))
        | 67%nat => bv_unsigned (getr R0 (reg 18)) | 68%nat => bv_unsigned (getr R0 (reg 19)) | 69%nat => bv_unsigned (getr R0 (reg 20))
        | 70%nat => bv_unsigned (getr R0 (reg 21)) | 71%nat => bv_unsigned (getr R0 (reg 22)) | 72%nat => bv_unsigned (getr R0 (reg 23))
        | 73%nat => bv_unsigned (getr R0 (reg 24)) | 74%nat => bv_unsigned (getr R0 (reg 25)) | 75%nat => bv_unsigned (getr R0 (reg 26)) | _ => 0 end)) as P;
  cbn beta iota in P;
  L5SAR.feed P ltac:(first [assumption | unfold PEBRDKEYP.aligned; assumption]);
  let fx' := fresh "fx'" in let R' := fresh "R'" in let M' := fresh "M'" in
  destruct P as (fx' & R' & M' & ?MG & _ & ?FRZ & ?MS & ?KS & ?E1 & ?E2 & ?E8 & ?E9 & _ & _ & _ & ?E18 & ?E19 & ?E20 & ?E21 & ?E22 & ?E23 & ?E24 & ?E25 & ?E26 & ?FL0
                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & ?MO0 & _);
  exists fx', R', M';
  split; [assumption|];
  split; [intros i Hi N1 N2 N3 N4; match goal with FZ : forall i : Z, 0 <= i < 2 ^ 64 -> _ |- _ => apply FZ end;
          [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia]|];
  split; [assumption|];
  split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with KS0 : forall x, In x _ -> _ |- _ => apply KS0; inl end|]); destruct Hj|];
  split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr _ (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj|];
  split; [assumption|]; split; assumption.

Lemma k2_run : krun. Proof. unfold krun. krun_tac PEBRDKEYP.arkK2_conc. Qed.

Lemma credit_le_keep p1 c1 c2 p2 : PMSP.credit_le p1 c1 -> PMSP.credit_keep c1 c2 p1 p2 -> PMSP.credit_le p2 c2.
Proof. unfold PMSP.credit_le, PMSP.credit_keep. lia. Qed.
Lemma credit_keep_trans c1 c2 c3 p1 p2 p3 : PMSP.credit_keep c1 c2 p1 p2 -> PMSP.credit_keep c2 c3 p2 p3 -> PMSP.credit_keep c1 c3 p1 p3.
Proof. unfold PMSP.credit_keep. lia. Qed.

Lemma div8_off F a k : F / 8 * 8 = F -> F + 8 * k <= a < F + 8 * k + 8 -> a / 8 = F / 8 + k.
Proof. intros E H. symmetry. apply (Z.div_unique a 8 (F / 8 + k) (a - F - 8 * k)); lia. Qed.

Lemma frame_ok5_push FF fb f : PECA.frame_ok5 FF fb -> PECA.frame_ok5 (f :: FF) fb.
Proof. intros ((r0 & Hf) & Hm). split; [exists r0; right; exact Hf| exact Hm]. Qed.

Tactic Notation "wr_mem" integer(n) := unfold PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W; cbn [app]; do n right; left; reflexivity.
Ltac wr_rng := unfold L5.in_rng, PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_v, PESK.o_sink;
  cbn [fst snd pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutB.CADDR_B PeCLayoutB.EADDR_B].

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMB.ly_as0 L C LY.

Lemma content_keepA' LB FF sp scr W M M' fb p s str sm op :
  L5SAR.ek L ar LB FF sp scr W M M' -> PMKB.wapp W ->
  (forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  PMSPA.aobjA FF (PMSPA.o_is AD fb) 272 -> (forall i, PMSPA.o_is AD fb + 80 <= i < PMSPA.o_is AD fb + 80 + 24 -> L5.outside W i) ->
  incl (PM.vs_own str) LB -> In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB ->
  (forall q m, In (q, m) LB -> PMKB.blk_out W q m) ->
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

Hypothesis GL : PECSB.get_length_spec L ar HI P.
Hypothesis RS : PECSB.read_span_spec L ar HI.
Hypothesis VAL : PECVSA.validate_fun_spec RSEGS AD L ar HI (pa_validate AD).
Hypothesis MKE : PECSB.make_ec_spec L ar HI.
Hypothesis VK : PECSB.v_key_spec L ar HI P.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
          (cr : credit) (sp r fb cat : Z) (p : list Z) (X : st) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 7.
Hypothesis FRM : PMSPA.ffroomA 7 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_p AD fb).
Hypothesis A11 : getr R 11%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis A12 : getr R 12%bv = Z_to_bv 64 (PMSPA.o_ec AD fb).
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis POK : PECSPA.payload_ok p.
Hypothesis MP : PECSPA.mp_run tt p X.
Hypothesis NB : s_bad (r_key p X) = false.
Hypothesis HB : PESKA.spa_hb P (s_hi (r_key p X)).
Hypothesis CRED : PMSP.credit_le (PECA.pot_allA L ar P s en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (s' : PM.pst) (sm' : PM.strm) (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (r_key p X) s' str sm' en' k' e' cat ->
        PMSPA.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 7) (PEC.W_crun AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_allA L ar P s en k) (PECA.pot_allA L ar P s' en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PEC.owned s' en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.
Let op := PMSPA.o_p AD fb. Let ov := PMSPA.o_v AD fb. Let oec := PMSPA.o_ec AD fb. Let ois := PMSPA.o_is AD fb. Let osk := PESK.o_sink EE fb. Let otb := PMSPA.o_tb AD fb.
Let WR := PEC.W_crun AD EE fb.

Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 7) with 26624 in ASTK, STKSH; change (26624 / 8) with 3328 in STKSH;
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp; rewrite L5K.rl3 in Rgp; rewrite L5K.rl4 in Rtp;
  pose proof FOK as ((rs & Hfb) & Fal);
  assert (Eop : op = fb + 592) by reflexivity; assert (Eov : ov = fb + 496) by reflexivity; assert (Eoec : oec = fb + 1120) by reflexivity;
  assert (Eois : ois = fb + 96) by reflexivity; assert (Eosk : osk = fb + 432) by reflexivity; assert (Eotb : otb = op + 336) by reflexivity;
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & _);
  pose proof (WF _ Hfb) as (F1 & F2 & F3 & F4 & F5 & F6); cbn [ff_addr ff_class fst snd] in F1, F2, F3, F4, F5, F6; change (ff_bytes 5) with 2048 in F1, F2, F3, F4, F5, F6;
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in FSAPP; unfold FS_BYTES in FSCEIL, F1, F2;
  assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n)
    by (intros a' n' H1' H2'; exists (fb, 5, rs); split; [exact Hfb|]; cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; lia);
  assert (FB8 : forall j, (fb + 8 * j) mod 8 = 0)
    by (intros j'; pose proof (Z.div_mod fb 2048 ltac:(lia)) as E'; rewrite Fal, Z.add_0_r in E'; rewrite E';
        replace (2048 * (fb / 2048) + 8 * j') with ((256 * (fb / 2048) + j') * 8) by lia; apply Z_mod_mult);
  assert (O8 : op mod 8 = 0) by (rewrite Eop; replace (fb + 592) with (fb + 8 * 74) by lia; apply FB8);
  assert (Q8 : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8);
  assert (I8 : ois mod 8 = 0) by (rewrite Eois; replace (fb + 96) with (fb + 8 * 12) by lia; apply FB8);
  assert (C8m : oec mod 8 = 0) by (rewrite Eoec; replace (fb + 1120) with (fb + 8 * 140) by lia; apply FB8);
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model op 384 sp 26624 HH (PMKB.aobj_of_aobjA FF op 384 (AOF op 384 ltac:(lia) ltac:(lia)) O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & _);
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ois 272 sp 26624 HH (PMKB.aobj_of_aobjA FF ois 272 (AOF ois 272 ltac:(lia) ltac:(lia)) I8) ltac:(lia) ltac:(reflexivity))
    as ((I1 & I2 & I3 & I4 & I5) & IBIG & _);
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model oec 16 sp 26624 HH (PMKB.aobj_of_aobjA FF oec 16 (AOF oec 16 ltac:(lia) ltac:(lia)) C8m) ltac:(lia) ltac:(reflexivity))
    as ((E1' & E2' & E3' & E4' & E5') & EBIG & _);
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH);
  assert (AOP : PMSPA.aobjA FF op 384) by (apply AOF; lia);
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply AOF; lia).

Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PMBUK.gctx L ar HI LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k).
Hypothesis APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n ->
  (a + n <= F \/ F + ff_bytes 0 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + ff_bytes 0 / 8 <= a) /\ (a + n <= fl \/ fl + 1 <= a).
Let FF' := (F, 0, sp - 128 + 32) :: FF.

Ltac frame_facts :=
  pose proof G as G'; destruct G' as [_ GSPT GSLO GSHI _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS];
  change (ff_bytes 0) with 64 in GFS2, GFCEIL, GFLC, GFR, GF8, GFBIG, GFLA, GNCF; unfold FS_BYTES in GFS2, GFLP.

Definition amid (fxi : FPState) (Ri : bvmap 5 word) (Mi : word -> option byte) (mdi : Model) (LKi : list fframe) (Awi : list (Z * Z)) (cri : credit)
           (si : PM.pst) (smi : PM.strm) (eni : PEC.enc) (ki : PESK.sink) (ei : bool) (Xi : st) : Prop :=
  (getr Ri (reg 2) = Z_to_bv 64 (sp - 128) /\ getr Ri (reg 8) = Z_to_bv 64 sp /\ getr Ri (reg 9) = Z_to_bv 64 (sp - 128) /\ getr Ri (reg 18) = Z_to_bv 64 F
   /\ getr Ri (reg 19) = Z_to_bv 64 op /\ getr Ri (reg 20) = Z_to_bv 64 oec /\ getr Ri (reg 21) = Z_to_bv 64 ov /\ getr Ri (reg 24) = Z_to_bv 64 F
   /\ getr Ri (reg 25) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr Ri (reg 26) = Z_to_bv 64 2147450880 /\ (forall j, In j [3; 4; 27]%nat -> getr Ri (reg j) = getr R (reg j)))
  /\ PMBUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned si eni ki) Mi mdi LKi cri Awi
  /\ PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat
  /\ PMSPA.src_step (PM.p_src s) (PM.p_src si) sm smi /\ (e = true -> ei = true)
  /\ PMSP.credit_keep cr cri (PECA.pot_allA L ar P s en k) (PECA.pot_allA L ar P si eni ki).

Lemma cpre_keepA LB sp0 scr0 W Mi Mj Xi si smi eni ki ei :
  L5SAR.ek L ar LB FF sp0 scr0 W Mi Mj -> PMKB.wapp W ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  incl (PEC.owned si eni ki) LB -> incl (PM.vs_own str) LB ->
  (forall i, fb + 32 <= i < fb + 2040 -> L5.outside W i) -> (forall a, a < 6930432 -> L5.outside W a) ->
  (forall q m, In (q, m) LB -> PMKB.blk_out W q m) ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat -> PECA.crun_preA RSEGS AD AAD EE L ar P Mj fb p Xi si str smi eni ki ei cat.
Proof.
  intros EK WAPP BRB OINC SINC OW OI OB CP. entry_facts.
  destruct CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (PINC : incl (PM.parser_own si) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; left; exact Hx).
  assert (EINC : incl (PEC.enc_own eni) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (KINC : incl (PESK.sink_own ki) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; right; apply in_or_app; right; exact Hx).
  assert (OWo : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> forall i, a <= i < a + n -> L5.outside W i) by (intros a n X1 X2 i Hi; apply OW; clear - X1 X2 Hi; lia).
  split.
  { apply (PMKB.parser_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB _ _ _ AOP); [exact PINC| apply OWo; clear - Eop; lia| | | | exact PA].
    - apply OB. apply PINC. unfold PM.parser_own, PM.src_own. left. reflexivity.
    - apply OB. apply PINC. unfold PM.parser_own, PM.vec_own. right. left. reflexivity.
    - intros c0 n0 p0 E0. apply OB. apply PINC. unfold PM.parser_own, PM.vs_own. rewrite E0. right. right. left. reflexivity. }
  split.
  { apply (PMKB.iss_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ois str smi AOI); [exact SINC| apply OWo; clear - Eois; lia| | exact IA].
    intros c0 n0 p0 E0. apply OB. apply SINC. unfold PM.vs_own. rewrite E0. left. reflexivity. }
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ov fb eni (AOF ov 56 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eov; lia| exact EINC| | exact EA].
    intros Hp. apply OB. apply EINC. unfold PEC.enc_own. replace (PEC.en_k eni =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [apply (PMKB.u64_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eop; lia| exact VREF]|].
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eosk; lia| exact KINC| | exact SKA].
    intros Hp. apply OB. apply KINC. unfold PESK.sink_own. replace (PESK.sk_c ki =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [change (PMSTA.base_okA RSEGS PMB.AD Mj); apply (PMBSK.base_keep L ar C LY LB FF sp0 scr0 W Mi Mj EK); [intros a Ha; apply OI; clear - Ha; lia| exact BASE]|].
  split.
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LB FF sp0 scr0 W Mi Mj EK ei PECSB.addrs_wf_B); [| exact ERR].
    intros a D. change (PMST.dep PMB.AD a) in D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMB.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OI. clear - DI; lia. }
  split; [exact TBOK|].
  split.
  { apply (content_keepA' LB FF sp0 scr0 W Mi Mj fb p si str smi op EK WAPP FRB BRB AOI); [fold ois; apply OWo; clear - Eois; lia| exact SINC| | intros q m Hq; exact (OB q m Hq)| exact IA| exact PA| exact CONT].
    apply PINC. unfold PM.parser_own, PM.src_own. left. reflexivity. }
  split; [exact CL|].
  split; [apply (PECFA.ec_state_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB fb (s_ec Xi) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [fold oec; apply OWo; clear - Eoec; lia| exact ECS]|].
  split; [exact ECI|].
  exact (PMKB.acc_keepA' L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACC).
Qed.

Lemma cpre_stepA LB sp0 scr0 W Mi Mj Xi si smi eni ki ei Xj sj ej :
  L5SAR.ek L ar LB FF sp0 scr0 W Mi Mj -> PMKB.wapp W ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  incl (PEC.owned si eni ki) LB -> incl (PM.vs_own str) LB ->
  (forall i, fb + 32 <= i < fb + 2040 -> ~ (op <= i < op + 384) -> ~ (oec <= i < oec + 16) -> L5.outside W i) ->
  (forall q m, In (q, m) LB -> PMKB.blk_out W q m) ->
  PM.p_src sj = PM.p_src si -> PM.p_tb sj = PM.p_tb si -> PM.p_tg sj = PM.p_tg si ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mj op ois sj -> PMSTA.base_okA RSEGS AD Mj -> PESTA.err_okA RSEGS AD AAD EE Mj ej ->
  PEC.clink p Xj sj smi eni ki -> PECA.ec_stateA RSEGS AD Mj fb (s_ec Xj) cat -> (s_ec Xj = true -> ej = true) ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat -> PECA.crun_preA RSEGS AD AAD EE L ar P Mj fb p Xj sj str smi eni ki ej cat.
Proof.
  intros EK WAPP BRB OINC SINC OW OB ESRC ETB ETG PA' BASE' ERR' CL' ECS' ECI' CP. entry_facts.
  destruct CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (PINC : incl (PM.parser_own si) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; left; exact Hx).
  assert (EINC : incl (PEC.enc_own eni) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (KINC : incl (PESK.sink_own ki) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; right; apply in_or_app; right; exact Hx).
  assert (OWo : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= op \/ op + 384 <= a) -> (a + n <= oec \/ oec + 16 <= a) -> forall i, a <= i < a + n -> L5.outside W i)
    by (intros a n X1 X2 X3 X4 i Hi; apply OW; clear - X1 X2 X3 X4 Hi; lia).
  split; [exact PA'|].
  split.
  { apply (PMKB.iss_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ois str smi AOI); [exact SINC| apply OWo; clear - Eois Eop Eoec; lia| | exact IA].
    intros c0 n0 p0 E0. apply OB. apply SINC. unfold PM.vs_own. rewrite E0. left. reflexivity. }
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ov fb eni (AOF ov 56 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eov Eop Eoec; lia| exact EINC| | exact EA].
    intros Hp. apply OB. apply EINC. unfold PEC.enc_own. replace (PEC.en_k eni =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [apply (PMKB.u64_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eop Eoec; lia| exact VREF]|].
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eosk Eop Eoec; lia| exact KINC| | exact SKA].
    intros Hp. apply OB. apply KINC. unfold PESK.sink_own. replace (PESK.sk_c ki =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [exact BASE'|].
  split; [exact ERR'|].
  split; [rewrite ETB, ETG; exact TBOK|].
  split.
  { rewrite ESRC. apply (content_keepA' LB FF sp0 scr0 W Mi Mj fb p si str smi op EK WAPP FRB BRB AOI); [fold ois; apply OWo; clear - Eois Eop Eoec; lia| exact SINC| | intros q m Hq; exact (OB q m Hq)| exact IA| exact PA| exact CONT].
    apply PINC. unfold PM.parser_own, PM.src_own. left. reflexivity. }
  split; [exact CL'|]. split; [exact ECS'|]. split; [exact ECI'|].
  exact (PMKB.acc_keepA' L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACC).
Qed.

Ltac open_amid MID :=
  pose proof MID as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J24 & J25 & J26 & J34) & BI & CP & ST & EIMP & CK);
  pose proof BI as (HHi & AMi & MRTi & INCAi & INCLi & ASTKi & EKbi & DKbi & OWNi & FSHDi);
  pose proof AMi as (Mhi & MIi).

Ltac vis_amid BI Hh Mv :=
  let X := fresh "VF" in
  pose proof (PMBUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
                WR _ _ _ _ _ _ BI) as X;
  destruct X as ((WSi & ICi & CSBi & CUARi & _) & OWNv & (FDi & FWi & FSWi & FLCi & FLWi) & (FLCci & FLVi & VFi & VSi & VSHi));
  change (ff_bytes 0) with 64 in WSi, FDi, FWi, FSWi, FLCi, VFi, VSHi; change (64 / 8) with 8 in FSWi, VSHi;
  replace (sp - (sp - 128)) with 128 in WSi by (clear; lia); replace (F + 64 - 8) with (F + 56) in FLCi by (clear; lia);
  fold Hh in WSi, ICi, CSBi, CUARi, OWNv, FDi, FWi, FSWi, FLCi, FLWi, FLVi, VFi, VSi, VSHi; fold Mv in WSi, ICi, CSBi, CUARi, OWNv, FDi, FWi, FSWi, FLCi, FLWi.

Lemma tail_Z pcz fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  zrun pcz -> amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_ec Y = true -> PECRVD.but_pos (r_key p X) (w_more false Y) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri pcz Mi mdi) K.
Proof.
  intros ZR MID EY RV. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).
  pose proof (PMBPAR.op_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb _ si HHi FOK' PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  fold Hi in Zop, Z32, Z20, OWR, OVIS. fold MVi in Zop, Z32, Z20, OWR.
  destruct (APART op 384 0 0) as (ApF & ApSF & ApFL).
  { intros i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048.
    split; [clear - Eop Hi'; lia| intros Y'; clear - Eop Hi' Y'; lia]. }
  { clear; lia. }
  change (ff_bytes 0) with 64 in ApF, ApSF. change (64 / 8) with 8 in ApSF. unfold SB in ApSF.
  assert (SHop : op / 8 + 2147450880 = fb / 8 + 2147450880 + 74).
  { rewrite Eop. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
    replace (2048 * (fb / 2048) + 592) with ((256 * (fb / 2048) + 74) * 8) by (clear; lia). rewrite Z.div_mul by lia.
    replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
  destruct (APART (op / 8 + 2147450880) 48 0 0) as (_ & AsopSF & _).
  { intros i Hi'. unfold aclient, aclient_g. do 5 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. unfold in_shadow_of, S. unfold SB.
    assert (D1 : (fb + 2048 - 1) / 8 = fb / 8 + 255).
    { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
      replace (2048 * (fb / 2048) + 2048 - 1) with (7 + (256 * (fb / 2048) + 255) * 8) by (clear; lia). rewrite Z.div_add by lia.
      replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
    rewrite D1. clear - SHop Hi'. lia. }
  { clear; lia. }
  change (64 / 8) with 8 in AsopSF. unfold SB in AsopSF.
  pose proof OWNv as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26.
  pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  destruct (ZR fxi Ri R MVi sp op ov oec F fl) as (fx7 & R7 & M7v & MG7 & FRZ7 & MS7 & K347 & REG7 & E72 & FL0 & MO0);
    first [assumption | clear - GSLO GSHI GSPT; lia | clear - O1 O3; lia | clear - O1 O3 Eop Eov; lia | clear - O1 O3 Eop Eoec; lia | clear - GFR; lia
          | clear - GL1 GL2; lia | clear - O2 GSLO; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | exact SP32 | exact O8 | exact GF32 | idtac].
  all: try (clear - ApF; lia). all: try (clear - ApFL; lia). all: try (clear - AsopSF; lia).
  assert (R7ra : getr R7 (reg 1) = Z_to_bv 64 r) by (rewrite (REG7 1%nat) by inl; exact Rra).
  pose proof (PMK.ret_to RSEGS fx7 R7 M7v 0xb8e54 W_b8e04 r F_b8e04 eq_refl D_b8e04 R7ra Hr1 Hr2) as MSr.
  apply (PMBUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
           WR (PEC.owned si eni ki) Mi mdi LKi cri Awi (fun a => op + 8 <= a < op + 9) fxi fx7 Ri pcz R7 r M7v K BI).
  { intros a X'. split.
    - apply (L5SAR.fframe_client L ar (PEC.owned si eni ki ++ LBX) FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - X' Eop; lia].
    - intros O. apply (O (PMSP.o_p AD fb + 8, 8)); [unfold WR; wr_mem 0| wr_rng; clear - X' Eop; lia]. }
  { intros a. destruct (L5SAR.rng_dec a (op + 8) (op + 9)) as [X'|X']; [left; exact X'| right; exact X']. }
  { exact (msteps_trans _ _ _ _ MS7 MSr). }
  { exact MG7. }
  { intros a Ha Nw. unfold PMBUK.WretX, PMBUK.Wret in Nw. change (ff_bytes 0) with 64 in Nw.
    apply FRZ7; [exact Ha| intros X'; apply Nw; right; clear - X'; lia| intros X'; apply Nw; left; left; left; clear - X'; lia
                | intros X'; apply Nw; left; left; right; unfold SB; clear - X'; lia| intros X'; apply Nw; left; right; clear - X'; lia]. }
  { exact FL0. }
  intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict Hi Mf = M7v) in VISf.
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  assert (EKf : L5SAR.ek L ar LBi FF 0 0 [(op + 8, 1)] Mi Mf).
  { apply (PMBUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k)
             LBi LKi cri Awi Mi Mf _ [(op + 8, 1)] (fun a => op + 8 <= a < op + 9) G HHi).
    - intros a X' O. apply (O (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X'; lia].
    - exact FZf. }
  pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  assert (MO0f : L5.u8_at RSEGS Mf (op + 8) 0).
  { apply (proj1 (L5A.u8_at_vis Hi Mf (op + 8) 0 (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). rewrite VISf. exact MO0. }
  assert (WAPP8 : PMKB.wapp [(op + 8, 1)]).
  { apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OBIG; lia. }
  assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i).
  { intros a n X3 i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi' Hr X3. lia. }
  assert (OUTB8 : forall q' m, In (q', m) LBi -> forall i, q' <= i < q' + m -> L5.outside [(op + 8, 1)] i).
  { intros q' m Hq i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
    destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi Hq (PMBUAR.aobjA_push FF op 384 _ AOP)) as [Z'|Z']; clear - Hi' Hr Z'; lia. }
  assert (Iq : In (PM.sr_qc (PM.p_src si), PM.CHUNK) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (Ib : In (PM.p_b si, 32 * 2 ^ PM.p_k si) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
  apply (KONT fx7 R7 Mf modelf LKi Awi (PMPK.set_more si 0) smi eni ki ei cri).
  - apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite E72; exact (eq_sym Rsp) | apply REG7; inl | rewrite (K347 _) by inl; apply J34; inl ] |]).
    destruct Hj.
  - destruct (BRBi _ Iq) as (Xq1 & Xq2). destruct (BRBi _ Ib) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2. unfold PM.CHUNK in Xq2.
    apply (cpre_stepA LBi 0 0 [(op + 8, 1)] Mi Mf Y si smi eni ki ei (r_key p X) (PMPK.set_more si 0) ei EKf WAPP8 BRBi).
    + unfold LBi. apply incl_appl. apply incl_refl.
    + unfold LBi. apply incl_appr. exact INCS.
    + intros i Hi' Ni _. apply (OUT8 i 1); clear - Hi' Ni; lia.
    + intros q' m Hq. exact (OUTB8 q' m Hq).
    + reflexivity. + reflexivity. + reflexivity.
    + apply (PMBPAR.parser_more_updA Mi Mf op ois si 0 PA).
      * clear - O1; lia.
      * clear - O1 O3; lia.
      * apply (PMKB.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
      * apply (PMKB.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB (op + 9) 375 (AOF (op + 9) 375 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
      * exact (PMKB.agsh_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB op 384 AOP).
      * pose proof PA as (_ & PDi & _). apply (L5.defined_grows Mi Mf _ _ MGf PDi).
      * exact MO0f.
      * left; reflexivity.
      * exact Xq1.
      * unfold PM.CHUNK. clear - Xq2; lia.
      * apply (PMKB.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Iq). apply OUTB8. exact Iq.
      * exact Xb1.
      * clear - Xb2; lia.
      * apply (PMKB.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Ib). apply OUTB8. exact Ib.
      * intros c0 n0 p0 E0. assert (Ip : In (p0, c0) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
        apply (PMKB.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Ip). apply OUTB8. exact Ip.
    + change (PMSTA.base_okA RSEGS PMB.AD Mf). apply (PMBSK.base_keep L ar C LY LBi FF 0 0 [(op + 8, 1)] Mi Mf EKf); [| exact BASE]. intros a Ha. apply (OUT8 a 1); clear - Ha O1; lia.
    + apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBi FF 0 0 [(op + 8, 1)] Mi Mf EKf ei PECSB.addrs_wf_B); [| exact ERR].
      intros a D. change (PMST.dep PMB.AD a) in D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
      split; [clear - DI; lia|]. split; [exact (PMB.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply (OUT8 a 1); clear - DI O1; lia.
    + apply (PECRVD.clink_but_pos p (r_key p X) (w_more false Y)); [reflexivity| exact RV|].
      destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
      unfold PEC.clink, PMPK.set_more. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_more PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src PEC.b2z].
      split; [reflexivity|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|].
      split; [intros X' _; discriminate X'|]. split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad].
    + assert (ECF : s_ec (r_key p X) = true) by (destruct RV as (_ & _ & _ & _ & _ & E6 & _); rewrite E6; cbn; exact EY). rewrite ECF.
      pose proof ECS as ECS0. unfold PECA.ec_stateA in ECS0 |- *. rewrite EY in ECS0. fold oec in ECS0 |- *. destruct ECS0 as (v & Hv & ECv).
      exists v. split; [exact Hv|].
      pose proof ECv as (ECa & ECb & ECc & ECd). split; [|split; [|split]].
      * apply (PMF.u32_at_agree RSEGS Mi Mf); [| clear - O1 Eop Eoec; lia| clear - O3 Eop Eoec; lia| exact ECa].
        apply (proj1 (PMKB.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB oec 4 (AOF oec 4 ltac:(lia) ltac:(lia)) ltac:(apply OUT8; clear - Eop Eoec; lia))).
      * apply (L5C.u64_at_agree RSEGS Mi Mf); [| clear - O1 Eop Eoec; lia| clear - O3 Eop Eoec; lia| exact ECb].
        apply (proj1 (PMKB.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB (oec + 8) 8 (AOF (oec + 8) 8 ltac:(lia) ltac:(lia)) ltac:(apply OUT8; clear - Eop Eoec; lia))).
      * apply (L5.defined_grows Mi Mf _ _ MGf ECc).
      * exact (PMKB.acc_keepA' L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB oec 16 (AOF oec 16 ltac:(lia) ltac:(lia)) ECd).
    + intros _. apply ECI. exact EY.
    + exact CP.
  - unfold PMPK.set_more. cbn [PM.p_src]. exact ST.
  - exact EIMP.
  - exact AHf.
  - unfold PMSP.credit_keep, PMPK.set_more, PECA.pot_allA, PEC.credit_add, PM.pot_parser in CK |- *. cbn [PM.p_k PM.p_tb PM.p_tg fst snd] in CK |- *. exact CK.
  - exact MRTf.
  - exact INCLi.
  - exact INCAi.
  - exact AMf.
  - unfold PMPK.set_more. change (PEC.owned (PM.PST 0 (PM.p_done si) (PM.p_depth si) (PM.p_src si) (PM.p_tb si) (PM.p_tg si) (PM.p_b si) (PM.p_k si) (PM.p_stk si)) eni ki)
      with (PEC.owned si eni ki). exact HHf.
Qed.

Lemma call_mkec (q v : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 oec -> getr Ri (reg 11) = Z_to_bv 64 v -> 1 <= v <= 64 ->
  (forall fx' R' M' md' LK' Aw', regs_preserved Ri R' -> amid fx' R' M' md' LK' Aw' cri si smi eni ki true (w_ec true Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri 0xafda8 Mi mdi) K.
Proof.
  intros MID J1 RAq J10 J11 Hv KONT'. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  assert (ECD : L5.defined Mi oec 16 /\ PMSPA.accA Mi oec 16).
  { pose proof ECS as ECS0. unfold PECA.ec_stateA in ECS0. fold oec in ECS0.
    destruct (s_ec Y); [destruct ECS0 as (v0 & _ & (_ & _ & D' & A')); exact (conj D' A')| destruct ECS0 as (_ & _ & D' & A'); exact (conj D' A')]. }
  assert (SZK : forall Mc lo g, L5SAR.ek L ar LBX FF sp 26624 WR M Mc -> sp - 26624 <= lo -> lo + 8 * g <= sp -> lo mod 8 = 0 -> 0 <= g -> shadow_zero Mc lo g).
  { intros Mc lo g EKc H1' H2' H3' H4'.
    assert (WAPPR : PMKB.wapp WR).
    { intros rr Hin. destruct rr as [ra' rn]. unfold BIGSHADOW_LO, BIGSHADOW_HI. cbn [fst snd].
      pose proof FSAPP as (FA0 & FA1 & FA2).
      unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
      cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutB.CADDR_B PeCLayoutB.EADDR_B] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros <- <-; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia|]). destruct Hin. }
    apply (PMKB.stksh_keepA L ar LBX FF sp 26624 WR M Mc EKc WAPPR lo g); [clear - H1' SLO SPT; lia| clear - H1' SLO; lia| clear - H2' SHI SPT; lia| exact H3'| exact H4'|].
    apply (PMKB.shadow_zero_sub M (sp - 26624) 3328); [| exact H3'| exact H1'| clear - H2'; lia| exact H4'| exact STKSH].
    apply PMKB.mod16_8'. replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  unfold PECSB.make_ec_spec, PECSPA.make_ec_spec in MKE.
  apply (MKE fxi Ri Mi mdi K LBi FF' LKi Awi cri oec v (sp - 128) q ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 26624 128 14336 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply SZK; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKB.mod16_8'. replace (sp - 128 - 14336) with (sp + (-904) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
    apply (PMBUAR.ffroomA_push 7 1 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMBUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact J10. }
  { rewrite L5K.rl11. exact J11. }
  { exact Hv. }
  { apply PMBUAR.aobjA_push. apply AOF; clear - Eoec; lia. }
  { exact C8m. }
  { exact (proj1 ECD). }
  { exact (proj2 ECD). }
  { exact BASE. }
  { exact ERR. }
  intros fx6 R6 M6 model6 LK6 Aw6 RP6 EC6 ERR6 HP6 MRT6 INCLK6 INCAw6 AM6 HH6.
  change (PMSPA.pm_scr 1) with 14336 in HP6.
  set (Wc6 := (oec, 16) :: (if ei then [] else PMSPA.err_W AD)) in HP6.
  assert (Wc6R : forall rr a, In rr Wc6 -> L5.in_rng rr a -> (oec <= a < oec + 16) \/ (0x678780 <= a < 0x69a4f4)).
  { intros rr a Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [left; exact Hr|]. right. destruct ei; [destruct Hin|].
    unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutB.CADDR_B] in Hin. unfold L5.in_rng in Hr.
    destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia. }
  assert (BI6 : PMBUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned si eni ki) M6 model6 LK6 cri Aw6).
  { apply (PMBUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) (PEC.owned si eni ki) (PEC.owned si eni ki) Mi mdi LKi cri Awi M6 model6 LK6 cri Aw6 14336 Wc6 BI HP6 HH6 AM6 MRT6 INCAw6 INCLK6);
      [clear; lia| clear; lia| | | intros a X'; exact X'].
    - intros rr a Hin Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
      pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
      assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
      pose proof FSAPP as (FA0 & FA1 & FA2).
      destruct (Wc6R rr a Hin Hr) as [X'|X']; (split; [clear - X' SLO SPT Eop Eoec F2 FSCEIL; lia|]).
      + destruct FA1 as [Y'|Y']; clear - X' Y' DF1 DF2 F1 F2 Eoec; lia.
      + clear - X' DF1; lia.
    - intros a Hc Ho rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [X'|X'].
      + apply (Ho (PMSP.o_ec AD fb, 16)); [unfold WR; wr_mem 6| wr_rng; clear - X' Eoec; lia].
      + unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr X' Eoec O1 Eop; lia|].
        destruct ei; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutB.CADDR_B] in Hin.
        destruct Hin as [<-|[<-|[]]].
        * apply (Ho (pa_errcat_guard AD, 2)); [unfold WR; wr_mem 7| exact Hr].
        * apply (Ho (pa_atexit AD, 544)); [unfold WR; wr_mem 8| exact Hr]. }
  pose proof (L5SAR.ek_callee L ar LBi [] FF [(F, 0, sp - 128 + 32)] sp 26624 (sp - 128) 14336 Wc6 Wc6 Mi M6 ltac:(rewrite app_nil_l; exact HP6) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK6.
  assert (WAPP6 : PMKB.wapp Wc6).
  { intros rr Hin. unfold Wc6 in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|Hin]; cbn [fst snd].
    - pose proof FSAPP as (FA0 & FA1 & FA2). destruct FA1 as [Y'|Y']; clear - Y' F1 F2 Eoec; lia.
    - destruct ei; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutB.CADDR_B] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
  assert (OUTB6 : forall q' m, In (q', m) LBi -> forall i, q' <= i < q' + m -> L5.outside Wc6 i).
  { intros q' m Hq i Hi' rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y'].
    - destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m oec 16 HHi Hq (PMBUAR.aobjA_push FF oec 16 _ (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia)))) as [Z'|Z']; clear - Hi' Y' Z'; lia.
    - pose proof (PMBSK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q' m HHi Hq) as Z'. destruct Z' as [Z'|Z']; clear - Hi' Y' Z'; lia. }
  apply (KONT' fx6 R6 M6 model6 LK6 Aw6 RP6).
  split; [|split; [exact BI6| split; [| split; [exact ST| split; [intros _; reflexivity| exact CK]]]]].
  - pose proof (fun j Hj => L5SAR.cs_of_preserved Ri R6 j RP6 Hj) as R6c.
    split; [rewrite (R6c 2%nat) by inl; exact J2|]. split; [rewrite (R6c 8%nat) by inl; exact J8|]. split; [rewrite (R6c 9%nat) by inl; exact J9|].
    split; [rewrite (R6c 18%nat) by inl; exact J18|]. split; [rewrite (R6c 19%nat) by inl; exact J19|]. split; [rewrite (R6c 20%nat) by inl; exact J20|].
    split; [rewrite (R6c 21%nat) by inl; exact J21|]. split; [rewrite (R6c 24%nat) by inl; exact J24|]. split; [rewrite (R6c 25%nat) by inl; exact J25|].
    split; [rewrite (R6c 26%nat) by inl; exact J26|].
    intros j Hj. rewrite (R6c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - apply (cpre_stepA LBi sp 26624 Wc6 Mi M6 Y si smi eni ki ei (w_ec true Y) si true EK6 WAPP6 BRBi).
    + unfold LBi. apply incl_appl. apply incl_refl.
    + unfold LBi. apply incl_appr. exact INCS.
    + intros i Hi' N1 N2 rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y']; [clear - N2 Y'; lia| clear - Hi' Y' Eop O1; lia].
    + intros q' m Hq. exact (OUTB6 q' m Hq).
    + reflexivity. + reflexivity. + reflexivity.
    + apply (PMKB.parser_keepA RSEGS AD L ar LBi FF sp 26624 Wc6 Mi M6 EK6 WAPP6 FRB BRBi _ _ _ AOP); [| | | | | exact PA].
      * unfold LBi, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. left. exact Hx.
      * intros i Hi' rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y']; [clear - Hi' Y' Eop Eoec; lia| clear - Hi' Y' Eop O1; lia].
      * unfold PMKB.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.src_own; left; reflexivity.
      * unfold PMKB.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
      * intros c0 n0 p0 E0. unfold PMKB.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.vs_own. rewrite E0. right; right; left; reflexivity.
    + apply (PMBPAR.base_keepW L ar C LY LBi FF sp 26624 Wc6 Mi M6 EK6); [| | | | exact BASE].
      * intros a Ha rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [Y'|Y']; [clear - Ha Y' Eoec Eop O1; lia| clear - Ha Y'; lia].
      * intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct ei; [destruct Hin|].
        unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutB.CADDR_B] in Hin. unfold L5.in_rng in Hr.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
      * intros rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eoec Eop O1; lia|]. destruct ei; [destruct Hin|].
        unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutB.CADDR_B] in Hin. unfold L5.in_rng in Hr.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia.
      * intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct ei; [destruct Hin|].
        unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutB.CADDR_B] in Hin. unfold L5.in_rng in Hr.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
    + exact ERR6.
    + destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
      unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad s_ec w_ec].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|]. split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad].
    + unfold PECA.ec_stateA. cbn [s_ec w_ec]. fold oec. exists v. split; [exact Hv| exact EC6].
    + intros _; reflexivity.
    + exact CP.
Qed.

Lemma wr_wav : forall rr a, In rr WR -> L5.in_rng rr a -> ~ ocell sp a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 0 / 8).
Proof.
  entry_facts. frame_facts.
  assert (WRR' : forall rr a, In rr WR -> L5.in_rng rr a -> (fb + 32 <= a < fb + 2040) \/ (0x678780 <= a < 0x69a4f4)).
  { intros rr a Hin Hr. unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutB.CADDR_B PeCLayoutB.EADDR_B] in Hin. unfold L5.in_rng in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin. }
  intros rr a Hin Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
  pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  pose proof FSAPP as (FA0 & FA1 & FA2).
  destruct (WRR' rr a Hin Hr) as [X'|X']; (split; [clear - X' SLO SPT F2 FSCEIL; lia|]).
  - destruct FA1 as [Y'|Y']; clear - X' Y' DF1 DF2 F1 F2; lia.
  - clear - X' DF1; lia.
Qed.

Lemma wappR : PMKB.wapp WR.
Proof.
  entry_facts. intros rr Hin. destruct rr as [ra' rn]. unfold BIGSHADOW_LO, BIGSHADOW_HI. cbn [fst snd].
  pose proof FSAPP as (FA0 & FA1 & FA2).
  unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
  cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutB.CADDR_B PeCLayoutB.EADDR_B] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros <- <-; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia|]). destruct Hin.
Qed.

Lemma szk Mc lo g : L5SAR.ek L ar LBX FF sp 26624 WR M Mc -> sp - 26624 <= lo -> lo + 8 * g <= sp -> lo mod 8 = 0 -> 0 <= g -> shadow_zero Mc lo g.
Proof.
  entry_facts. intros EKc H1' H2' H3' H4'.
  apply (PMKB.stksh_keepA L ar LBX FF sp 26624 WR M Mc EKc wappR lo g); [clear - H1' SLO SPT; lia| clear - H1' SLO; lia| clear - H2' SHI SPT; lia| exact H3'| exact H4'|].
  apply (PMKB.shadow_zero_sub M (sp - 26624) 3328); [| exact H3'| exact H1'| clear - H2'; lia| exact H4'| exact STKSH].
  apply PMKB.mod16_8'. replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
Qed.

Lemma call_gl (q : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 op -> getr Ri (reg 11) = Z_to_bv 64 oec ->
  PECSPA.mp_gl tt p Y ->
  (forall fx' R' M' md' LK' Aw' cr' si' smi' ei', regs_preserved Ri R' -> PECSPA.gl_ret p Y R' ->
      amid fx' R' M' md' LK' Aw' cr' si' smi' eni ki ei' (PECSPA.gl_post p Y) ->
      PM.p_tb si' = PM.p_tb si -> PM.p_tg si' = PM.p_tg si -> PM.p_b si' = PM.p_b si -> PM.p_k si' = PM.p_k si ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri (pa_get_length AD) Mi mdi) K.
Proof.
  intros MID J1 RAq J10 J11 MPG KONT'. entry_facts. frame_facts. open_amid MID.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).
  unfold PECSB.get_length_spec, PECSPA.get_length_spec in GL.
  apply (GL PMODE fxi Ri Mi mdi K LBX FF' LKi Awi cri (sp - 128) q fb cat p Y si str smi eni ki ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 5) with 22528. change (22528 / 8) with 2816.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 26624 128 22528 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKB.mod16_8'. replace (sp - 128 - 22528) with (sp + (-1416) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
    apply (PMBUAR.ffroomA_push 7 5 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMBUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { replace (sp - 128) with (sp + (-4) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
  { split; [rewrite L5K.rl10; exact J10| rewrite L5K.rl11; exact J11]. }
  { exact CP. }
  { exact INCS. }
  { exact POK. }
  { exact MPG. }
  { exact (credit_le_keep _ _ _ _ CRED CK). }
  intros fx4 R4 M4 model4 LK4 Aw4 s4 sm4 e4 cr4 RP4 CPRE4 RET4 STEP4 EE4 ETB ETG EB EKK HP4 CK4 MRT4 INCLK4 INCAw4 AM4 HH4.
  change (PMSPA.pm_scr 5) with 22528 in HP4.
  assert (BI4 : PMBUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned s4 eni ki) M4 model4 LK4 cr4 Aw4).
  { apply (PMBUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) [] (PEC.owned s4 eni ki) Mi mdi LKi cri Awi M4 model4 LK4 cr4 Aw4 22528 WR BI HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
      [clear; lia| clear; lia| exact wr_wav| intros a _ X'; exact X'| intros a X'; exact X']. }
  apply (KONT' fx4 R4 M4 model4 LK4 Aw4 cr4 s4 sm4 e4 RP4 RET4); [| exact ETB| exact ETG| exact EB| exact EKK].
  split; [|split; [exact BI4| split; [exact CPRE4| split; [exact (PMBPAR.src_step_transA _ _ _ _ _ _ ST STEP4)| split; [intros X'; exact (EE4 (EIMP X'))| exact (credit_keep_trans _ _ _ _ _ _ CK CK4)]]]]].
  pose proof (fun j Hj => L5SAR.cs_of_preserved Ri R4 j RP4 Hj) as R4c.
  split; [rewrite (R4c 2%nat) by inl; exact J2|]. split; [rewrite (R4c 8%nat) by inl; exact J8|]. split; [rewrite (R4c 9%nat) by inl; exact J9|].
  split; [rewrite (R4c 18%nat) by inl; exact J18|]. split; [rewrite (R4c 19%nat) by inl; exact J19|]. split; [rewrite (R4c 20%nat) by inl; exact J20|].
  split; [rewrite (R4c 21%nat) by inl; exact J21|]. split; [rewrite (R4c 24%nat) by inl; exact J24|]. split; [rewrite (R4c 25%nat) by inl; exact J25|].
  split; [rewrite (R4c 26%nat) by inl; exact J26|].
  intros j Hj. rewrite (R4c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply J34. exact Hj.
Qed.

Lemma cred_text Mi Xi si smi eni ki ei cri :
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat -> PMSP.credit_le (PECA.pot_allA L ar P si eni ki) cri ->
  PMSP.credit_le (PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) (PM.p_tb si) (PM.p_tg si))) cri.
Proof.
  intros CP CLE. pose proof CP as (PA & _ & EA & _ & SKA & _).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _). pose proof PVEC as (_ & _ & _ & Hk & _).
  pose proof EA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EHk & _).
  pose proof (PESKA.sink_potA_nonneg RSEGS L ar P Mi osk ki PO SKA) as (SP1 & SP2).
  pose proof (PMB.ly_cost L C LY) as (KPM & BLIN & BOV).
  apply (PMBPAR.pot_text_le_parserA L ar C LY si cri); [clear - Hk; lia|].
  pose proof (Z.pow_le_mono_r 2 (PEC.en_k eni) 12 ltac:(lia) ltac:(clear - EHk; lia)) as P2e. pose proof (PM.pow2_pos (PEC.en_k eni) ltac:(clear - EHk; lia)) as P2p.
  unfold PMSPA.credit_le, PMSP.credit_le, PECA.pot_allA, PEC.credit_add, PEC.pot_estack, PMSPA.scA in CLE |- *. cbn [fst snd] in CLE |- *.
  unfold PMSPA.HV, LibIfaceAB.heap_view in CLE |- *. cbn [HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in CLE |- *. rewrite KPM, BOV, BLIN in CLE |- *.
  assert (E2 : 0 <= PEC.ESZ * (2 ^ 12 - 2 ^ PEC.en_k eni)) by (unfold PEC.ESZ; apply Z.mul_nonneg_nonneg; clear - P2e; lia).
  clear - CLE SP1 SP2 EHk E2. split; nia.
Qed.

Lemma cred_enc Mi Xi si smi eni ki ei cri :
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat -> PMSP.credit_le (PECA.pot_allA L ar P si eni ki) cri ->
  PMSP.credit_le (PECA.pot_encA L ar P eni ki) cri.
Proof.
  intros CP CLE. pose proof CP as (PA & _ & _ & _ & _ & _ & _ & TBOK & _).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PTB & PVEC & _). pose proof PVEC as (_ & _ & _ & Hk & _).
  pose proof (PMB.ly_cost L C LY) as (KPM & BLIN & BOV).
  assert (PPN : 0 <= fst (PM.pot_parser (PMSPA.HV L ar) si) /\ 0 <= snd (PM.pot_parser (PMSPA.HV L ar) si)).
  { pose proof PTB as (_ & _ & TBF). destruct TBOK as (TG1 & TG2 & _).
    unfold PM.pot_parser, PM.credit_add, PM.pot_stack, PM.pot_text. cbn [fst snd].
    unfold PMSPA.HV, LibIfaceAB.heap_view. cbn [HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead]. rewrite KPM, BOV.
    assert (CAPB : 0 <= PM.vs_cap (PM.p_tb si) <= 2 ^ 27) by (destruct (PM.p_tb si) as [n1|c1 n1 q1]; cbn [PM.vs_cap] in *; [lia| destruct TBF as (_ & _ & _ & _ & Hc1 & _); lia]).
    pose proof (PM.pow2_pos (PM.p_k si + 1) ltac:(lia)) as P2a. assert (P2b : 2 ^ (PM.p_k si + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
    clear - CAPB P2a P2b Hk TG1. split; nia. }
  unfold PMSP.credit_le, PECA.pot_allA, PECA.pot_encA, PEC.credit_add, PMSPA.scA in CLE |- *. cbn [fst snd] in CLE |- *. clear - CLE PPN BLIN. nia.
Qed.

Lemma call_span (len q : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_more Y = true -> s_done Y = false -> 0 <= s_pos Y <= blen p ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 (op + 24) -> getr Ri (reg 11) = Z_to_bv 64 len -> getr Ri (reg 12) = Z_to_bv 64 otb -> 0 <= len < 2 ^ 64 ->
  (forall fx' R' M' md' LK' Aw' cr' si' smi' ptr n, regs_preserved Ri R' ->
      getr R' (reg 10) = Z_to_bv 64 ptr -> getr R' (reg 11) = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
      ((ptr = 0 /\ n = 0) \/ (exists B m, In (B, m) (PM.parser_own si') /\ B <= ptr /\ ptr + n <= B + m) \/ (otb + 1 <= ptr /\ ptr + n <= otb + 24)) ->
      L5.defined M' ptr n -> PMSPA.accA M' ptr n -> L5.bytes_at RSEGS M' ptr (UbjRef.slice p (s_pos Y) n) -> n = Z.min len (blen p - s_pos Y) ->
      amid fx' R' M' md' LK' Aw' cr' si' smi' eni ki ei (w_pos (s_pos Y + n) Y) ->
      PM.p_b si' = PM.p_b si -> PM.p_k si' = PM.p_k si ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri (pa_read_span AD) Mi mdi) K.
Proof.
  intros MID MORE DONE PPOS J1 RAq J10 J11 J12 Hlen KONT'. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  set (LBX0 := PEC.enc_own eni ++ PESK.sink_own ki ++ LBX).
  pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad). pose proof (Lpos MORE DONE) as POS.
  unfold PECSB.read_span_spec, PECSPA.read_span_spec in RS.
  apply (RS fxi Ri Mi mdi K LBX0 FF' LKi Awi cri (sp - 128) q fb len p si str smi ltac:(unfold LBX0; rewrite PEC.owned_app; exact HHi) AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 6) with 24576. change (24576 / 8) with 3072.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 26624 128 24576 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKB.mod16_8'. replace (sp - 128 - 24576) with (sp + (-1544) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
    apply (PMBUAR.ffroomA_push 7 6 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMBUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { replace (sp - 128) with (sp + (-4) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
  { rewrite L5K.rl10. exact J10. }
  { rewrite L5K.rl11. exact J11. }
  { rewrite L5K.rl12. exact J12. }
  { exact Hlen. }
  { exact PA. } { exact IA. } { exact BASE. } { exact ACC. } { exact TBOK. }
  { unfold LBX0. intros x Hx. apply in_or_app. right. apply in_or_app. right. exact (INCS x Hx). }
  { exact POK. } { exact CONT. }
  { exact (cred_text Mi Y si smi eni ki ei cri CP (credit_le_keep _ _ _ _ CRED CK)). }
  intros fxn Rn Mn mdn LKn Awn s2 sm2 cr2 ptr n RP2 Y10 Y11 Hn Hn26 LOC DEF2 ACC2 BYT2 NMIN PA2 IA2 TBOK2 CONT2 Emore Edone Edepth Eb Ek Estk STEP2 CONS HP2 CK2 MRT2 INCLK2 INCAw2 AM2 HH2.
  change (PMSPA.pm_scr 6) with 24576 in HP2. rewrite L5K.rl10 in Y10. rewrite L5K.rl11 in Y11.
  assert (OWN2 : PM.parser_own s2 ++ LBX0 = PEC.owned s2 eni ki ++ LBX) by (unfold LBX0; rewrite PEC.owned_app; reflexivity).
  rewrite OWN2 in HH2. fold otb in HP2. set (Wc := PMSPA.W_srcf AD fb ++ [(otb, 24)]) in HP2.
  pose proof HP2 as HP2a. unfold LBX0 in HP2a. rewrite app_assoc in HP2a.
  assert (X0INC : incl LBX0 LBi) by (unfold LBX0, LBi, PEC.owned; intros x Hx; rewrite <- !app_assoc; apply in_or_app; right; exact Hx).
  assert (BRB0 : forall b, In b LBX0 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; exact (BRBi b (X0INC b Hb))).
  assert (WcIN : forall rr, In rr Wc -> In rr WR).
  { intros rr Hin. unfold Wc, PMSPA.W_srcf in Hin. cbn [app] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; unfold WR; [wr_mem 1| wr_mem 2| wr_mem 3| wr_mem 4]. }
  assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a -> (op + 280 <= a < op + 320) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (otb <= a < otb + 24)).
  { intros rr a Hin Hr. unfold Wc, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is AD PeCLayoutB.CADDR_B] in Hin.
    unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; [clear - Hr Eop| clear - Hr Eois| clear - Hr Eois| clear - Hr Eotb Eop]; lia. }
  assert (BI2 : PMBUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned s2 eni ki) Mn mdn LKn cr2 Awn).
  { apply (PMBUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) (PEC.enc_own eni ++ PESK.sink_own ki) (PEC.owned s2 eni ki) Mi mdi LKi cri Awi Mn mdn LKn cr2 Awn 24576 Wc BI HP2a HH2 AM2 MRT2 INCAw2 INCLK2);
      [clear; lia| clear; lia| intros rr a Hin Hr; exact (wr_wav rr a (WcIN rr Hin) Hr)| intros a _ O rr Hin Hr; exact (O rr (WcIN rr Hin) Hr)| intros a X'; exact X']. }
  pose proof (L5SAR.ek_callee L ar LBX0 [] FF [(F, 0, sp - 128 + 32)] sp 26624 (sp - 128) 24576 Wc Wc Mi Mn ltac:(rewrite app_nil_l; exact HP2) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK2.
  assert (WAPPc : PMKB.wapp Wc) by (intros rr Hin; exact (wappR rr (WcIN rr Hin))).
  assert (OUTc : forall a m, fb + 32 <= a -> a + m <= fb + 2040 -> (a + m <= op + 280 \/ op + 320 <= a) -> (a + m <= ois + 40 \/ ois + 48 <= a) -> (a + m <= ois + 152 \/ ois + 156 <= a) ->
                 (a + m <= otb \/ otb + 24 <= a) -> forall i, a <= i < a + m -> L5.outside Wc i).
  { intros a m X1 X2 X3 X4 X5 X6 i Hi' rr Hin Hr. destruct (WcR rr i Hin Hr) as [Y'|[Y'|[Y'|Y']]]; [clear - Hi' Y' X3| clear - Hi' Y' X4| clear - Hi' Y' X5| clear - Hi' Y' X6]; lia. }
  assert (OUTBc : forall q' m, In (q', m) LBX0 -> forall i, q' <= i < q' + m -> L5.outside Wc i).
  { intros q' m Hq0 i Hi' rr Hin Hr. pose proof (X0INC _ Hq0) as Hq. destruct (WcR rr i Hin Hr) as [Y'|[Y'|[Y'|Y']]].
    - destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi Hq (PMBUAR.aobjA_push FF op 384 _ AOP)) as [Z'|Z']; clear - Hi' Y' Z'; lia.
    - destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m ois 272 HHi Hq (PMBUAR.aobjA_push FF ois 272 _ AOI)) as [Z'|Z']; clear - Hi' Y' Z'; lia.
    - destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m ois 272 HHi Hq (PMBUAR.aobjA_push FF ois 272 _ AOI)) as [Z'|Z']; clear - Hi' Y' Z'; lia.
    - destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi Hq (PMBUAR.aobjA_push FF op 384 _ AOP)) as [Z'|Z']; clear - Hi' Y' Z' Eotb; lia. }
  assert (EINC : incl (PEC.enc_own eni) LBX0) by (unfold LBX0; intros x Hx; apply in_or_app; left; exact Hx).
  assert (KINC : incl (PESK.sink_own ki) LBX0) by (unfold LBX0; intros x Hx; apply in_or_app; right; apply in_or_app; left; exact Hx).
  unfold PEC.pos_of in POS, BYT2, NMIN. unfold PMSPA.consumed in CONS.
  assert (CK2' : PMSP.credit_keep cri cr2 (PECA.pot_allA L ar P si eni ki) (PECA.pot_allA L ar P s2 eni ki)).
  { pose proof (PMB.ly_cost L C LY) as (KPM & BLIN & BOV).
    unfold PMSP.credit_keep, PECA.pot_allA, PEC.credit_add, PM.pot_parser, PM.credit_add, PMSPA.scA in CK2 |- *. cbn [fst snd] in CK2 |- *. rewrite BLIN in CK2 |- *. rewrite Ek. clear - CK2. lia. }
  apply (KONT' fxn Rn Mn mdn LKn Awn cr2 s2 sm2 ptr n RP2 Y10 Y11 Hn Hn26 LOC DEF2 ACC2); [rewrite <- POS; exact BYT2| rewrite <- POS; exact NMIN| | exact Eb| exact Ek].
  split; [|split; [exact BI2| split; [| split; [exact (PMBPAR.src_step_transA _ _ _ _ _ _ ST STEP2)| split; [exact EIMP| exact (credit_keep_trans _ _ _ _ _ _ CK CK2')]]]]].
  - pose proof (fun j Hj => L5SAR.cs_of_preserved Ri Rn j RP2 Hj) as Rnc.
    split; [rewrite (Rnc 2%nat) by inl; exact J2|]. split; [rewrite (Rnc 8%nat) by inl; exact J8|]. split; [rewrite (Rnc 9%nat) by inl; exact J9|].
    split; [rewrite (Rnc 18%nat) by inl; exact J18|]. split; [rewrite (Rnc 19%nat) by inl; exact J19|]. split; [rewrite (Rnc 20%nat) by inl; exact J20|].
    split; [rewrite (Rnc 21%nat) by inl; exact J21|]. split; [rewrite (Rnc 24%nat) by inl; exact J24|]. split; [rewrite (Rnc 25%nat) by inl; exact J25|].
    split; [rewrite (Rnc 26%nat) by inl; exact J26|].
    intros j Hj. rewrite (Rnc j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - split; [exact PA2|]. split; [exact IA2|].
    split; [apply (PECFA.enc_keepA RSEGS EE L ar LBX0 FF sp 26624 Wc Mi Mn EK2 WAPPc FRB BRB0 ov fb eni (AOF ov 56 ltac:(lia) ltac:(lia))); [apply OUTc; clear - Eov Eop Eois Eotb; lia| exact EINC| | exact EA]|].
    { intros Hp. refine (OUTBc _ _ _). apply EINC. unfold PEC.enc_own. replace (PEC.en_k eni =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
    split; [apply (PMKB.u64_keepA RSEGS L ar LBX0 FF sp 26624 Wc Mi Mn EK2 WAPPc FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [apply OUTc; clear - Eop Eois Eotb; lia| exact VREF]|].
    split; [apply (PECFA.sink_keepA RSEGS L ar LBX0 FF sp 26624 Wc Mi Mn EK2 WAPPc FRB BRB0 P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [apply OUTc; clear - Eosk Eop Eois Eotb; lia| exact KINC| | exact SKA]|].
    { intros Hp. refine (OUTBc _ _ _). apply KINC. unfold PESK.sink_own. replace (PESK.sk_c ki =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
    split; [change (PMSTA.base_okA RSEGS PMB.AD Mn); apply (PMBSK.base_keep L ar C LY LBX0 FF sp 26624 Wc Mi Mn EK2); [| exact BASE]|].
    { intros a Ha rr Hin Hr. destruct (WcR rr a Hin Hr) as [Y'|[Y'|[Y'|Y']]]; [clear - Ha Y' O1| clear - Ha Y' I1| clear - Ha Y' I1| clear - Ha Y' O1 Eotb]; lia. }
    split.
    { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBX0 FF sp 26624 Wc Mi Mn EK2 ei PECSB.addrs_wf_B); [| exact ERR].
      intros a D. change (PMST.dep PMB.AD a) in D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
      split; [clear - DI; lia|]. split; [exact (PMB.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|].
      intros rr Hin Hr. destruct (WcR rr a Hin Hr) as [Y'|[Y'|[Y'|Y']]]; [clear - DI Y' O1| clear - DI Y' I1| clear - DI Y' I1| clear - DI Y' O1 Eotb]; lia. }
    split; [exact TBOK2|]. split; [exact CONT2|].
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_pos].
      rewrite Emore, Edone, Edepth, Estk. split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|].
      split; [intros _ _; unfold PEC.pos_of; clear - CONS POS; lia|].
      split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad]. }
    split; [| split; [exact ECI|]].
    { cbn [s_ec w_pos]. apply (PECFA.ec_state_keepA RSEGS AD L ar LBX0 FF sp 26624 Wc Mi Mn EK2 WAPPc FRB fb (s_ec Y) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
      fold oec. apply OUTc; clear - Eoec Eop Eois Eotb; lia. }
    pose proof BI2 as (_ & _ & _ & _ & _ & _ & EKb2 & _).
    exact (PMKB.acc_keepA' L ar LBX FF sp 26624 WR M Mn EKb2 wappR FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) (PECA.crun_preA_rdr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPRE)).
Qed.

Lemma call_valid (pp n q : Z) (l : list Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 pp -> getr Ri (reg 11) = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 ->
  0 <= pp -> (n = 0 \/ 0 < pp) -> pp + n <= 2 ^ 47 -> L5.defined Mi pp n -> PMSPA.accA Mi pp n ->
  (n = 0 \/ (exists B m, In (B, m) (PEC.owned si eni ki ++ LBX) /\ B <= pp /\ pp + n <= B + m) \/ (otb + 1 <= pp /\ pp + n <= otb + 24)) ->
  L5.bytes_at RSEGS Mi pp l -> Z.of_nat (length l) = n -> Forall (fun b => 0 <= b < 256) l ->
  (forall fx' R' M' md' v, regs_preserved Ri R' -> getr R' (reg 11) = Z_to_bv 64 v -> 0 <= v < 7 -> (v = 0 <-> UbjRef.utf8_valid l = true) ->
      mem_grows Mi M' -> (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 - 12288 <= i < sp - 128) -> M' (Z_to_bv 64 i) = Mi (Z_to_bv 64 i)) ->
      amid fx' R' M' md' LKi Awi cri si smi eni ki ei Y ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri (pa_validate AD) Mi mdi) K.
Proof.
  intros MID J1 RAq J10 J11 Hn Hp0 Hp1 Hp2 DEFp ACCp LOC BYT LEN LB8 KONT'. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
  assert (ASTKv : L5CA.astk ar Mi (sp - 128) 12288).
  { apply (L5SAR.astk_sub ar Mi Mi sp 26624 128 12288 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia|].
    replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  unfold PECVSA.validate_fun_spec in VAL.
  apply (VAL fxi Ri Mi mdi K LBi FF' LKi Awi cri pp n (sp - 128) q l HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536.
    split; [exact ASTKv|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKB.mod16_8'. replace (sp - 128 - 12288) with (sp + (-776) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMBUAR.ffroomA_push 7 0 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMBUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact J10. }
  { rewrite L5K.rl11. exact J11. }
  { exact Hn. } { exact Hp0. } { exact Hp1. } { exact Hp2. } { exact DEFp. } { exact ACCp. }
  { intros a Ha. apply (PMBSR1.vis_scan L ar C HI LY HIok _ FF' LKi cri Awi Mi mdi pp n HHi); [| exact Ha].
    destruct LOC as [X'|[(Bq & mq & Hin & X1 & X2)|(X1 & X2)]]; [left; exact X'| right; right; exists Bq, mq; split; [exact Hin| split; [exact X1| exact X2]]| right; left].
    unfold FS_BYTES. clear - X1 X2 F1 F2 Eotb Eop. lia. }
  { change (PMSPA.pm_scr 0) with 12288.
    destruct LOC as [X'|[(Bq & mq & Hin & X1 & X2)|(X1 & X2)]]; [left; exact X'| |].
    - right. right. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (WBi & _). pose proof (WBi _ Hin) as ((_ & _ & _ & _ & Xc & _) & _). cbn [fst snd] in Xc.
      clear - X2 Xc SLO. lia.
    - right. right. clear - X2 Eotb Eop F2 FSCEIL SLO. lia. }
  { exact BASE. }
  { exact BYT. } { exact LEN. } { exact LB8. }
  intros fx8 R8 M8 model8 v RP8 FBT8 MG8 MRT8 AM8 HH8 V11 Hv HV.
  assert (AH8 : L5CA.ahpres L ar LBi FF' (sp - 128) 12288 [] Mi M8).
  { apply (PMBUAR.ahpres_of_frame_but L ar C HI LY HIok LBi FF' LKi cri Awi Mi M8 (vml_of mdi) (sp - 128) 12288 HHi);
      [clear - SPT; lia| clear - SLO; lia| clear; lia| exact FBT8| exact MG8|].
    pose proof ASTKv as (_ & _ & _ & _ & X' & _). exact X'. }
  assert (BI8 : PMBUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned si eni ki) M8 model8 LKi cri Awi).
  { apply (PMBUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) (PEC.owned si eni ki) (PEC.owned si eni ki) Mi mdi LKi cri Awi M8 model8 LKi cri Awi 12288 [] BI AH8 HH8 AM8 MRT8 (incl_refl _) (incl_refl _));
      [clear; lia| clear; lia| intros rr a []| intros a _ _ rr []| intros a X'; exact X']. }
  pose proof (L5SAR.ek_callee L ar LBi [] FF [(F, 0, sp - 128 + 32)] sp 26624 (sp - 128) 12288 [] [] Mi M8 ltac:(rewrite app_nil_l; exact AH8) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK8.
  apply (KONT' fx8 R8 M8 model8 v RP8).
  { rewrite <- L5K.rl11. exact V11. }
  { exact Hv. } { exact HV. } { exact MG8. }
  { intros i Hi' Ni. apply FBT8. intros rr [<-|[]]. unfold L5.in_rng. cbn [fst snd]. rewrite L5.unsigned_lit by exact Hi'. change (PMSPA.pm_scr 0) with 12288. clear - Ni. lia. }
  split; [|split; [exact BI8| split; [| split; [exact ST| split; [exact EIMP| exact CK]]]]].
  - pose proof (fun j Hj => L5SAR.cs_of_preserved Ri R8 j RP8 Hj) as R8c.
    split; [rewrite (R8c 2%nat) by inl; exact J2|]. split; [rewrite (R8c 8%nat) by inl; exact J8|]. split; [rewrite (R8c 9%nat) by inl; exact J9|].
    split; [rewrite (R8c 18%nat) by inl; exact J18|]. split; [rewrite (R8c 19%nat) by inl; exact J19|]. split; [rewrite (R8c 20%nat) by inl; exact J20|].
    split; [rewrite (R8c 21%nat) by inl; exact J21|]. split; [rewrite (R8c 24%nat) by inl; exact J24|]. split; [rewrite (R8c 25%nat) by inl; exact J25|].
    split; [rewrite (R8c 26%nat) by inl; exact J26|].
    intros j Hj. rewrite (R8c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - apply (cpre_keepA LBi sp 26624 [] Mi M8 Y si smi eni ki ei EK8 PMKB.wapp_nil BRBi); [unfold LBi; apply incl_appl; apply incl_refl| unfold LBi; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP].
Qed.

Lemma call_slot (d : Z * list Z) (q : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 ov ->
  PECSPA.args_key RSEGS AD d FF' Ri Mi (sp - 128) fb si ->
  PECSPA.mp_enc p Y -> s_bad (e_key (Z.of_nat (length (snd d))) Y) = false -> PESKA.spa_hb P (s_hi (e_key (Z.of_nat (length (snd d))) Y)) ->
  (forall fx' R' M' md' LK' Aw' en' k' e' cr', regs_preserved Ri R' ->
      amid fx' R' M' md' LK' Aw' cr' si smi en' k' e' (e_key (Z.of_nat (length (snd d))) Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri (pe_key EE) Mi mdi) K.
Proof.
  intros MID J1 RAq J10 ARGS MPE NB' HB' KONT'. entry_facts. frame_facts. open_amid MID.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
  unfold PECSB.v_key_spec, PECSPA.v_key_spec, PECSPA.eslot_spec in VK.
  apply (VK PMODE d fxi Ri Mi mdi K LBX FF' LKi Awi cri (sp - 128) q fb cat p Y si str smi eni ki ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 4) with 20480. change (20480 / 8) with 2560.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 26624 128 20480 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKB.mod16_8'. replace (sp - 128 - 20480) with (sp + (-1288) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMBUAR.ffroomA_push 7 4 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMBUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { replace (sp - 128) with (sp + (-4) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
  { rewrite L5K.rl10. exact J10. }
  { exact ARGS. }
  { exact CP. } { exact INCS. } { exact POK. } { exact MPE. } { exact NB'. } { exact HB'. }
  { exact (cred_enc Mi Y si smi eni ki ei cri CP (credit_le_keep _ _ _ _ CRED CK)). }
  intros fxn Rn Mn mdn LKn Awn en2 k2 e2 cr2 RP2 CPRE2 EIMP2 HP2 CK2 MRT2 INCLK2 INCAw2 AM2 HH2.
  change (PMSPA.pm_scr 4) with 20480 in HP2.
  assert (WeIN : forall rr, In rr (PEC.W_enc AD EE fb) -> In rr WR).
  { intros rr Hin. unfold PEC.W_enc, PMSP.err_W in Hin. cbn [app] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold WR; [wr_mem 9| wr_mem 10| wr_mem 6| wr_mem 7| wr_mem 8]. }
  assert (BI2 : PMBUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned si en2 k2) Mn mdn LKn cr2 Awn).
  { apply (PMBUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) (PM.parser_own si) (PEC.owned si en2 k2) Mi mdi LKi cri Awi Mn mdn LKn cr2 Awn 20480 (PEC.W_enc AD EE fb) BI HP2 HH2 AM2 MRT2 INCAw2 INCLK2);
      [clear; lia| clear; lia| intros rr a Hin Hr; exact (wr_wav rr a (WeIN rr Hin) Hr)| intros a _ O rr Hin Hr; exact (O rr (WeIN rr Hin) Hr)| intros a X'; exact X']. }
  assert (CK2' : PMSP.credit_keep cri cr2 (PECA.pot_allA L ar P si eni ki) (PECA.pot_allA L ar P si en2 k2)).
  { unfold PMSP.credit_keep, PECA.pot_allA, PECA.pot_encA, PEC.credit_add in CK2 |- *. cbn [fst snd] in CK2 |- *. clear - CK2. lia. }
  apply (KONT' fxn Rn Mn mdn LKn Awn en2 k2 e2 cr2 RP2).
  split; [|split; [exact BI2| split; [exact CPRE2| split; [exact ST| split; [intros X'; exact (EIMP2 (EIMP X'))| exact (credit_keep_trans _ _ _ _ _ _ CK CK2')]]]]].
  pose proof (fun j Hj => L5SAR.cs_of_preserved Ri Rn j RP2 Hj) as Rnc.
  split; [rewrite (Rnc 2%nat) by inl; exact J2|]. split; [rewrite (Rnc 8%nat) by inl; exact J8|]. split; [rewrite (Rnc 9%nat) by inl; exact J9|].
  split; [rewrite (Rnc 18%nat) by inl; exact J18|]. split; [rewrite (Rnc 19%nat) by inl; exact J19|]. split; [rewrite (Rnc 20%nat) by inl; exact J20|].
  split; [rewrite (Rnc 21%nat) by inl; exact J21|]. split; [rewrite (Rnc 24%nat) by inl; exact J24|]. split; [rewrite (Rnc 25%nat) by inl; exact J25|].
  split; [rewrite (Rnc 26%nat) by inl; exact J26|].
  intros j Hj. rewrite (Rnc j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply J34. exact Hj.
Qed.

Lemma tail_RK fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_more Y = true -> r_key p X = w_more true Y ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri 0xb8ea8 Mi mdi) K.
Proof.
  intros MID MOREY RV. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).
  pose proof (PMBPAR.op_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb _ si HHi FOK' PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  fold Hi in Zop, Z32, Z20, OWR, OVIS. fold MVi in Zop, Z32, Z20, OWR.
  destruct (APART op 384 0 0) as (ApF & ApSF & ApFL).
  { intros i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048.
    split; [clear - Eop Hi'; lia| intros Y'; clear - Eop Hi' Y'; lia]. }
  { clear; lia. }
  change (ff_bytes 0) with 64 in ApF, ApSF. change (64 / 8) with 8 in ApSF. unfold SB in ApSF.
  assert (SHop : op / 8 + 2147450880 = fb / 8 + 2147450880 + 74).
  { rewrite Eop. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
    replace (2048 * (fb / 2048) + 592) with ((256 * (fb / 2048) + 74) * 8) by (clear; lia). rewrite Z.div_mul by lia.
    replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
  destruct (APART (op / 8 + 2147450880) 48 0 0) as (_ & AsopSF & _).
  { intros i Hi'. unfold aclient, aclient_g. do 5 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. unfold in_shadow_of, S. unfold SB.
    assert (D1 : (fb + 2048 - 1) / 8 = fb / 8 + 255).
    { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
      replace (2048 * (fb / 2048) + 2048 - 1) with (7 + (256 * (fb / 2048) + 255) * 8) by (clear; lia). rewrite Z.div_add by lia.
      replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
    rewrite D1. clear - SHop Hi'. lia. }
  { clear; lia. }
  change (64 / 8) with 8 in AsopSF. unfold SB in AsopSF.
  pose proof OWNv as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26.
  pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  pose proof PA as (_ & _ & _ & _ & _ & _ & P16 & _).
  assert (U16 : L5.u8_at RSEGS MVi (op + 16) 0).
  { apply (proj2 (L5A.u8_at_vis Hi Mi (op + 16) 0 (OVIS (op + 16) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). exact P16. }
  destruct (k2_run fxi Ri R MVi sp op ov oec F fl) as (fx7 & R7 & M7v & MG7 & FRZ7 & MS7 & K347 & REG7 & E72 & FL0 & MO0);
    first [assumption | clear - GSLO GSHI GSPT; lia | clear - O1 O3; lia | clear - O1 O3 Eop Eov; lia | clear - O1 O3 Eop Eoec; lia | clear - GFR; lia
          | clear - GL1 GL2; lia | clear - O2 GSLO; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | exact SP32 | exact O8 | exact GF32 | idtac].
  all: try (clear - ApF; lia). all: try (clear - ApFL; lia). all: try (clear - AsopSF; lia).
  assert (R7ra : getr R7 (reg 1) = Z_to_bv 64 r) by (rewrite (REG7 1%nat) by inl; exact Rra).
  pose proof (PMK.ret_to RSEGS fx7 R7 M7v 0xb8e54 W_b8e04 r F_b8e04 eq_refl D_b8e04 R7ra Hr1 Hr2) as MSr.
  apply (PMBUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
           WR (PEC.owned si eni ki) Mi mdi LKi cri Awi (fun a => op + 8 <= a < op + 9) fxi fx7 Ri 0xb8ea8 R7 r M7v K BI).
  { intros a X'. split.
    - apply (L5SAR.fframe_client L ar (PEC.owned si eni ki ++ LBX) FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - X' Eop; lia].
    - intros O. apply (O (PMSP.o_p AD fb + 8, 8)); [unfold WR; wr_mem 0| wr_rng; clear - X' Eop; lia]. }
  { intros a. destruct (L5SAR.rng_dec a (op + 8) (op + 9)) as [X'|X']; [left; exact X'| right; exact X']. }
  { exact (msteps_trans _ _ _ _ MS7 MSr). }
  { exact MG7. }
  { intros a Ha Nw. unfold PMBUK.WretX, PMBUK.Wret in Nw. change (ff_bytes 0) with 64 in Nw.
    apply FRZ7; [exact Ha| intros X'; apply Nw; right; clear - X'; lia| intros X'; apply Nw; left; left; left; clear - X'; lia
                | intros X'; apply Nw; left; left; right; unfold SB; clear - X'; lia| intros X'; apply Nw; left; right; clear - X'; lia]. }
  { exact FL0. }
  intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict Hi Mf = M7v) in VISf.
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  assert (EKf : L5SAR.ek L ar LBi FF 0 0 [(op + 8, 1)] Mi Mf).
  { apply (PMBUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k)
             LBi LKi cri Awi Mi Mf _ [(op + 8, 1)] (fun a => op + 8 <= a < op + 9) G HHi).
    - intros a X' O. apply (O (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X'; lia].
    - exact FZf. }
  pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  assert (MO0f : L5.u8_at RSEGS Mf (op + 8) 1).
  { apply (proj1 (L5A.u8_at_vis Hi Mf (op + 8) 1 (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). rewrite VISf. exact MO0. }
  assert (WAPP8 : PMKB.wapp [(op + 8, 1)]).
  { apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OBIG; lia. }
  assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i).
  { intros a n X3 i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi' Hr X3. lia. }
  assert (OUTB8 : forall q' m, In (q', m) LBi -> forall i, q' <= i < q' + m -> L5.outside [(op + 8, 1)] i).
  { intros q' m Hq i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
    destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi Hq (PMBUAR.aobjA_push FF op 384 _ AOP)) as [Z'|Z']; clear - Hi' Hr Z'; lia. }
  assert (Iq : In (PM.sr_qc (PM.p_src si), PM.CHUNK) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (Ib : In (PM.p_b si, 32 * 2 ^ PM.p_k si) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
  apply (KONT fx7 R7 Mf modelf LKi Awi (PMPK.set_more si 1) smi eni ki ei cri).
  - apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite E72; exact (eq_sym Rsp) | apply REG7; inl | rewrite (K347 _) by inl; apply J34; inl ] |]).
    destruct Hj.
  - destruct (BRBi _ Iq) as (Xq1 & Xq2). destruct (BRBi _ Ib) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2. unfold PM.CHUNK in Xq2.
    rewrite RV. apply (cpre_stepA LBi 0 0 [(op + 8, 1)] Mi Mf Y si smi eni ki ei (w_more true Y) (PMPK.set_more si 1) ei EKf WAPP8 BRBi).
    + unfold LBi. apply incl_appl. apply incl_refl.
    + unfold LBi. apply incl_appr. exact INCS.
    + intros i Hi' Ni _. apply (OUT8 i 1); clear - Hi' Ni; lia.
    + intros q' m Hq. exact (OUTB8 q' m Hq).
    + reflexivity. + reflexivity. + reflexivity.
    + apply (PMBPAR.parser_more_updA Mi Mf op ois si 1 PA).
      * clear - O1; lia.
      * clear - O1 O3; lia.
      * apply (PMKB.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
      * apply (PMKB.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB (op + 9) 375 (AOF (op + 9) 375 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
      * exact (PMKB.agsh_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB op 384 AOP).
      * pose proof PA as (_ & PDi & _). apply (L5.defined_grows Mi Mf _ _ MGf PDi).
      * exact MO0f.
      * right; reflexivity.
      * exact Xq1.
      * unfold PM.CHUNK. clear - Xq2; lia.
      * apply (PMKB.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Iq). apply OUTB8. exact Iq.
      * exact Xb1.
      * clear - Xb2; lia.
      * apply (PMKB.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Ib). apply OUTB8. exact Ib.
      * intros c0 n0 p0 E0. assert (Ip : In (p0, c0) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
        apply (PMKB.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Ip). apply OUTB8. exact Ip.
    + change (PMSTA.base_okA RSEGS PMB.AD Mf). apply (PMBSK.base_keep L ar C LY LBi FF 0 0 [(op + 8, 1)] Mi Mf EKf); [| exact BASE]. intros a Ha. apply (OUT8 a 1); clear - Ha O1; lia.
    + apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBi FF 0 0 [(op + 8, 1)] Mi Mf EKf ei PECSB.addrs_wf_B); [| exact ERR].
      intros a D. change (PMST.dep PMB.AD a) in D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
      split; [clear - DI; lia|]. split; [exact (PMB.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply (OUT8 a 1); clear - DI O1; lia.
    + destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
      unfold PEC.clink, PMPK.set_more. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_more PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src PEC.b2z].
      split; [reflexivity|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|].
      split; [intros _ X'; exact (Lpos MOREY X')|]. split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad].
    + cbn [s_ec w_more]. apply (PECFA.ec_state_keepA RSEGS AD L ar LBi FF 0 0 [(op + 8, 1)] Mi Mf EKf WAPP8 FRB fb (s_ec Y) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
      fold oec. apply OUT8. clear - Eop Eoec; lia.
    + cbn [s_ec w_more]. exact ECI.
    + exact CP.
  - unfold PMPK.set_more. cbn [PM.p_src]. exact ST.
  - exact EIMP.
  - exact AHf.
  - unfold PMSP.credit_keep, PMPK.set_more, PECA.pot_allA, PEC.credit_add, PM.pot_parser in CK |- *. cbn [PM.p_k PM.p_tb PM.p_tg fst snd] in CK |- *. exact CK.
  - exact MRTf.
  - exact INCLi.
  - exact INCAi.
  - exact AMf.
  - unfold PMPK.set_more. change (PEC.owned (PM.PST 0 (PM.p_done si) (PM.p_depth si) (PM.p_src si) (PM.p_tb si) (PM.p_tg si) (PM.p_b si) (PM.p_k si) (PM.p_stk si)) eni ki)
      with (PEC.owned si eni ki). exact HHf.
Qed.

Lemma amid_regs fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fx' : FPState) R' md' :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat -> getr R' (reg j) = getr Ri (reg j)) ->
  ri_inv HI (PEC.owned si eni ki ++ LBX) FF' LKi cri Awi Mi (vml_of md') -> L5CA.amodel_ok Awi md' -> model_rt mdi md' ->
  amid fx' R' Mi md' LKi Awi cri si smi eni ki ei Y.
Proof.
  intros MID RR HH' AM' MRT'. open_amid MID.
  split; [|split; [exact (PMBUK.binv_model L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned si eni ki) Mi mdi LKi cri Awi md' BI HH' AM' MRT')| split; [exact CP| split; [exact ST| split; [exact EIMP| exact CK]]]]].
  split; [rewrite (RR 2%nat) by inl; exact J2|]. split; [rewrite (RR 8%nat) by inl; exact J8|]. split; [rewrite (RR 9%nat) by inl; exact J9|].
  split; [rewrite (RR 18%nat) by inl; exact J18|]. split; [rewrite (RR 19%nat) by inl; exact J19|]. split; [rewrite (RR 20%nat) by inl; exact J20|].
  split; [rewrite (RR 21%nat) by inl; exact J21|]. split; [rewrite (RR 24%nat) by inl; exact J24|]. split; [rewrite (RR 25%nat) by inl; exact J25|].
  split; [rewrite (RR 26%nat) by inl; exact J26|].
  intros j Hj. rewrite (RR j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply J34. exact Hj.
Qed.

End Frame.

Ltac open_amid MID :=
  pose proof MID as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J24 & J25 & J26 & J34) & BI & CP & ST & EIMP & CK);
  pose proof BI as (HHi & AMi & MRTi & INCAi & INCLi & ASTKi & EKbi & DKbi & OWNi & FSHDi);
  pose proof AMi as (Mhi & MIi).

Ltac vis_amidM G F fl LK2 M2 model2 BI Hh Mv :=
  let X := fresh "VF" in
  pose proof (PMBUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
                WR _ _ _ _ _ _ BI) as X;
  destruct X as ((WSi & ICi & CSBi & CUARi & _) & OWNv & (FDi & FWi & FSWi & FLCi & FLWi) & (FLCci & FLVi & VFi & VSi & VSHi));
  change (ff_bytes 0) with 64 in WSi, FDi, FWi, FSWi, FLCi, VFi, VSHi; change (64 / 8) with 8 in FSWi, VSHi;
  replace (sp - (sp - 128)) with 128 in WSi by (clear; lia); replace (F + 64 - 8) with (F + 56) in FLCi by (clear; lia);
  fold Hh in WSi, ICi, CSBi, CUARi, OWNv, FDi, FWi, FSWi, FLCi, FLWi, FLVi, VFi, VSi, VSHi; fold Mv in WSi, ICi, CSBi, CUARi, OWNv, FDi, FWi, FSWi, FLCi, FLWi.

Theorem read_key_call : srealizes RSEGS SCFG (PMSPA.cfg RSEGS R (pa_read_key AD) M model) K.
Proof.
  entry_facts.
  pose proof AM as (Mh & MI).
  pose proof A10 as X10. pose proof A11 as X11. pose proof A12 as X12. rewrite L5K.rl10 in X10. rewrite L5K.rl11 in X11. rewrite L5K.rl12 in X12.
  fold op in X10. fold ov in X11. fold oec in X12.
  pose proof CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  destruct MP as (PRE & DONE & HALT & DEPB & ESTKB & STKB). pose proof PRE as (PRE0 & MORE). pose proof PRE0 as (BOK & PPOS & PLH & PBAD & PED & PEOK).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model op 384 sp 26624 HH (PMKB.aobj_of_aobjA FF op 384 AOP O8) ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF & OVIS & _).
  set (LB := PEC.owned s en k ++ LBX) in *.
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  assert (BASE' : PMSTA.base_okA RSEGS PMB.AD M) by exact BASE.
  pose proof (PMBSK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE') as (IC0 & CSBv & CUARv). fold H in IC0, CSBv, CUARv. fold MV in IC0, CSBv, CUARv.
  pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 26624 128 HH ASTK ltac:(lia)) as (SL128 & SH128 & SWR). fold H in SWR. fold MV in SWR.

  pose proof (PEBRDKEYP.arkA_conc fx R MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | unfold PEBRDKEYP.aligned; assumption | clear - SL128 SHI SPT; lia | clear - O1 O3; lia | clear - O1 O3 Eop Eov; lia | clear - O1 O3 Eop Eoec; lia]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & _ & T19 & T20 & T21 & T26
                 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C128).
  unfold PMSPA.cfg. cbn [pa_read_key AD PeCLayoutB.CADDR_B].
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb8c1c R1 0x5ec3c M1v (fun a => sp - 128 <= a < sp - 128 + 128) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X'; clear - X' Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL128 SHI SPT; lia| intros X'; clear - X'; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (NCS0 : forall a, sp - 128 <= a < sp -> ~ aclient L ar LB FF sp 26624 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 26624 a HH SPT Hc) as [Y|Y].
    - clear - Xa Y; lia.
    - clear - Xa Y SL128; lia. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 26624 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 26624 [] M M1 (fun a => sp - 128 <= a < sp - 128 + 128) FR1). intros a Ha Hc _ X'. apply (NCS0 a); [clear - X'; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 26624 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKB.ek_sublb L ar LB LBX FF sp 26624 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKB.dk_sublb L ar LB LBX FF sp 26624 M M1 INCX DK01f) as DK01.
  assert (SV1 : forall a v, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X'. apply (proj1 (L5A.u64_at_vis H M1 a v (VIS a 8 ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X'. }
  assert (OWN1 : own sp R M1).
  { unfold own. split; [apply SV1; [clear; lia| clear; lia| exact C8]|]. split; [apply SV1; [clear; lia| clear; lia| exact C16]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C24]|]. split; [apply SV1; [clear; lia| clear; lia| exact C32]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C40]|]. split; [apply SV1; [clear; lia| clear; lia| exact C48]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C56]|]. split; [apply SV1; [clear; lia| clear; lia| exact C64]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C72]|]. split; [apply SV1; [clear; lia| clear; lia| exact C80]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C88]|]. apply SV1; [clear; lia| clear; lia| exact C96]. }
  clear C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 C128 SV1.

  assert (FRk0 : ff_room 0 FF LK) by (pose proof (FRM 0 ltac:(left; reflexivity)) as X'; unfold ff_room; clear - X'; lia).
  change 0x5ec3c with (PMB.SM_PC 0).
  apply (PMBUAR.uar_sm L ar C HI LY HIok 0 LBX (PEC.owned s en k) FF LK cr Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K 0xb8c90 ltac:(left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk0. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 0) with 64 in FW, FSHW, FSHZ, FLC, FLW, FDEF, VF, VSH. change (64 / 8) with 8 in FSHW, FSHZ, VSH. change (64 - 8) with 56 in FLC.
  fold LB in EK12f, DK12f, APART.
  pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in GFS2, GFCEIL, GFLC, GFR, GF8, GFBIG, GFLA, GNCF. unfold FS_BYTES in GFS2, GFLP.

  pose proof (L5SAR.ek_trans L ar LB FF sp 26624 [] M M1 M2 EK01f EK12f) as EK02f.
  pose proof (L5SAR.dk_trans L ar LB FF sp 26624 M M1 M2 DK01f DK12f) as DK02f.
  assert (HH2 : ri_inv HI LB ((F, 0, sp - 128 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (PMBSK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 26624 128 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2). fold H2 in SWR2. fold MV2 in SWR2.

  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B19R : getr R2 (reg 19) = Z_to_bv 64 op) by (rewrite (R2c 19%nat) by inl; exact T19).
  assert (B20R : getr R2 (reg 20) = Z_to_bv 64 oec) by (rewrite (R2c 20%nat) by inl; exact T20).
  assert (B21R : getr R2 (reg 21) = Z_to_bv 64 ov) by (rewrite (R2c 21%nat) by inl; exact T21).
  assert (B26R : getr R2 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R2c 26%nat) by inl; exact T26).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
  assert (FLCv : L5.u64_at RSEGS MV2 (F + 56) fl) by (replace (F + 56) with (F + 64 - 8) by (clear; lia); exact FLC).
  assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64)
    by (clear - SL128 SHI SPT O1 O3 Eop Eov Eoec GFR GFLR; lia).
  destruct Q0 as (Q0a & Q0b & Q0c & Q0d & Q0f & Q0g).
  assert (Q1 : 140735332487296 <= sp <= 140737488355328) by (clear - SL128 SHI SPT; lia).
  assert (Q3 : 6930432 <= F <= 140737488355264) by (clear - GFR; lia).
  assert (Q4 : (sp - 128) + 128 <= F \/ F + 64 <= (sp - 128)) by (clear - GFCEIL SL128; lia).
  assert (Q5 : (sp - 128) + 128 <= fl \/ fl + 1 <= (sp - 128)) by (clear - GFLR SL128; lia).
  assert (Q7 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
  pose proof (PEBRDKEYP.arkB_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | unfold PEBRDKEYP.aligned; assumption]).
  destruct PP as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & _ & _ & Y18 & Y24 & Y25 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & YD).
  set (W3 := fun a => (sp - 104 <= a < sp - 104 + 8) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xb8c90 R3 (pa_get_length AD) M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; clear - X'; lia| intros X'; apply Hn; right; left; clear - X'; lia| intros X'; apply Hn; right; right; clear - X'; lia]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X'|[X'|X']].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SL128 SHI SPT; lia| intros Y'; clear - Y'; lia].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X'; lia.
    - destruct Wa as [X'|[X'|X']]; clear - X' GFR SL128 SPT; lia. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (EK23f : L5SAR.ek L ar LB FF sp 26624 [] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 26624 [] M2 M3 W3 FR3). intros a Ha Hc _ X'. destruct X' as [X'|[X'|X']].
    - apply (NCS0 a); [clear - X'; lia| exact Hc].
    - destruct (APART a 1 sp 26624 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y' & _). change (ff_bytes 0) with 64 in Y'. clear - X' Y'; lia.
    - destruct (APART a 1 sp 26624 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y' & _). change (ff_bytes 0 / 8) with 8 in Y'. unfold SB in Y'. clear - X' Y'; lia. }
  pose proof (L5SAR.ek_trans L ar LB FF sp 26624 [] M M2 M3 EK02f EK23f) as EK03f.
  assert (DK23f : L5SAR.dk L ar LB FF sp 26624 M2 M3) by (apply L5SAR.dk_grows; exact MGM3).
  pose proof (L5SAR.dk_trans L ar LB FF sp 26624 M M2 M3 DK02f DK23f) as DK03f.
  assert (OWN3 : own sp R M3).
  { apply (own_agree sp R M1 M3 ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha.
    rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL128 SHI SPT; lia| intros [X'|[X'|X']]; clear - X' Ha GFCEIL GFR SL128 SPT; unfold SB in *; lia]. }
  assert (BI3 : PMBUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned s en k) M3 model3 LK2 cr Aw).
  { unfold PMBUK.binv. split; [exact HH3|]. split; [exact AM3|].
    split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 26624 ASTK2 MGM3)|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 26624 WR [] M M3 (PMKB.ek_sublb L ar LB LBX FF sp 26624 [] M M3 INCX EK03f)); intros a _ r0 []|].
    split; [exact (PMKB.dk_sublb L ar LB LBX FF sp 26624 M M3 INCX DK03f)|].
    split; [exact OWN3|].
    change (ff_bytes 0 / 8) with 8. apply (L5.defined_grows M2 M3 _ _ MGM3).
    apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 8 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  assert (AMID3 : amid F fx3 R3 M3 model3 LK2 Aw cr s sm en k e X).
  { unfold amid. split; [| split; [exact BI3| split; [| split; [| split; [intros X'; exact X'| unfold PMSP.credit_keep; clear; lia]]]]].
    - split; [rewrite (KS3 2%nat) by inl; exact B2R|]. split; [rewrite (KS3 8%nat) by inl; exact B8R|]. split; [rewrite (KS3 9%nat) by inl; exact B9R|].
      split; [exact Y18|]. split; [rewrite (KS3 19%nat) by inl; exact B19R|]. split; [rewrite (KS3 20%nat) by inl; exact B20R|].
      split; [rewrite (KS3 21%nat) by inl; exact B21R|]. split; [exact Y24|]. split; [exact Y25|]. split; [rewrite (KS3 26%nat) by inl; exact B26R|].
      intros j Hj. rewrite (KS3 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
      rewrite (R2c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
      apply KS1. revert j Hj. apply (L5K.incl_b [3; 4; 27]%nat). vm_compute. reflexivity.
    - apply (cpre_keepA LB sp 26624 [] M M3 X s sm en k e EK03f PMKB.wapp_nil BRB); [unfold LB; apply incl_appl; apply incl_refl| unfold LB; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CPRE].
    - unfold PMSPA.src_step. split; [reflexivity|]. split; [reflexivity|]. split; [clear; lia|]. split; [intros X'; exact X'| clear; lia]. }
  clear FR3 W3 FRZ3 MS3 YD OWN3 OWN1 EK23f DK23f.

  apply (call_gl F fl LK2 M2 model2 G 0xb8d28 fx3 R3 M3 model3 LK2 Aw cr s sm en k e X AMID3 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11).
  { unfold PECSPA.mp_gl. split; [exact BOK|]. split; [exact PPOS|]. split; [exact MORE|]. split; [exact DONE|]. split; [exact HALT| exact PBAD]. }
  intros fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 e4 RP4 RET4 AMID4 ETB ETG EB EK4.
  unfold PECSPA.gl_post in AMID4. unfold PECSPA.gl_ret in RET4.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).

  assert (GE : forall YG, amid F fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en k e4 YG -> s_ec YG = true ->
               PECRVD.but_pos (r_key p X) (w_more false (w_ec true YG)) -> srealizes RSEGS SCFG (PMSPA.cfg RSEGS R4 0xb8d28 M4 md4) K).
  { intros YG MIDg EY BP.
    pose proof MIDg as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J24 & J25 & J26 & J34) & BIg & CPg & STg & EEg & CKg).
    pose proof BIg as (HHg & AMg & MRTg & _ & _ & ASTKg & _).
    pose proof CPg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ECSg & _).
    unfold PECA.ec_stateA in ECSg. rewrite EY in ECSg. fold oec in ECSg. destruct ECSg as (v & Hv & ECv).
    pose proof (PMBPAR.oec_vis L ar C HI LY HIok _ _ LK4 cr4 Aw4 M4 md4 fb v _ HHg FOK' ECv) as ((QE1 & QE8 & QENSH) & ZE4 & EW4 & ECE & EU4 & _ & _).
    set (H4 := ahid Aw4 md4) in *. set (MV4 := mrestrict H4 M4) in *.
    pose proof (bv_unsigned_in_range 64 (getr R4 (reg 10))) as B10. change (bv_modulus 64) with (2 ^ 64) in B10.
    assert (G10' : getr R4 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R4 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (QEF : (sp - 128) + 128 <= oec \/ oec + 16 <= (sp - 128)) by (clear - ECE SLO; lia).
    pose proof (PEBRDKEYP.arkCe_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F
                                                     | 49%nat => bv_unsigned (getr R4 (reg 10)) | 50%nat => v | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | unfold PEBRDKEYP.aligned; assumption | clear - Hv; lia]).
    destruct PP as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z10 & Z11 & _).
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr4 Aw4 M4 md4 fx4 fx5 R4 0xb8d28 R5 0xafda8 MV4 K HHg AMg MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid F fx5 R5 M4 md5 LK4 Aw4 cr4 s4 sm4 en k e4 YG).
    { apply (amid_regs F fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en k e4 YG fx5 R5 md5 MIDg); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec F fl LK2 M2 model2 G 0xb8f04 12 fx5 R5 M4 md5 LK4 Aw4 cr4 s4 sm4 en k e4 YG MID5 Z1 ltac:(split; [clear; lia| reflexivity]) Z10 Z11 ltac:(clear; lia)).
    intros fx6 R6 M6 md6 LK6 Aw6 RP6 MID6.
    apply (tail_Z F fl LK2 M2 model2 G APART 0xb8f04 fx6 R6 M6 md6 LK6 Aw6 cr4 s4 sm4 en k true (w_ec true YG) z12_run MID6); [reflexivity| exact BP]. }
  destruct (UbjRef.get_length p (s_pos X)) as [[n pos1]|] eqn:GLd.
  2: { apply (GE (r_fail X) AMID4 eq_refl). rewrite (PECRKD.r_key_none p X GLd). apply PECRKD.but_pos_fail_refail0. }
  pose proof (get_length_some p (s_pos X) n pos1 BOK ltac:(clear - PPOS; lia) GLd) as (Hn & Hpos1 & _).
  destruct (s_ec X) eqn:EX.
  { apply (GE (w_pos pos1 X) AMID4 ltac:(cbn; exact EX)). rewrite (PECRKD.r_key_pending p X n pos1 GLd EX). apply PECRKD.but_pos_fail_any2. }

  rewrite L5K.rl10 in RET4.
  pose proof AMID4 as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J24 & J25 & J26 & J34) & BI4 & CP4 & ST4 & EE4 & CK4).
  pose proof BI4 as (HH4 & AM4 & MRT4 & _ & _ & ASTK4 & _).
  pose proof CP4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ECS4 & _).
  unfold PECA.ec_stateA in ECS4. cbn [s_ec w_pos] in ECS4. rewrite EX in ECS4. fold oec in ECS4.
  pose proof (PMBPAR.oec_vis L ar C HI LY HIok _ _ LK4 cr4 Aw4 M4 md4 fb 0 _ HH4 FOK' ECS4) as ((QE1 & QE8 & QENSH) & ZE4 & EW4 & ECE & EU4 & _ & _).
  set (H4 := ahid Aw4 md4) in *. set (MV4 := mrestrict H4 M4) in *.
  assert (QEF : (sp - 128) + 128 <= oec \/ oec + 16 <= (sp - 128)) by (clear - ECE SLO; lia).
  pose proof (PEBRDKEYP.arkC0_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 49%nat => n | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | unfold PEBRDKEYP.aligned; assumption | clear - Hn; lia]).
  destruct PP as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z10 & Z11 & Z12 & Z22).
  assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr4 Aw4 M4 md4 fx4 fx5 R4 0xb8d28 R5 (pa_read_span AD) MV4 K HH4 AM4 MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
  assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
  assert (MID5 : amid F fx5 R5 M4 md5 LK4 Aw4 cr4 s4 sm4 en k e4 (w_pos pos1 X)).
  { apply (amid_regs F fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en k e4 (w_pos pos1 X) fx5 R5 md5 AMID4); [| exact HH5| exact AM5| exact MRT5].
    intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
  apply (call_span F fl LK2 M2 model2 G n 0xb8d54 fx5 R5 M4 md5 LK4 Aw4 cr4 s4 sm4 en k e4 (w_pos pos1 X) MID5 ltac:(cbn; exact MORE) ltac:(cbn; exact DONE) ltac:(cbn [s_pos w_pos]; clear - Hpos1 PPOS; lia)
           Z1 ltac:(split; [clear; lia| reflexivity]) Z10 Z11 Z12 ltac:(clear - Hn; lia)).
  intros fxn Rn Mn mdn LKn Awn crn sn smn ptr n2 RPn V10 V11 Hn2 Hn26 LOC DEFn ACCn BYTn NMIN MIDn Ebn Ekn. cbn [s_pos w_pos] in BYTn, NMIN, MIDn.
  assert (WW : w_pos (pos1 + n2) (w_pos pos1 X) = w_pos (pos1 + n2) X) by (destruct X; reflexivity). rewrite WW in MIDn. clear WW.
  pose proof MIDn as ((K2 & K8 & K9 & K18 & K19 & K20 & K21 & K24 & K25 & K26 & K34) & BIn & CPn & STn & EEn & CKn).
  pose proof BIn as (HHn & AMn & MRTn & _ & _ & ASTKn & _).
  assert (S22n : getr Rn (reg 22) = Z_to_bv 64 n) by (rewrite (L5SAR.cs_of_preserved R5 Rn 22 RPn) by inl; exact Z22).
  pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHn) as BRBn.
  assert (PTRR : 0 <= ptr < 2 ^ 64 /\ (n2 = 0 \/ 0 < ptr) /\ ptr + n2 <= 2 ^ 47).
  { destruct LOC as [(E0 & E0')|[(B & m & HinB & HB1 & HB2)|(T1' & T2')]].
    - clear - E0 E0'. lia.
    - destruct (BRBn (B, m) ltac:(apply in_or_app; left; unfold PEC.owned; apply in_or_app; left; exact HinB)) as (B0 & B4). cbn [fst snd] in B0, B4.
      pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHn) as (WBn & _).
      pose proof (WBn (B, m) ltac:(apply in_or_app; left; unfold PEC.owned; apply in_or_app; left; exact HinB)) as ((Bl & _) & _). cbn [fst snd] in Bl.
      clear - B0 B4 Bl HB1 HB2 Hn2. lia.
    - clear - T1' T2' Eotb Eop O1 O3 Hn2. lia. }
  destruct PTRR as (PT0 & PT1 & PT2).
  set (Hn' := ahid Awn mdn) in *. set (MVn := mrestrict Hn' Mn) in *.

  pose proof (PEBRDKEYP.arkF_conc fxn Rn MVn (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 49%nat => n | 51%nat => ptr | 52%nat => n2 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | clear - Hn; lia | clear - PT0; lia | clear - Hn2 Hn; lia]).
  destruct PP as (fx5' & R5' & M5v' & MG5' & _ & FRZ5' & [(MS5' & KS5' & QF1 & QF11 & QF23 & CQ) | (MS5' & KS5' & QF1 & QF10 & QF11 & CQ)]).
  -
    assert (En : n2 = n).
    { clear - CQ Hn Hn2. destruct (Z.eq_dec n2 n) as [E|N]; [exact E| exfalso].
      replace (n2 - n) with ((n2 - n + 2 ^ 64) + (-1) * 2 ^ 64) in CQ by lia. rewrite Z.mod_add in CQ by lia. rewrite Z.mod_small in CQ by lia. lia. }
    apply eq_sym in En. subst n. clear CQ.
    assert (LEN : pos1 + n2 <= blen p) by (clear - NMIN Hn Hpos1; lia). rename n2 into n.
    assert (E5 : M5v' = MVn) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5'; exact Ha). subst M5v'.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKn crn Awn Mn mdn fxn fx5' Rn 0xb8d54 R5' (pa_validate AD) MVn K HHn AMn MS5' (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5' md5' HH5' AM5' MRT5' HID5' VIS5' MGM5' FR5'.
    assert (E5 : M5' = Mn) by (apply L5SAR.mem_eq_of_agree; exact FR5'). subst M5'.
    assert (MID5' : amid F fx5' R5' Mn md5' LKn Awn crn sn smn en k e4 (w_pos (pos1 + n) X)).
    { apply (amid_regs F fxn Rn Mn mdn LKn Awn crn sn smn en k e4 (w_pos (pos1 + n) X) fx5' R5' md5' MIDn); [| exact HH5'| exact AM5'| exact MRT5'].
      intros j Hj. apply KS5'. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    assert (SLEN : Z.of_nat (length (UbjRef.slice p pos1 n)) = n) by (apply PECRVD.slice_length; clear - Hn Hpos1 LEN PPOS; lia).
    assert (SBYT : Forall (fun b => 0 <= b < 256) (UbjRef.slice p pos1 n)) by (apply PECRVD.slice_bytes; exact BOK).
    apply (call_valid F fl LK2 M2 model2 G ptr n 0xb8d64 (UbjRef.slice p pos1 n) fx5' R5' Mn md5' LKn Awn crn sn smn en k e4 (w_pos (pos1 + n) X) MID5' QF1 ltac:(split; [clear; lia| reflexivity])
             ltac:(rewrite (KS5' 10%nat) by inl; exact V10) QF11 ltac:(clear - Hn Hn26; lia) ltac:(clear - PT0; lia) PT1 PT2 DEFn ACCn).
    { destruct LOC as [(E0 & E0')|[(B & m & HinB & HB1 & HB2)|(T1' & T2')]]; [left; exact E0'| right; left; exists B, m; split; [apply in_or_app; left; unfold PEC.owned; apply in_or_app; left; exact HinB| split; [exact HB1| exact HB2]]| right; right; split; [exact T1'| exact T2']]. }
    { exact BYTn. } { exact SLEN. } { exact SBYT. }
    intros fx6 R6 M6 md6 v RP6 V11' Hv HV MG6 FRZ6 MID6.
    pose proof MID6 as ((L2' & L8 & L9 & L18 & L19 & L20 & L21 & L24 & L25 & L26 & L34) & BI6 & CP6 & ST6 & EE6 & CK6).
    pose proof BI6 as (HH6 & AM6 & MRT6 & _ & _ & ASTK6 & _).
    assert (S22f : getr R6 (reg 22) = Z_to_bv 64 n) by (rewrite (L5SAR.cs_of_preserved R5' R6 22 RP6) by inl; rewrite (KS5' 22%nat) by inl; exact S22n).
    assert (S23f : getr R6 (reg 23) = Z_to_bv 64 ptr) by (rewrite (L5SAR.cs_of_preserved R5' R6 23 RP6) by inl; exact QF23).
    assert (PT4 : forall i, ptr <= i < ptr + n -> ~ (sp - 128 - 12288 <= i < sp - 128)).
    { destruct LOC as [(E0 & E0')|[(B & m & HinB & HB1 & HB2)|(T1' & T2')]].
      - intros i Hi. clear - Hi E0'. lia.
      - pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHn) as (WBn & _).
        pose proof (WBn (B, m) ltac:(apply in_or_app; left; unfold PEC.owned; apply in_or_app; left; exact HinB)) as ((_ & _ & _ & _ & Bc & _) & _). cbn [fst snd] in Bc.
        intros i Hi X'. clear - Hi X' Bc HB2 SLO. lia.
      - intros i Hi X'. clear - Hi X' T1' T2' Eotb Eop F2 FSCEIL SLO. lia. }
    assert (BYT6 : L5.bytes_at RSEGS M6 ptr (UbjRef.slice p pos1 n)).
    { apply (L5C.bytes_at_agree RSEGS Mn M6); [| clear - PT0; lia| rewrite SLEN; clear - PT2; lia| exact BYTn]. rewrite SLEN. intros i Hi. apply FRZ6; [clear - Hi PT0 PT2; lia| exact (PT4 i Hi)]. }
    assert (DEFp6 : L5.defined M6 ptr n) by exact (L5.defined_grows Mn M6 ptr n MG6 DEFn).
    assert (ACC6 : PMSPA.accA M6 ptr n).
    { apply (PMFA.accA_agree Mn M6 ptr n); [| exact ACCn]. intros x Hx. apply FRZ6.
      - unfold S, SB. clear - Hx PT0 PT2. split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia| lia]|].
        assert (x / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in H. lia.
      - unfold S, SB. intros X'. clear - X' SLO SHI SPT Hx PT0 PT2.
        assert (x / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia). lia. }
    set (H6 := ahid Awn md6) in *. set (MV6 := mrestrict H6 M6) in *.
    pose proof (bv_unsigned_in_range 64 (getr R6 (reg 11))) as B611. change (bv_modulus 64) with (2 ^ 64) in B611.

    pose proof (PEBRDKEYP.arkW_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 49%nat => n
                                                  | 51%nat => ptr | 53%nat => v | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | clear - Hn; lia | clear - PT0; lia | clear - Hv; lia]).
    destruct PP as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & [(MS7 & KS7 & CQ2) | (MS7 & KS7 & E1 & E10 & E11 & CQ2)]).
    +
      assert (Ev : v = 0) by (clear - CQ2 Hv; destruct (Z.eq_dec v 0) as [E|N]; [exact E| exfalso; rewrite Z.sub_0_r in CQ2; rewrite Z.mod_small in CQ2 by lia; lia]).
      assert (VT : UbjRef.utf8_valid (UbjRef.slice p pos1 n) = true) by (apply HV; exact Ev).
      assert (E7 : M7v = MV6) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). subst M7v.
      apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKn crn Awn M6 md6 fx6 fx7 R6 0xb8d64 R7 0xb8e58 MV6 K HH6 AM6 MS7 (fun x Hx => Hx) (fun a Ha => eq_refl)).
      intros M7 md7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7.
      assert (E7 : M7 = M6) by (apply L5SAR.mem_eq_of_agree; exact FR7). subst M7.
      assert (MID7 : amid F fx7 R7 M6 md7 LKn Awn crn sn smn en k e4 (w_pos (pos1 + n) X)).
      { apply (amid_regs F fx6 R6 M6 md6 LKn Awn crn sn smn en k e4 (w_pos (pos1 + n) X) fx7 R7 md7 MID6); [| exact HH7| exact AM7| exact MRT7].
        intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }

      pose proof MID7 as ((N2 & N8 & N9 & N18 & N19 & N20 & N21 & N24 & N25 & N26 & N34) & BI7 & CP7 & ST7 & EE7 & CK7).
      pose proof BI7 as (HH7' & AM7' & MRT7' & INCA7 & INCL7 & ASTK7 & EKb7 & _).
      pose proof CP7 as (PA7 & IA7 & EA7 & _ & _ & BASE7 & _).
      set (H7 := ahid Awn md7) in *. set (MV7 := mrestrict H7 M6) in *.
      vis_amidM G F fl LK2 M2 model2 BI7 H7 MV7.
      assert (S22g : getr R7 (reg 22) = Z_to_bv 64 n) by (rewrite (KS7 22%nat) by inl; exact S22f).
      assert (S23g : getr R7 (reg 23) = Z_to_bv 64 ptr) by (rewrite (KS7 23%nat) by inl; exact S23f).
      assert (AOF' : forall a m, fb + 32 <= a -> a + m <= fb + 2040 -> PMSPA.aobjA FF' a m) by (intros a m X1 X2; apply PMBUAR.aobjA_push; apply AOF; [exact X1| exact X2]).
      pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKn crn Awn M6 md7 ov 56 sp 26624 HH7' (PMKB.aobj_of_aobjA FF' ov 56 (AOF' ov 56 ltac:(lia) ltac:(lia)) Q8) ltac:(lia) ltac:(reflexivity))
        as ((V1 & V2 & V3 & V4 & V5) & VBIG & VDEF & VVIS & _). fold H7 in VVIS.
      pose proof EA7 as (EVT & _ & _ & _ & _ & _ & _ & _ & EACC & _). cbn [pe_vt EE PeCLayoutB.EADDR_B] in EVT.
      assert (UVP : L5.u64_at RSEGS MV7 ov 1277312) by (apply (proj2 (L5A.u64_at_vis H7 M6 ov _ (L5A.avis_sub H7 ov 56 ov 8 VVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - V1; lia) ltac:(clear - V3; lia))); exact EVT).
      assert (Zov : L5KA.zeros_at MV7 (ov / 8 + 2147450880) 1).
      { apply (L5KA.zeros_at_sub MV7 (ov / 8 + SB) (56 / 8)); [| unfold SB; clear; lia| unfold SB; change (56 / 8) with 7; clear; lia].
        apply (PMKB.obj_shadow_vis L ar C HI LYa HIok _ FF' LKn crn Awn M6 md7 ov 56 HH7' (AOF' ov 56 ltac:(lia) ltac:(lia)) Q8); [clear; lia| reflexivity| exact EACC]. }
      pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LKn crn Awn M6 md7 0x137de0 1 HH7' ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia)) as VTS.
      change (0x137de0 / 8 + 2147450880) with 2147610556 in VTS. fold H7 in VTS. fold MV7 in VTS.
      assert (Wov : L5.writable RSEGS MV7 ov 8).
      { apply (proj2 (L5A.writable_vis H7 M6 ov 8 (L5A.avis_sub H7 ov 56 ov 8 VVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - V1; lia) ltac:(clear - V3; lia))).
        apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M6 ov 56); [exact VDEF| clear; lia| clear; lia]| clear - V1; lia| clear - V3; lia]. }
      destruct (APART ov 56 0 0) as (AvF & AvSF' & _).
      { intros i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048.
        split; [clear - Eov Hi'; lia| intros Y'; clear - Eov Hi' Y'; lia]. }
      { clear; lia. }
      change (ff_bytes 0) with 64 in AvF.
      assert (SHov : ov / 8 + 2147450880 = fb / 8 + 2147450880 + 62).
      { rewrite Eov. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
        replace (2048 * (fb / 2048) + 496) with ((256 * (fb / 2048) + 62) * 8) by (clear; lia). rewrite Z.div_mul by lia.
        replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
      destruct (APART (ov / 8 + 2147450880) 7 0 0) as (_ & AvSF & _).
      { intros i Hi'. unfold aclient, aclient_g. do 5 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
        change (ff_bytes 5) with 2048. unfold in_shadow_of, S. unfold SB.
        assert (D1 : (fb + 2048 - 1) / 8 = fb / 8 + 255).
        { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
          replace (2048 * (fb / 2048) + 2048 - 1) with (7 + (256 * (fb / 2048) + 255) * 8) by (clear; lia). rewrite Z.div_add by lia.
          replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
        rewrite D1. clear - SHov Hi'. lia. }
      { clear; lia. }
      change (ff_bytes 0 / 8) with 8 in AvSF. unfold SB in AvSF.
      assert (Q9v : (F / 8 + 2147450880) + 8 <= 2147610556 \/ 2147610556 + 1 <= (F / 8 + 2147450880)).
      { clear - GFR GF8. assert (F / 8 >= 849920) by (apply Z.le_ge; apply Z.div_le_lower_bound; lia). lia. }
      assert (BASE7' : PMSTA.base_okA RSEGS PMB.AD M6) by exact BASE7.
      pose proof (PMBSK.mach_vis L ar C HI LY HIok _ FF' LKn crn Awn M6 md7 HH7' BASE7') as (IC7 & CSB7 & CUAR7). fold H7 in IC7, CSB7, CUAR7. fold MV7 in IC7, CSB7, CUAR7.
      pose proof (PEBRDKEYP.arkK1_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => n | 51%nat => ptr | _ => 0 end)) as PP.
      cbn beta iota in PP.
      L5SAR.feed PP ltac:(first [timeout 3 assumption | timeout 3 (unfold PEBRDKEYP.aligned; assumption) | (first [clear - Hn; lia | clear - PT0; lia | clear - GFR; lia | clear - GFLR; lia   (* timeout-ok: on expiry the next arm runs; without this limit the build exceeds 250 GiB *)
                               | clear - GFCEIL SLO; lia | clear - GFLR SLO; lia | clear - V1 V3; lia | clear - V2 SLO; lia | clear - VBIG; lia | clear - AvF; lia | clear - AvSF; lia])]).
      destruct PP as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & W1 & W10 & W11 & W12 & W13 & _ & K40 & K32 & SH5 & SH4 & _ & _).
      set (W8 := fun a => (F + 32 <= a < F + 32 + 16) \/ (F / 8 + 2147450880 + 4 <= a < F / 8 + 2147450880 + 4 + 2)).
      unfold PMSPA.cfg.
      apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LKn crn Awn M6 md7 fx7 fx8 R7 0xb8e58 R8 (pe_key EE) M8v W8 K HH7' AM7' MS8 MG8).
      { intros a Ha NW. apply FRZ8; [exact Ha| intros X'; apply NW; left; exact X'| intros X'; apply NW; right; exact X']. }
      { intros a Ha Wa. split.
        - destruct Wa as [X'|X'].
          + apply (L5SAR.fframe_client L ar _ FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X'; lia].
          + apply (L5SAR.fframe_shadow_client L ar _ FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
            unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X'; lia.
        - destruct Wa as [X'|X']; clear - X' GFR SLO SPT; lia. }
      intros M8 md8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8 VV8. change (mrestrict H7 M8 = M8v) in VIS8.
      assert (BI8 : PMBUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned sn en k) M8 md8 LKn crn Awn).
      { apply (PMBUK.binv_pieceW L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
                 WR (PEC.owned sn en k) M6 md7 LKn crn Awn M8 md8 W8 BI7 HH8 AM8 MRT8 MGM8 FR8).
        intros a X'. split; [unfold ocell; destruct X' as [X'|X']; clear - X' GFCEIL SLO SPT GFR; lia|].
        right. change (ff_bytes 0) with 64. change (64 / 8) with 8. unfold SB. destruct X' as [X'|X']; [left; clear - X'; lia| right; left; clear - X'; lia]. }
      set (LBn := PEC.owned sn en k ++ LBX) in *.
      assert (EK78 : L5SAR.ek L ar LBn FF 0 0 [] M6 M8).
      { apply (PMBUAR.wfr_ek L ar C HI LY HIok LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k)
                 LBn LKn crn Awn M6 M8 _ [] (fun _ => False) G HH7' (fun a X' => match X' with end)).
        intros a Ha N. apply FR8; [exact Ha|]. intros X'. apply N. unfold PMBUAR.Wfr. change (ff_bytes 0) with 64. change (64 / 8) with 8. unfold SB.
        left. left. destruct X' as [X'|X']; [left| right]; clear - X'; lia. }
      pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH7') as BRB7.
      assert (CP8 : PECA.crun_preA RSEGS AD AAD EE L ar P M8 fb p (w_pos (pos1 + n) X) sn str smn en k e4 cat).
      { apply (cpre_keepA LBn 0 0 [] M6 M8 (w_pos (pos1 + n) X) sn smn en k e4 EK78 PMKB.wapp_nil BRB7); [unfold LBn; apply incl_appl; apply incl_refl| unfold LBn; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP7]. }
      assert (MID8 : amid F fx8 R8 M8 md8 LKn Awn crn sn smn en k e4 (w_pos (pos1 + n) X)).
      { split; [| split; [exact BI8| split; [exact CP8| split; [exact ST7| split; [exact EE7| exact CK7]]]]].
        split; [rewrite (KS8 2%nat) by inl; exact N2|]. split; [rewrite (KS8 8%nat) by inl; exact N8|]. split; [rewrite (KS8 9%nat) by inl; exact N9|].
        split; [rewrite (KS8 18%nat) by inl; exact N18|]. split; [rewrite (KS8 19%nat) by inl; exact N19|]. split; [rewrite (KS8 20%nat) by inl; exact N20|].
        split; [rewrite (KS8 21%nat) by inl; exact N21|]. split; [rewrite (KS8 24%nat) by inl; exact N24|]. split; [rewrite (KS8 25%nat) by inl; exact N25|].
        split; [rewrite (KS8 26%nat) by inl; exact N26|].
        intros j Hj. rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply N34. exact Hj. }

      assert (K40' : L5.u64_at RSEGS M8 (F + 40) n).
      { apply (proj1 (L5A.u64_at_vis H7 M8 (F + 40) n (L5A.avis_sub H7 F 64 (F + 40) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GFR; lia) ltac:(clear - GFR; lia))). rewrite VIS8. exact K40. }
      assert (K32' : L5.u64_at RSEGS M8 (F + 32) ptr).
      { apply (proj1 (L5A.u64_at_vis H7 M8 (F + 32) ptr (L5A.avis_sub H7 F 64 (F + 32) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GFR; lia) ltac:(clear - GFR; lia))). rewrite VIS8. exact K32. }
      assert (SH4' : L5.u8_at RSEGS M8 (F / 8 + 2147450884) 0).
      { apply (proj1 (L5A.u8_at_vis H7 M8 _ 0 (L5A.avis_sub H7 (F / 8 + SB) 8 (F / 8 + 2147450884) 1 VSHi ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) ltac:(clear - GFR; lia) ltac:(clear - GFR; lia))). rewrite VIS8. exact SH4. }
      assert (SH5' : L5.u8_at RSEGS M8 (F / 8 + 2147450885) 0).
      { apply (proj1 (L5A.u8_at_vis H7 M8 _ 0 (L5A.avis_sub H7 (F / 8 + SB) 8 (F / 8 + 2147450885) 1 VSHi ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) ltac:(clear - GFR; lia) ltac:(clear - GFR; lia))). rewrite VIS8. exact SH5. }
      assert (PTF : n = 0 \/ (ptr + n <= F \/ F + 64 <= ptr)).
      { destruct LOC as [(E0 & E0')|[(B & m & HinB & HB1 & HB2)|(T1' & T2')]]; [left; exact E0'| |].
        - right. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHn) as (WBn & _).
          pose proof (WBn (B, m) ltac:(apply in_or_app; left; unfold PEC.owned; apply in_or_app; left; exact HinB)) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
          pose proof (FA (F, 0, sp - 128 + 32) ltac:(apply in_or_app; left; left; reflexivity)) as FA'. cbn [ff_addr ff_class fst snd] in FA'. change (ff_bytes 0) with 64 in FA'.
          clear - FA' HB1 HB2. lia.
        - right. destruct (APART (fb + 32) 2008 0 0) as (Y' & _); [| clear; lia|].
          + intros i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. clear - Hi'; lia.
          + change (ff_bytes 0) with 64 in Y'. clear - Y' T1' T2' Eotb Eop. lia. }
      assert (FRp : forall i, ptr <= i < ptr + n -> M8 (Z_to_bv 64 i) = M6 (Z_to_bv 64 i) /\ M8 (Z_to_bv 64 (S i)) = M6 (Z_to_bv 64 (S i))).
      { intros i Hi'. destruct PTF as [E0|PTF']; [exfalso; clear - Hi' E0; lia|]. split.
        - apply FR8; [clear - Hi' PT0 PT2; lia|]. intros [X'|X']; [clear - X' Hi' PTF'; lia|].
          pose proof (PMKB.S_in_shadow (F + 32) ltac:(clear - GFR; lia)) as SX. unfold S, BIGSHADOW_LO, BIGSHADOW_HI in SX. unfold SB in X'.
          pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHn) as (WBn & _).
          destruct LOC as [(E0 & E0')|[(B & m & HinB & HB1 & HB2)|(T1' & T2')]]; [clear - Hi' E0'; lia| |].
          + pose proof (WBn (B, m) ltac:(apply in_or_app; left; unfold PEC.owned; apply in_or_app; left; exact HinB)) as ((_ & _ & _ & _ & _ & APB) & _). cbn [fst snd] in APB.
            unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in APB. pose proof GF8 as (GF8a & _). clear - X' Hi' HB1 HB2 APB GF8a GFR. destruct APB as (_ & [Y'|Y'] & _); lia.
          + pose proof FSAPP as (FA0 & FA1 & FA2). pose proof GF8 as (GF8a & _). clear - X' Hi' T1' T2' Eotb Eop FA1 F1 F2 GF8a GFR. lia.
        - apply FR8.
          + unfold S, SB. clear - Hi' PT0 PT2. split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia| lia]|].
            assert (i / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia). lia.
          + intros [X'|X']; unfold S, SB in X'.
            * pose proof (PMKB.S_in_shadow i ltac:(clear - Hi' PT0 PT2; lia)) as SX. unfold S, SB, BIGSHADOW_LO, BIGSHADOW_HI in SX. clear - X' SX GFBIG. lia.
            * clear - X' Hi' PTF' GF8. pose proof GF8 as (GF8a & _).
              assert (i / 8 = F / 8 + 4 \/ i / 8 = F / 8 + 5) by lia.
              assert (F + 32 <= i < F + 48).
              { destruct H as [E|E]; (split; [| ]); Z.div_mod_to_equations; lia. }
              lia. }
      assert (BYT8 : L5.bytes_at RSEGS M8 ptr (UbjRef.slice p pos1 n)).
      { apply (L5C.bytes_at_agree RSEGS M6 M8); [| clear - PT0; lia| rewrite SLEN; clear - PT2; lia| exact BYT6]. rewrite SLEN. intros i Hi'. exact (proj1 (FRp i Hi')). }
      assert (ACC8 : PMSPA.accA M8 ptr n) by (apply (PMFA.accA_agree M6 M8 ptr n); [intros x Hx; exact (proj2 (FRp x Hx))| exact ACC6]).
      assert (DEF8 : L5.defined M8 ptr n) by exact (L5.defined_grows M6 M8 ptr n MGM8 DEFp6).

      assert (MPE : PECSPA.mp_enc p (w_pos (pos1 + n) X)).
      { unfold PECSPA.mp_enc. cbn [s_lo s_hi s_bad s_estk s_edepth w_pos]. split; [exact PLH|]. split; [exact PBAD|]. split; [exact PEOK|]. rewrite PED. exact DEPB. }
      pose proof NB as NB'. rewrite (PECRKD.r_key_valid p X n pos1 GLd EX LEN VT) in NB'. cbn [s_bad w_more] in NB'.
      pose proof HB as HB'. rewrite (PECRKD.r_key_valid p X n pos1 GLd EX LEN VT) in HB'. cbn [s_hi w_more] in HB'.
      apply (call_slot F fl LK2 M2 model2 G (ptr, UbjRef.slice p pos1 n) 0xb8ea8 fx8 R8 M8 md8 LKn Awn crn sn smn en k e4 (w_pos (pos1 + n) X) MID8 W1 ltac:(split; [clear; lia| reflexivity]) W10).
      { unfold PECSPA.args_key, PECSPA.args_sv. cbn [fst snd]. rewrite L5K.rl11, L5K.rl13. rewrite SLEN.
        split; [| split; [exact W13| exact VT]].
        exists (F + 32). split; [exact W11|]. split; [replace (F + 32) with (F / 8 * 8 + 4 * 8) by (clear - GF8; destruct GF8 as (X' & _); lia); rewrite Z_mod_plus_full; apply Z_mod_mult|].
        split; [exists (F, 0, sp - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 0) with 64; clear; lia]|].
        split.
        { intros a Ha. left. unfold byte_at, S.
          destruct (Z_lt_le_dec a (F + 40)) as [Xa|Xa].
          - rewrite (div8_off F a 4 (proj1 GF8)) by (clear - Ha Xa; lia). unfold SB. replace (F / 8 + 4 + 2147450880) with (F / 8 + 2147450884) by (clear; lia).
            apply (L5ADHR.byte_of_u8 M8 _ 0 SH4'); clear - GFR; lia.
          - rewrite (div8_off F a 5 (proj1 GF8)) by (clear - Ha Xa; lia). unfold SB. replace (F / 8 + 5 + 2147450880) with (F / 8 + 2147450885) by (clear; lia).
            apply (L5ADHR.byte_of_u8 M8 _ 0 SH5'); clear - GFR; lia. }
        split.
        {
          pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHn) as (_ & WFn & _).
          destruct (WFn (F, 0, sp - 128 + 32) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & APF).
          assert (Iin : In (fb, 5, rs) (ff_remove F FF' ++ LKn)) by (apply in_or_app; left; unfold FF'; cbn [ff_remove ff_addr fst snd]; rewrite Z.eqb_refl; exact Hfb).
          pose proof (APF _ Iin) as APF'. cbn [ff_addr ff_class fst snd] in APF'. change (ff_bytes 5) with 2048 in APF'. change (ff_bytes 0) with 64 in APF'. clear - APF'. lia. }
        split; [exact K32'|]. split; [replace (F + 32 + 8) with (F + 40) by (clear; lia); exact K40'|].
        split; [exact BYT8|]. split; [exact SBYT|]. split; [clear - Hn26; lia|]. split; [exact DEF8|]. split; [exact ACC8|].
        destruct LOC as [(E0 & E0')|[(B & m & HinB & HB1 & HB2)|(T1' & T2')]].
        - right. right. left. split; [exact E0|]. rewrite E0' in SLEN |- *. destruct (UbjRef.slice p pos1 0) eqn:ES; [reflexivity| exfalso; cbn in SLEN; clear - SLEN; lia].
        - left. exists B, m. split; [exact HinB|]. split; [exact HB1| exact HB2].
        - right. left. split; [exact T1'| exact T2']. }
      { exact MPE. }
      { cbn [snd]. rewrite SLEN. exact NB'. }
      { cbn [snd]. rewrite SLEN. exact HB'. }
      intros fx9 R9 M9 md9 LK9 Aw9 en9 k9 e9 cr9 RP9 MID9. cbn [snd] in MID9. rewrite SLEN in MID9.
      apply (tail_RK F fl LK2 M2 model2 G APART fx9 R9 M9 md9 LK9 Aw9 cr9 sn smn en9 k9 e9 (e_key n (w_pos (pos1 + n) X)) MID9).
      * rewrite PECRKD.e_key_more. cbn. exact MORE.
      * exact (PECRKD.r_key_valid p X n pos1 GLd EX LEN VT).
    +
      assert (Nv : v <> 0) by (clear - CQ2 Hv; intros E; subst v; rewrite Z.sub_0_r, Z.mod_0_l in CQ2 by lia; lia).
      assert (VFL8 : UbjRef.utf8_valid (UbjRef.slice p pos1 n) = false) by (destruct (UbjRef.utf8_valid (UbjRef.slice p pos1 n)) eqn:EV; [exfalso; apply Nv; apply HV; reflexivity| reflexivity]).
      assert (E7 : M7v = MV6) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). subst M7v.
      apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKn crn Awn M6 md6 fx6 fx7 R6 0xb8d64 R7 (pa_make_ec AD) MV6 K HH6 AM6 MS7 (fun x Hx => Hx) (fun a Ha => eq_refl)).
      intros M7 md7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7.
      assert (E7 : M7 = M6) by (apply L5SAR.mem_eq_of_agree; exact FR7). subst M7.
      assert (MID7 : amid F fx7 R7 M6 md7 LKn Awn crn sn smn en k e4 (w_pos (pos1 + n) X)).
      { apply (amid_regs F fx6 R6 M6 md6 LKn Awn crn sn smn en k e4 (w_pos (pos1 + n) X) fx7 R7 md7 MID6); [| exact HH7| exact AM7| exact MRT7].
        intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
      apply (call_mkec F fl LK2 M2 model2 G 0xb8d78 7 fx7 R7 M6 md7 LKn Awn crn sn smn en k e4 (w_pos (pos1 + n) X) MID7 E1 ltac:(split; [clear; lia| reflexivity]) E10 E11 ltac:(clear; lia)).
      intros fx8 R8 M8 md8 LK8 Aw8 RP8 MID8.
      apply (tail_Z F fl LK2 M2 model2 G APART 0xb8d78 fx8 R8 M8 md8 LK8 Aw8 crn sn smn en k true (w_ec true (w_pos (pos1 + n) X)) z7_run MID8); [reflexivity|].
      rewrite (PECRKD.r_key_invalid p X n pos1 GLd EX LEN VFL8). apply PECRKD.but_pos_fail_any.
  -
    assert (Nn : n2 < n).
    { clear - CQ Hn Hn2. destruct (Z.eq_dec n2 n) as [E|N]; [exfalso| lia]. subst n2. rewrite Z.sub_diag, Z.mod_0_l in CQ by lia. lia. }
    assert (SHORT : blen p < pos1 + n) by (clear - NMIN Nn Hn Hn2 Hpos1; lia).
    assert (E5 : M5v' = MVn) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5'; exact Ha). subst M5v'.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKn crn Awn Mn mdn fxn fx5' Rn 0xb8d54 R5' (pa_make_ec AD) MVn K HHn AMn MS5' (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5' md5' HH5' AM5' MRT5' HID5' VIS5' MGM5' FR5'.
    assert (E5 : M5' = Mn) by (apply L5SAR.mem_eq_of_agree; exact FR5'). subst M5'.
    assert (MID5' : amid F fx5' R5' Mn md5' LKn Awn crn sn smn en k e4 (w_pos (pos1 + n2) X)).
    { apply (amid_regs F fxn Rn Mn mdn LKn Awn crn sn smn en k e4 (w_pos (pos1 + n2) X) fx5' R5' md5' MIDn); [| exact HH5'| exact AM5'| exact MRT5'].
      intros j Hj. apply KS5'. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec F fl LK2 M2 model2 G 0xb8da4 1 fx5' R5' Mn md5' LKn Awn crn sn smn en k e4 (w_pos (pos1 + n2) X) MID5' QF1 ltac:(split; [clear; lia| reflexivity]) QF10 QF11 ltac:(clear; lia)).
    intros fx8 R8 M8 md8 LK8 Aw8 RP8 MID8.
    apply (tail_Z F fl LK2 M2 model2 G APART 0xb8da4 fx8 R8 M8 md8 LK8 Aw8 crn sn smn en k true (w_ec true (w_pos (pos1 + n2) X)) z1_run MID8); [reflexivity|].
    rewrite (PECRKD.r_key_short p X n pos1 GLd EX SHORT). apply PECRKD.but_pos_fail_any.
Qed.

End Call.

Theorem read_key_ok : PECSB.read_key_spec L ar HI P.
Proof.
  unfold PECSB.read_key_spec, PECSPA.read_key_spec, PECSPA.crun_spec.
  intros PMODE a fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 ARGS CPRE INCS POK MP NB HB CRED KONT.
  destruct ARGS as (A10 & A11 & A12). destruct a.
  exact (read_key_call PMODE fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 A11 A12 CPRE INCS POK MP NB HB CRED KONT).
Qed.
End WithHeap.
End PEBCRDKEY.
