(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmEncSpecs2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VBK.
Import PMES.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma regs_ok_updn : forall E sr (R : bvmap 5 word) (n : nat) e, (0 < n < 32)%nat ->
  regs_ok E sr R -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E e -> regs_ok E (sr_upd sr n e) R.
Proof.
  intros E sr R n e Hn HR He r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
  - specialize (HR r). unfold sr_get in HR. rewrite Er in HR. exact HR.
  - rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx r) n) as [en|ne].
    + assert (r = Z_to_bv 5 (Z.of_nat n)) as -> by (rewrite <- (CC.reg_of_ridx r), en; reflexivity). exact He.
    + specialize (HR r). unfold sr_get in HR. rewrite Er in HR. exact HR.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_sub : forall (M : mem) p (bs : list Z) (k n : nat), (k + n <= length bs)%nat ->
  L5.bytes_at RSEGS M p bs -> L5.bytes_at RSEGS M (p + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros M p bs k n Hkn HB i Hi. rewrite length_firstn, length_skipn in Hi.
  rewrite nth_firstn. replace (Nat.ltb i n) with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_skipn.
  replace (p + Z.of_nat k + Z.of_nat i) with (p + Z.of_nat (k + i)) by lia. apply HB. lia.
Qed.
Lemma rdn_of_bytes : forall (M : mem) p (bs : list Z) (k n : nat), (k + n <= length bs)%nat -> 0 <= p -> p + Z.of_nat (length bs) <= 2 ^ 64 ->
  L5.bytes_at RSEGS M p bs -> rdn RSEGS M (Z_to_bv 64 (p + Z.of_nat k)) n = Some (map (fun z => Z_to_bv 8 z) (firstn n (skipn k bs))).
Proof.
  intros M p bs k n Hkn Hp Hn HB.
  pose proof (bytes_at_sub M p bs k n Hkn HB) as HS.
  assert (HL : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  assert (Hn2 : p + Z.of_nat k + Z.of_nat (length (firstn n (skipn k bs))) <= 2 ^ 64) by (rewrite HL; lia).
  assert (Hp2 : 0 <= p + Z.of_nat k) by lia.
  pose proof (L5C.bytes_at_rdn RSEGS M (firstn n (skipn k bs)) (p + Z.of_nat k) Hp2 Hn2 HS) as R. rewrite HL in R. exact R.
Qed.

(* [comment removed for export] *)
Lemma ctx_at_xfer : forall (M M' : mem) a a' c (bs : list Z) (k : nat),
  (k + 32 <= length bs)%nat -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= a' -> a' + Z.of_nat (length bs) <= 2 ^ 64 ->
  L5.bytes_at RSEGS M a bs -> L5.bytes_at RSEGS M' a' bs -> L5.defined M' (a' + Z.of_nat k) 32 ->
  ctx_at M (a + Z.of_nat k) c -> ctx_at M' (a' + Z.of_nat k) c.
Proof.
  intros M M' a a' c bs k Hk Ha Han Ha' Han' HB HB' HD (C1 & C2 & C3 & C4 & C5 & C6).
  assert (X : forall (o n : nat) v, (o + n <= 32)%nat ->
             rdn RSEGS M (Z_to_bv 64 (a + Z.of_nat k + Z.of_nat o)) n = Some v -> rdn RSEGS M' (Z_to_bv 64 (a' + Z.of_nat k + Z.of_nat o)) n = Some v).
  { intros o n v Hon HR.
    pose proof (rdn_of_bytes M a bs (k + o) n ltac:(lia) Ha Han HB) as R1. replace (a + Z.of_nat (k + o)) with (a + Z.of_nat k + Z.of_nat o) in R1 by lia.
    pose proof (rdn_of_bytes M' a' bs (k + o) n ltac:(lia) Ha' Han' HB') as R2. replace (a' + Z.of_nat (k + o)) with (a' + Z.of_nat k + Z.of_nat o) in R2 by lia.
    rewrite HR in R1. injection R1 as R1. rewrite R2, R1. reflexivity. }
  unfold ctx_at, PML.u32, PML.u8, PML.u64, L5.u32_at, L5.u8_at, L5.u64_at in *.
  split; [|split; [|split; [|split; [|split; [exact C5 | exact HD]]]]].
  - pose proof (fun v => X 0%nat 4%nat v ltac:(lia)) as Y. cbn [Z.of_nat] in Y. rewrite !Z.add_0_r in Y. apply Y. exact C1.
  - apply (X 4%nat 1%nat _ ltac:(lia)). exact C2.
  - apply (X 6%nat 1%nat _ ltac:(lia)). exact C3.
  - apply (X 24%nat 8%nat _ ltac:(lia)). exact C4.
Qed.

(* [comment removed for export] *)
Lemma u_sra_lit : forall E e (s : Z) x, bv_unsigned (edenot E e) = x -> 0 <= x < 2 ^ 63 -> 0 <= s < 64 ->
  bv_unsigned (edenot E (EAlu ALU_SRA e (ELit s))) = x / 2 ^ s.
Proof.
  intros E e s x He Hx Hs. cbn [edenot]. rewrite u_sra64_nonneg by (rewrite He; lia). rewrite He. rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma u_mul_lit : forall E e (c : Z) x, bv_unsigned (edenot E e) = x -> 0 <= c < 2 ^ 64 -> 0 <= c * x < 2 ^ 64 ->
  bv_unsigned (edenot E (EMd M_MUL (ELit c) e)) = c * x.
Proof.
  intros E e c x He Hc Hcx. cbn [edenot]. rewrite u_mul64. rewrite He. rewrite (u64_of_Z c) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stack_blocks_zero : forall b, stack_blocks b 0 = [].
Proof. intros b. reflexivity. Qed.
Lemma stack_blocks_pos : forall b capb, capb <> 0 -> stack_blocks b capb = [(b, capb)].
Proof. intros b capb H. unfold stack_blocks. destruct (Z.eqb_spec capb 0); [lia | reflexivity]. Qed.

End VBK.
