(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 1243 of its 1273 lines of code are new or changed and 39 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntCls.v; 50 of its 99 lines of code are new or changed and 1224 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody
ClassifyCore ReacDiscoClassify ReacDiscoClassifyOnSegment CheckSighting ReacDiscoGateShouldPush DiscoEntClsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntClsLoop7 DiscoEntClsLoop8 DiscoEntClsLoop9 DiscoEntClsLoop10.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Lemma cll_LI_rng : forall cx h i n now op nb fr len nn k W c,
  cl_LI B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len nn k W c -> 0 <= k < nn.
Proof.
intros cx h i n now op nb fr len nn k W c H. unfold cl_LI, d_at in H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & kk & acc & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP).
destruct HP as (_ & Hk & _). exact Hk.
Qed.

Lemma cll_LJ_rng : forall cx h i n now op nb fr len nn k j W c,
  cl_LJ B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len nn k j W c -> 0 <= k < j /\ j < nn.
Proof.
intros cx h i n now op nb fr len nn k j W c H. unfold cl_LJ, d_at in H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & kk & acc & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP).
destruct HP as (_ & HJ). unfold cl_jregs in HJ. destruct HJ as (Hk & Hj & _). exact (conj Hk Hj).
Qed.

Lemma cl_loop_of : cl_L7_stmt B MT XM_LIB RLO RHI tfib_K -> cl_L8_stmt B MT XM_LIB RLO RHI tfib_K ->
  cl_L9_stmt B MT XM_LIB RLO RHI tfib_K -> cl_loop_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros L7 L8 L9 cx h i n now op nb fr len nn.
assert (OUTER : forall (m : nat) k W c, Z.of_nat m = nn - k ->
  cl_LI B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len nn k W c ->
  SRr SEGS W c (cl_X B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len)).
{ induction m as [|m IH]; intros k W c Hm HI;
    pose proof (cll_LI_rng _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as Hk; [lia|].
  assert (INNER : forall (m' : nat) j W1 c1, Z.of_nat m' = nn - j -> k < j < nn ->
    cl_LJ B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len nn k j W1 c1 ->
    SRr SEGS W1 c1 (fun W' c' => cl_X B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W' c' \/
      cl_LI B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len nn (k + 1) W' c')).
  { induction m' as [|m' IH']; intros j W1 c1 Hm' Hj HJ; [lia|].
    eapply SRr_bind; [exact (L8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)|]. intros W2 c2 _ HBR.
    eapply SRr_bind; [exact (L9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ HBR)|]. intros W3 c3 _ [HJ3 | [HI3 | HX3]].
    - pose proof (cll_LJ_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as Hj3.
      apply (IH' (j + 1)); [lia | lia | exact HJ3].
    - apply SRr_ret. right. exact HI3.
    - apply SRr_ret. left. exact HX3. }
  eapply SRr_bind; [exact (L7 _ _ _ _ _ _ _ _ _ _ _ _ _ HI)|]. intros W1 c1 _ [HX1 | HJ1].
  - apply SRr_ret. exact HX1.
  - pose proof (cll_LJ_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as Hj1.
    eapply SRr_bind; [exact (INNER (Z.to_nat (nn - (k + 1))) (k + 1) W1 c1 ltac:(lia) ltac:(lia) HJ1)|].
    intros W2 c2 _ [HX2 | HI2].
    + apply SRr_ret. exact HX2.
    + apply (IH (k + 1)); [lia | exact HI2]. }
intros k W c HI. pose proof (cll_LI_rng _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as Hk.
apply (OUTER (Z.to_nat (nn - k)) k); [lia | exact HI].
Qed.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).

Theorem cl_loop : cl_loop_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
apply cl_loop_of.
- exact (cl_L7 B MT XM_LIB RLO RHI tfib_K LAWS TL).
- exact (cl_L8 B MT XM_LIB XM_LIB RLO RHI tfib_K LAWS TL ABCMP).
- exact (cl_L9 B MT XM_LIB RLO RHI tfib_K LAWS).
Qed.

End h.
End f.
End d.
