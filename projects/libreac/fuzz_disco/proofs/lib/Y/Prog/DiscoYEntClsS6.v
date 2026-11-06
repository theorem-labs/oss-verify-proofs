(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 1243 of its 1273 lines of code are new or changed and 39 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntCls.v, with its module paths and module names changed; 58 of its 99 lines of code are new or changed and 1232 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt ClassifyCore DiscoYEntClsCuts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis L7 : cl_L7_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis L8 : cl_L8_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis L9 : cl_L9_stmt B MT XM_LIB RLO RHI tfib_K.

Lemma s6_LI_lt : forall cx h i n now op nb fr len nn k W c,
  cl_LI B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len nn k W c -> 0 <= k < nn.
Proof.
intros cx h i n now op nb fr len nn k W c H. unfold cl_LI, d_at in H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & kk & acc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hk & _).
exact Hk.
Qed.

Lemma s6_LJ_lt : forall cx h i n now op nb fr len nn k j W c,
  cl_LJ B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len nn k j W c -> 0 <= k < j /\ j < nn.
Proof.
intros cx h i n now op nb fr len nn k j W c H. unfold cl_LJ, d_at, cl_jregs in H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & kk & acc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkj & Hjn & _).
exact (conj Hkj Hjn).
Qed.

Lemma s6_inner : forall m cx h i n now op nb fr len nn k j W c,
  Z.of_nat m = nn - j ->
  cl_LJ B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len nn k j W c ->
  SRr SEGS W c (fun W' c' => cl_X B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W' c' \/
    cl_LI B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len nn (k + 1) W' c').
Proof.
induction m as [|m IH]; intros cx h i n now op nb fr len nn k j W c Hm H.
- destruct (s6_LJ_lt cx h i n now op nb fr len nn k j W c H) as (_ & Hj). lia.
- eapply SRr_bind; [exact (L8 cx h i n now op nb fr len nn k j W c H)|]. intros W1 c1 _ HB.
  eapply SRr_bind; [exact (L9 cx h i n now op nb fr len nn k j W1 c1 HB)|].
  intros W2 c2 _ [HJ | [HI | HX]].
  + apply (IH cx h i n now op nb fr len nn k (j + 1) W2 c2); [lia | exact HJ].
  + apply SRr_ret. right. exact HI.
  + apply SRr_ret. left. exact HX.
Qed.

Lemma s6_outer : forall m cx h i n now op nb fr len nn k W c,
  Z.of_nat m = nn - k ->
  cl_LI B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len nn k W c ->
  SRr SEGS W c (cl_X B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len).
Proof.
induction m as [|m IH]; intros cx h i n now op nb fr len nn k W c Hm H.
- pose proof (s6_LI_lt cx h i n now op nb fr len nn k W c H) as Hk. lia.
- eapply SRr_bind; [exact (L7 cx h i n now op nb fr len nn k W c H)|]. intros W1 c1 _ [HX | HJ].
  + apply SRr_ret. exact HX.
  + destruct (s6_LJ_lt cx h i n now op nb fr len nn k (k + 1) W1 c1 HJ) as (Hkj & Hjn).
    eapply SRr_bind.
    { apply (s6_inner (Z.to_nat (nn - (k + 1))) cx h i n now op nb fr len nn k (k + 1) W1 c1);
        [lia | exact HJ]. }
    intros W2 c2 _ [HX | HI].
    * apply SRr_ret. exact HX.
    * apply (IH cx h i n now op nb fr len nn (k + 1) W2 c2); [lia | exact HI].
Qed.

Theorem pb_cl_loop : cl_loop_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold cl_loop_stmt. intros cx h i n now op nb fr len nn k W c H.
pose proof (s6_LI_lt cx h i n now op nb fr len nn k W c H) as Hk.
apply (s6_outer (Z.to_nat (nn - k)) cx h i n now op nb fr len nn k W c); [lia | exact H].
Qed.

End h.
End f.
End d.
