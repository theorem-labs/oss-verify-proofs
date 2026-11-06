(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 338 of its 373 lines of code are new or changed and 1243 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntProC.v, with its module names changed; 73 of its 108 lines of code are new or changed and 338 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoEntryShapes DiscoArm3 DiscoEntSeatStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoRo DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JtokIs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_age_c reac_disco_table_json_c disco_json_text disco_json_reader_model disco_json_lemmas
slot_ser_defs slot_ser_pure slot_ser_tokb.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoArm3FieldCut.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition MDS_OFF : Z := 0x2198.
Definition MDJ_OFF : Z := 0x21a8.

Definition dsh_age (k : Z) : Z := if (258 <=? k) && (k <? 261) then 0 else dsh_md k.

Definition a3f_age (T : list byte) (now p : Z) : Z := disco_json_text.age_of now (disco_table_c.last_of T p).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition mdb_c1 (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p : Z) : world SEGS -> config -> Prop :=
  a3f_st B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad
    (SIGMA DS___interceptor_trampoline_snprintf - BASE) dsh_age
    (fun regs => getr regs 1 = w64 (BASE + MDS_OFF) /\
       getr regs 10 = w64 (d_obj cx OAGE) /\ getr regs 11 = w64 24 /\ getr regs 12 = w64 (VAL (A_OBJ 18)) /\
       getr regs 13 = w64 (a3f_age T1 now p) /\ getr regs 19 = w64 (d_obj cx OAGE) /\
       getr regs 21 = w64 (d_obj cx OO + 144 * p))
    (fun W m => a3f_pyk cx p count W m).

Definition mdb_c2 (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p : Z) : world SEGS -> config -> Prop :=
  a3f_st B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad AF_jtok_is dsh_age
    (fun regs => getr regs 1 = w64 (BASE + MDJ_OFF) /\
       getr regs 10 = w64 (d_obj cx OO + 144 * p + 120) /\ getr regs 11 = w64 2 /\
       getr regs 12 = w64 (d_obj cx OAGE))
    (fun W m => a3f_pyk cx p count W m /\
       garr8 SEGS (rd W m) (d_obj cx OAGE) (disco_json_text.dec (a3f_age T1 now p) ++ [0])).

Definition mdb_c3 (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p : Z) : world SEGS -> config -> Prop :=
  a3f_st B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad MDJ_OFF dsh_age
    (fun regs => getr regs 10 = w64 1)
    (fun W m => a3f_pyk cx p count W m).

Definition mdbA_stmt (p : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (W : world SEGS) (c : config),
  f_mo B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p W c ->
  SRr SEGS W c (mdb_c1 cx h i n now op W0 c0 T0 T1 buf count os vpad p).

Definition mdbB_stmt (p : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (W : world SEGS) (c : config),
  mdb_c1 cx h i n now op W0 c0 T0 T1 buf count os vpad p W c ->
  SRr SEGS W c (mdb_c2 cx h i n now op W0 c0 T0 T1 buf count os vpad p).

Definition mdbC_stmt (p : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (W : world SEGS) (c : config),
  mdb_c2 cx h i n now op W0 c0 T0 T1 buf count os vpad p W c ->
  SRr SEGS W c (mdb_c3 cx h i n now op W0 c0 T0 T1 buf count os vpad p).

Definition mdbD_stmt (p : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (W : world SEGS) (c : config),
  mdb_c3 cx h i n now op W0 c0 T0 T1 buf count os vpad p W c ->
  SRr SEGS W c (fun W' c' =>
    (p + 1 < count /\ f_ph B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad (p + 1) W' c') \/
    r14_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W' c').

Lemma mdb_of_parts : forall p, mdbA_stmt p -> mdbB_stmt p -> mdbC_stmt p -> mdbD_stmt p ->
  seg_mdb_p_spec B MT XM_LIB RLO RHI tfib_K p.
Proof.
  intros p HA HB HC HD cx h i n now op W0 c0 T0 T1 buf count os vpad W c Hs.
  eapply SRr_bind; [exact (HA cx h i n now op W0 c0 T0 T1 buf count os vpad W c Hs)|].
  intros W1 c1 _ H1.
  eapply SRr_bind; [exact (HB cx h i n now op W0 c0 T0 T1 buf count os vpad W1 c1 H1)|].
  intros W2 c2 _ H2.
  eapply SRr_bind; [exact (HC cx h i n now op W0 c0 T0 T1 buf count os vpad W2 c2 H2)|].
  intros W3 c3 _ H3.
  exact (HD cx h i n now op W0 c0 T0 T1 buf count os vpad W3 c3 H3).
Qed.

End h.
End f.
End d.
