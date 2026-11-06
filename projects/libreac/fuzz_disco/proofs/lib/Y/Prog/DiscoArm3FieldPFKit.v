(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module paths and module names changed; 326 of its 384 lines of code are new or changed and 438 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFKit.v, with its module paths, module names, addresses and numbers changed; 17 of its 114 lines of code are new or changed and 287 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0d YP0c YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv DiscoArm3.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3FieldCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_json_c disco_json_text disco_json_reader_model
slot_ser_defs slot_ser_tokb disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition PFR1_OFF : Z := 0x1e48.
Definition PFR2_OFF : Z := 0x1e5c.

Definition dsh_mac (k : Z) : Z :=
  if (k =? 216) || (k =? 217) then 0 else if k =? 218 then 2 else dsh_ser2 k.

Definition pf_mb (T : list byte) (j k : Z) : Z :=
  nth (Z.to_nat (48 * (j - 1) + k)) (map (fun b : byte => bv_unsigned b) T) 0.

Definition pf_mtext (T : list byte) (j : Z) : list Z :=
  disco_json_text.mac_text (disco_json_text.e_mac (reac_disco_table_json_c.tj_entry T (j - 1))).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition pf_Rj (cx : dcx) (j : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 21 = w64 (shadow_addr (d_FB cx)) /\
  getr regs 22 = w64 (2 ^ 64 - 1) /\ getr regs 23 = w64 (j - 1) /\ getr regs 25 = w64 j /\
  getr regs 26 = w64 (d_obj cx OT + 48 * (j - 1) + 2).

Definition pf_Y (cx : dcx) (p count j : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  a3f_slots cx p count W m /\ 1 <= j <= p + 1 /\
  val_mem SEGS (rd W m) (d_A cx + 408) 8 (d_obj cx OO + 144 * p) /\
  garr8 SEGS (rd W m) (d_obj cx OUSED) (a3f_used p).

Definition pf_c1 (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) : world SEGS -> config -> Prop :=
  a3f_stg B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad
    (SIGMA AS___interceptor_trampoline_snprintf - BASE) (-16) dsh_mac
    (fun regs => getr regs 1 = w64 (BASE + PFR1_OFF) /\ pf_Rj cx j regs /\
       getr regs 10 = w64 (d_obj cx OMAC) /\ getr regs 11 = w64 18 /\ getr regs 12 = w64 (VAL (A_OBJ 10)) /\
       getr regs 13 = w64 (pf_mb T1 j 0) /\ getr regs 14 = w64 (pf_mb T1 j 1) /\ getr regs 15 = w64 (pf_mb T1 j 2) /\
       getr regs 16 = w64 (pf_mb T1 j 3) /\ getr regs 17 = w64 (pf_mb T1 j 4) /\
       getr regs 27 = w64 (d_obj cx OMAC))
    (fun W m => pf_Y cx p count j W m /\ val_mem SEGS (rd W m) (d_A cx - 16) 8 (pf_mb T1 j 5)).

Definition pf_c2 (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) : world SEGS -> config -> Prop :=
  a3f_stg B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad AF_both3_jtok_is 0 dsh_mac
    (fun regs => getr regs 1 = w64 (BASE + PFR2_OFF) /\ pf_Rj cx j regs /\
       getr regs 10 = w64 (d_obj cx OO + 144 * p) /\ getr regs 11 = w64 1 /\ getr regs 12 = w64 (d_obj cx OMAC))
    (fun W m => pf_Y cx p count j W m /\ garr8 SEGS (rd W m) (d_obj cx OMAC) (pf_mtext T1 j ++ [0])).

Definition pf_c3 (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) : world SEGS -> config -> Prop :=
  a3f_stg B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad PFR2_OFF 0 dsh_mac
    (fun regs => pf_Rj cx j regs /\ getr regs 10 = w64 (if j - 1 =? p then 1 else 0))
    (fun W m => pf_Y cx p count j W m).

Definition pfA_stmt (j : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (p : Z) (W : world SEGS) (c : config),
  f_pf B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c ->
  SRr SEGS W c (pf_c1 cx h i n now op W0 c0 T0 T1 buf count os vpad p j).

Definition pfB_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) (W : world SEGS) (c : config),
  pf_c1 cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c ->
  SRr SEGS W c (pf_c2 cx h i n now op W0 c0 T0 T1 buf count os vpad p j).

Definition pfC_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) (W : world SEGS) (c : config),
  pf_c2 cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c ->
  SRr SEGS W c (pf_c3 cx h i n now op W0 c0 T0 T1 buf count os vpad p j).

Definition pfD_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) (W : world SEGS) (c : config),
  pf_c3 cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c ->
  SRr SEGS W c (fun W' c' =>
    (j <= p /\ f_pf B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p (j + 1) W' c') \/
    f_pfx B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p W' c').

Lemma pf_of_parts : forall p j, pfA_stmt j -> pfB_stmt -> pfC_stmt -> pfD_stmt ->
  seg_pf_pj_spec B MT XM_LIB RLO RHI tfib_K p j.
Proof.
  intros p j HA HB HC HD cx h i n now op W0 c0 T0 T1 buf count os vpad W c Hs.
  eapply SRr_bind; [exact (HA cx h i n now op W0 c0 T0 T1 buf count os vpad p W c Hs)|].
  intros W1 c1 _ H1.
  eapply SRr_bind; [exact (HB cx h i n now op W0 c0 T0 T1 buf count os vpad p j W1 c1 H1)|].
  intros W2 c2 _ H2.
  eapply SRr_bind; [exact (HC cx h i n now op W0 c0 T0 T1 buf count os vpad p j W2 c2 H2)|].
  intros W3 c3 _ H3.
  exact (HD cx h i n now op W0 c0 T0 T1 buf count os vpad p j W3 c3 H3).
Qed.

End h.
End f.
End d.
