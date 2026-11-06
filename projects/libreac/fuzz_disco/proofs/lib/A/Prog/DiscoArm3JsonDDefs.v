(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 959 of its 988 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntObs.v, with its module paths and module names changed; 172 of its 221 lines of code are new or changed and 939 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3JsonC2Defs.v; 71 of its 116 lines of code are new or changed and 176 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition MID_OFF : Z := 0x14dc.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition jmid (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (fin : Z * list jobj) (p : Z) (cur : jobj) (count : Z) (acc : list jobj) (vpad : list byte)
  : world SEGS -> config -> Prop :=
  jcut B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf MID_OFF dsh_scr
    (fun regs => getr regs 10 = w64 (buf + (p + 1)) /\ getr regs 11 = w64 (p + 1) /\
       getr regs 12 = w64 (jbyte (a3_text T1 now) (p + 1)) /\ getr regs 21 = w64 (buf + 1 + p) /\
       getr regs 19 = w64 (- a3_r T1 now))
    (fun W m => jfin_ok T1 now fin /\ 0 <= p /\ p + 1 < a3_r T1 now /\ 0 <= count <= 7 /\
       length acc = Z.to_nat count /\
       jobjs_after (a3_text T1 now) fin (p + 1) count acc cur /\
       length cur = 6%nat /\ Forall (slot_ser_tokb.tok_inb (a3_text T1 now)) cur /\
       jmem cx buf count vpad (acc ++ [cur]) W m).

Definition jd_A_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (fin : Z * list jobj) (p : Z) (cur : jobj) (count : Z) (acc : list jobj) (vpad : list byte)
         (W : world SEGS) (c : config),
  joend_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf fin p cur count acc vpad W c ->
  SRr SEGS W c (jmid cx h i n now op W0 c0 T0 T1 buf fin p cur count acc vpad).

Definition jd_B_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (fin : Z * list jobj) (p : Z) (cur : jobj) (count : Z) (acc : list jobj) (vpad : list byte)
         (W : world SEGS) (c : config),
  at_byte (a3_text T1 now) (p + 1) 44 = true ->
  jobjs_from (a3_text T1 now) fin (p + 2) (count + 1) (acc ++ [cur]) ->
  jmid cx h i n now op W0 c0 T0 T1 buf fin p cur count acc vpad W c ->
  SRr SEGS W c (jobj_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf fin
    (p + 2) (count + 1) (acc ++ [cur]) vpad).

Definition jd_C_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (fin : Z * list jobj) (p : Z) (cur : jobj) (count : Z) (acc : list jobj) (vpad : list byte)
         (W : world SEGS) (c : config),
  at_byte (a3_text T1 now) (p + 1) 93 = true ->
  p + 2 = a3_r T1 now ->
  fin = (count + 1, acc ++ [cur]) ->
  jmid cx h i n now op W0 c0 T0 T1 buf fin p cur count acc vpad W c ->
  SRr SEGS W c (jr12 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf).

Lemma jd_count_le : forall (T1 : list byte) (now : Z) (fin : Z * list jobj) (i2 count : Z)
  (acc : list jobj) (cur : jobj),
  jfin_ok T1 now fin -> jobjs_after (a3_text T1 now) fin i2 count acc cur -> count <= 7.
Proof.
  intros T1 now fin i2 count acc cur (_ & Hf & _) HA.
  pose proof (jobjs_after_count (a3_text T1 now) fin i2 count acc cur HA). lia.
Qed.

Lemma jd_acc_add : forall (T1 : list byte) (now : Z) (fin : Z * list jobj) (i2 count : Z)
  (acc : list jobj) (cur : jobj),
  jfin_ok T1 now fin -> jobjs_after (a3_text T1 now) fin i2 count acc cur ->
  jacc_add count acc cur = acc ++ [cur].
Proof.
  intros T1 now fin i2 count acc cur HF HA.
  pose proof (jd_count_le T1 now fin i2 count acc cur HF HA) as Hc.
  unfold jacc_add. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma jseg_D_of_parts : jd_A_stmt -> jd_B_stmt -> jd_C_stmt -> jseg_D B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros HA HB HC cx h i n now op W0 c0 T0 T1 buf fin p cur count acc vpad W c HE.
  destruct (jcut_x B MT XM_LIB RLO RHI tfib_K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE)
    as (m & HFIN & Hp & Hcount & Hlen & Hb & HAF & Hcur6 & Hcurin & HM).
  pose proof HFIN as (_ & _ & HNW & _).
  pose proof (jd_count_le T1 now fin (p + 1) count acc cur HFIN HAF) as Hc7.
  pose proof (jd_acc_add T1 now fin (p + 1) count acc cur HFIN HAF) as Hadd.
  eapply SRr_bind; [eapply HA; exact HE|].
  intros W1 c1 _ HMID.
  destruct (jobjs_after_step (a3_text T1 now) fin (p + 1) count acc cur HAF)
    as [(Hcm & HFROM) | (_ & Hcb & Hend & Hfin)].
  - rewrite (json_ws_id (a3_text T1 now) (p + 1) HNW ltac:(lia)) in Hcm, HFROM.
    rewrite (json_ws_id (a3_text T1 now) (p + 1 + 1) HNW ltac:(lia)) in HFROM.
    rewrite Hadd in HFROM. replace (p + 1 + 1) with (p + 2) in HFROM by lia.
    eapply SRr_mono; [eapply HB; [exact Hcm | exact HFROM | exact HMID]|].
    intros W2 c2 _ HO. right. exists (p + 2). split; [lia | exact HO].
  - rewrite (json_ws_id (a3_text T1 now) (p + 1) HNW ltac:(lia)) in Hcb, Hend.
    rewrite (json_ws_id (a3_text T1 now) (p + 1 + 1) HNW ltac:(lia)) in Hend.
    rewrite Hadd in Hfin.
    assert (Hr2 : p + 2 = a3_r T1 now) by (unfold a3_r, jlen in *; lia).
    eapply SRr_mono; [eapply HC; [exact Hcb | exact Hr2 | exact Hfin | exact HMID]|].
    intros W2 c2 _ HR. left. exact HR.
Qed.

End h.
End f.
End d.
