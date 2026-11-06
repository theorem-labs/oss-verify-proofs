(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFA4.v; 95 of its 134 lines of code are new or changed and 6 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoRo JtokIs DiscoArm3
DiscoArm3FieldCut DiscoArm3FieldMDA DiscoArm3FieldMDA2 DiscoArm3FieldMDA3
DiscoArm3FieldMDA1P1 DiscoArm3FieldMDA1P2 DiscoArm3FieldMDA1P3 DiscoArm3FieldMDA1P4
DiscoArm3FieldMDA1P5 DiscoArm3FieldMDA1P6 DiscoArm3FieldMDA1P7 DiscoArm3FieldMDA4.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import McConsts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis TJTOK : tjtok_is_spec B.
Hypothesis DBPC : d_body_pcall_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis MCRO : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI ->
  in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis MCUN : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis DCAN : d_can_hyps B tfib_K.

Definition md_a3_stmt (p : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
         (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (mp : Z)
         (W : world SEGS) (c : config),
  md_m4 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c ->
  SRr SEGS W c (md_m6 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p mp).

Lemma md_of_steps : forall p,
  (forall cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c,
     f_md B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c ->
     SRr SEGS W c (md_m2 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p mp)) ->
  (forall cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c,
     md_m2 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c ->
     SRr SEGS W c (md_m4 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p mp)) ->
  md_a3_stmt p ->
  (forall cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c,
     md_m6 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c ->
     SRr SEGS W c (f_mo B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p)) ->
  seg_mda_p_spec B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros p HA1 HA2 HA3 HA4 cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs.
eapply SRr_bind; [exact (HA1 cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs)|].
intros W1 c1 _ H1.
eapply SRr_bind; [exact (HA2 cx h i n now op W0 c0 T0 T1 buf count os vpad mp W1 c1 H1)|].
intros W2 c2 _ H2.
eapply SRr_bind; [exact (HA3 cx h i n now op W0 c0 T0 T1 buf count os vpad mp W2 c2 H2)|].
intros W3 c3 _ H3.
exact (HA4 cx h i n now op W0 c0 T0 T1 buf count os vpad mp W3 c3 H3).
Qed.

Theorem a3f_mda_of_a3 : (forall p, 0 <= p < 8 -> md_a3_stmt p) ->
  forall p, 0 <= p < 8 -> seg_mda_p_spec B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros HA3 p Hp.
assert (Hc : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
destruct Hc as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|Hq]]]]]]]; subst p.
- apply md_of_steps.
  + intros; eapply md_a1_0; eassumption.
  + intros; eapply md_a2_0; eassumption.
  + apply HA3; lia.
  + intros; eapply md_a4; try eassumption; lia.
- apply md_of_steps.
  + intros; eapply md_a1_1; eassumption.
  + intros; eapply md_a2_1; eassumption.
  + apply HA3; lia.
  + intros; eapply md_a4; try eassumption; lia.
- apply md_of_steps.
  + intros; eapply md_a1_2; eassumption.
  + intros; eapply md_a2_2; eassumption.
  + apply HA3; lia.
  + intros; eapply md_a4; try eassumption; lia.
- apply md_of_steps.
  + intros; eapply md_a1_3; eassumption.
  + intros; eapply md_a2_3; eassumption.
  + apply HA3; lia.
  + intros; eapply md_a4; try eassumption; lia.
- apply md_of_steps.
  + intros; eapply md_a1_4; eassumption.
  + intros; eapply md_a2_4; eassumption.
  + apply HA3; lia.
  + intros; eapply md_a4; try eassumption; lia.
- apply md_of_steps.
  + intros; eapply md_a1_5; eassumption.
  + intros; eapply md_a2_5; eassumption.
  + apply HA3; lia.
  + intros; eapply md_a4; try eassumption; lia.
- apply md_of_steps.
  + intros; eapply md_a1_6; eassumption.
  + intros; eapply md_a2_6; eassumption.
  + apply HA3; lia.
  + intros; eapply md_a4; try eassumption; lia.
- apply md_of_steps.
  + intros; eapply md_a1_7; eassumption.
  + intros; eapply md_a2_7; eassumption.
  + apply HA3; lia.
  + intros; eapply md_a4; try eassumption; lia.
Qed.

End h.
End f.
End d.
