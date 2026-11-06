(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module paths and module names changed; 62 of its 92 lines of code are new or changed and 466 lines of the source are left out. *)
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
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition F_OFF : Z := 0x2268.
Definition HS_OFF : Z := 0x2278.
Definition V_OFF : Z := 0x22a4.
Definition C_OFF : Z := 0x22b4.
Definition RL_OFF : Z := 0x22bc.

Definition a3t_shf (k : Z) : bool := ((30 <=? k) && (k <? 192)) || ((208 <=? k) && (k <? 212)).

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

Definition a3t_at (cx : dcx) (pc h i n now : Z) (R : bvmap 5 word -> Prop) : world SEGS -> config -> Prop :=
  d_arm_at B MT XM_LIB RLO RHI tfib_K cx pc h i n now [] dsh_loop R (d_sp1 cx i n now).
Definition a3t_rh (h now : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 21 = w64 h /\ getr regs 22 = w64 1 /\ getr regs 26 = w64 now.
Definition a3t_f (cx : dcx) (h i n now : Z) : world SEGS -> config -> Prop :=
  a3t_at cx F_OFF h i n now (fun _ => True).
Definition a3t_hs (cx : dcx) (h i n now : Z) : world SEGS -> config -> Prop :=
  a3t_at cx HS_OFF h i n now (fun regs => getr regs 26 = w64 now /\ (getr regs 10 = w64 0 \/ getr regs 10 = w64 1)).
Definition a3t_v (cx : dcx) (h i n now : Z) : world SEGS -> config -> Prop :=
  a3t_at cx V_OFF h i n now (fun regs => getr regs 22 = w64 1 /\ getr regs 26 = w64 now /\ getr regs 10 <> w64 0).
Definition a3t_c (cx : dcx) (h i n now : Z) : world SEGS -> config -> Prop :=
  a3t_at cx C_OFF h i n now (a3t_rh h now).
Definition a3t_r (cx : dcx) (h i n now : Z) : world SEGS -> config -> Prop :=
  a3t_at cx RL_OFF h i n now (a3t_rh h now).

Definition a3t_A_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (W : world SEGS) (c : config),
  r14_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W c ->
  SRr SEGS W c (r14x_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf).

Definition a3t_1_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (W : world SEGS) (c : config),
  r14x_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W c ->
  SRr SEGS W c (a3t_f cx h i n now).

Definition a3t_step_spec (P Q : dcx -> Z -> Z -> Z -> Z -> world SEGS -> config -> Prop) : Prop :=
  forall (cx : dcx) (h i n now : Z) (W : world SEGS) (c : config), P cx h i n now W c -> SRr SEGS W c (Q cx h i n now).

Lemma a3_tail_of_parts :
  a3t_A_spec -> a3t_1_spec -> a3t_step_spec a3t_f a3t_hs -> a3t_step_spec a3t_hs a3t_v ->
  a3t_step_spec a3t_v a3t_c -> a3t_step_spec a3t_c a3t_r ->
  a3t_step_spec a3t_r (lat_pre B MT XM_LIB RLO RHI tfib_K) ->
  a3_tail_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros HA H1 H2 H3 H4 H5 H6.
  assert (HX : forall cx h i n now op W0 c0 T0 T1 buf W c,
    r14x_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W c ->
    SRr SEGS W c (lat_pre B MT XM_LIB RLO RHI tfib_K cx h i n now)).
  { intros cx h i n now op W0 c0 T0 T1 buf W c H.
    eapply SRr_bind; [exact (H1 cx h i n now op W0 c0 T0 T1 buf W c H)|]. intros Wa ca _ Ha.
    eapply SRr_bind; [exact (H2 cx h i n now Wa ca Ha)|]. intros Wb cb _ Hb.
    eapply SRr_bind; [exact (H3 cx h i n now Wb cb Hb)|]. intros Wc cc _ Hc.
    eapply SRr_bind; [exact (H4 cx h i n now Wc cc Hc)|]. intros Wd cd _ Hd.
    eapply SRr_bind; [exact (H5 cx h i n now Wd cd Hd)|]. intros We ce _ He.
    exact (H6 cx h i n now We ce He). }
  intros cx h i n now op W0 c0 T0 T1 buf W c [H | H].
  - eapply SRr_bind; [exact (HA cx h i n now op W0 c0 T0 T1 buf W c H)|].
    intros W1 c1 _ H1'. exact (HX cx h i n now op W0 c0 T0 T1 buf W1 c1 H1').
  - exact (HX cx h i n now op W0 c0 T0 T1 buf W c H).
Qed.

End h.
End f.
End d.
