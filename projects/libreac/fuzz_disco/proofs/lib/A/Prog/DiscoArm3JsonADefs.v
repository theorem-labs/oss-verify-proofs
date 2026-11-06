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
DiscoEntryInv DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoArm3JsonMs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_age_c slot_ser_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition JA_RET1 : Z := 0xb7c.
Definition JA_RET2 : Z := 0x1048.

Lemma jA_fin : forall (T0 T1 : list byte) now removed,
  reac_disco_table_age_c.age_post T0 now T1 removed -> 0 <= now < 2 ^ 64 ->
  exists fin, jfin_ok T1 now fin.
Proof.
  intros T0 T1 now removed HP Hnow.
  destruct HP as (LT & _ & _ & _ & _ & _ & TOK & _).
  destruct (jtext_facts T1 now LT TOK Hnow) as (os & HJ & Hn & Hws & Hl & Hinb).
  exists (disco_table_c.n_of T1, os). split; [exact HJ|]. split; [exact Hn|].
  split; [exact Hws|]. split; [exact Hl | exact Hinb].
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition jA_c1 (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  : world SEGS -> config -> Prop :=
  jcut B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf JA_RET1 dsh_ser (fun _ => True) (fun _ _ => True).

Definition jA_R (cx : dcx) (regs : bvmap 5 word) : Prop :=
  getr regs 23 = w64 (jcur cx 0) /\ getr regs 24 = w64 1.

Definition jA_X (T1 : list byte) (now : Z) (fin : Z * list jobj) (W : world SEGS) (m : word -> option byte) : Prop :=
  jfin_ok T1 now fin /\ jobjs_from (a3_text T1 now) fin 1 0 [].

Definition jA_S1_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (W : world SEGS) (c : config),
  r10_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W c ->
  SRr SEGS W c (jA_c1 cx h i n now op W0 c0 T0 T1 buf).

Definition jA_S2_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (W : world SEGS) (c : config),
  jA_c1 cx h i n now op W0 c0 T0 T1 buf W c ->
  SRr SEGS W c (fun W' c' => jr12 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W' c' \/
    exists fin : Z * list jobj,
      ms_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf JA_RET2 0 (jA_R cx) (jA_X T1 now fin) W' c').

Definition jA_S3_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (fin : Z * list jobj) (W : world SEGS) (c : config),
  ms_out B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf JA_RET2 0 (jA_R cx) (jA_X T1 now fin) W c ->
  SRr SEGS W c (fun W' c' => exists vpad : list byte,
    jobj_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf fin 1 0 [] vpad W' c').

Lemma jA_R_kept : forall cx rg rg', aregs_preserved rg rg' -> jA_R cx rg -> jA_R cx rg'.
Proof.
  intros cx rg rg' HP (H23 & H24). split.
  - rewrite <- H23. exact (HP 23 ltac:(unfold acallee_saved; lia)).
  - rewrite <- H24. exact (HP 24 ltac:(unfold acallee_saved; lia)).
Qed.

Lemma a3j_A_of_parts : jA_S1_stmt -> jA_S2_stmt -> ms_step_stmt B MT XM_LIB RLO RHI tfib_K -> jA_S3_stmt ->
  jseg_A B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros H1 H2 HM H3 cx h i n now op W0 c0 T0 T1 buf W c H.
  eapply SRr_bind; [exact (H1 _ _ _ _ _ _ _ _ _ _ _ _ _ H)|].
  intros W1 c1 _ HC1.
  eapply SRr_bind; [exact (H2 _ _ _ _ _ _ _ _ _ _ _ _ _ HC1)|].
  intros W2 c2 _ [HR | (fin & HM2)].
  - apply SRr_ret. left. exact HR.
  - eapply SRr_bind.
    + refine (HM _ _ _ _ _ _ _ _ _ _ _ JA_RET2 0 (jA_R cx) (jA_X T1 now fin) W2 c2 _ _ _ _ _ HM2).
      * unfold JA_RET2. lia.
      * reflexivity.
      * lia.
      * exact (jA_R_kept cx).
      * intros W3 m3 W4 m4 HX _. exact HX.
    + intros W3 c3 _ HO.
      eapply SRr_mono; [exact (H3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ HO)|].
      intros W4 c4 _ (vpad & HJ). right. exists fin, 1, vpad. exact HJ.
Qed.

End h.
End f.
End d.
