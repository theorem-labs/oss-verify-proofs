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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
reac_disco_table_age_c reac_disco_table_json_c disco_json_reader_model slot_ser_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition R10_OFF : Z := 0xb70.
Definition R12_OFF : Z := 0x1d14.
Definition R14_OFF : Z := 0x22a0.
Definition R14X_OFF : Z := 0x22c0.

Definition live_ser (o : dobj) : bool :=
  match o with OO | OOUR | OT | OG | OLOCK => true | _ => false end.
Definition live_ser2 (o : dobj) : bool :=
  match o with OO | OUSED | OOUR | OT | OG | OLOCK => true | _ => false end.
Definition dsh_ser : Z -> Z := dsh live_ser.
Definition dsh_ser2 : Z -> Z := dsh live_ser2.

Definition a3_xb (buf op : Z) : list (Z * Z) := [(buf, Z.max (slot_ser_defs.ser_cap op) 1)].
Definition a3_text (T : list byte) (now : Z) : list Z := reac_disco_table_json_c.tj_text T now.
Definition a3_r (T : list byte) (now : Z) : Z := Z.of_nat (length (a3_text T now)).

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

Definition a3_from (cx : dcx) (h i n now op : Z) (T0 : list byte) (W0 : world SEGS) (c0 : config)
  (W3 : world SEGS) : Prop :=
  arm3_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 /\ wle W0 W3 /\ length T0 = 400%nat /\
  exists (fq : YK11.FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
    c0 = cfg_at (fx := fq) SEGS (BASE + ARM3_OFF) regs mem md /\
    garr8 SEGS (rd W0 mem) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T0).

Definition a3_tab (cx : dcx) (now : Z) (T0 T1 : list byte) (W : world SEGS) (mem : word -> option byte) : Prop :=
  (exists removed : Z,
     reac_disco_table_age_c.age_model T0 now = (T1, removed) /\
     reac_disco_table_age_c.age_post T0 now T1 removed) /\
  garr8 SEGS (rd W mem) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T1).

Definition a3_buf (op : Z) (T1 : list byte) (now buf : Z) (W : world SEGS) (mem : word -> option byte) : Prop :=
  2 <= a3_r T1 now < slot_ser_defs.ser_cap op /\
  garr8 SEGS (rd W mem) buf (a3_text T1 now ++ [0]).

Definition r10_in (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  : world SEGS -> config -> Prop :=
  fun W3 c3 => a3_from cx h i n now op T0 W0 c0 W3 /\
    d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx R10_OFF h i n now (a3_xb buf op) dsh_loop
      (fun regs => getr regs 22 = w64 (a3_r T1 now) /\ getr regs 26 = w64 buf)
      (fun W m => d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m /\ a3_buf op T1 now buf W m) W3 c3.

Definition r12_in (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) : world SEGS -> config -> Prop :=
  fun W3 c3 => a3_from cx h i n now op T0 W0 c0 W3 /\
    d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx R12_OFF h i n now (a3_xb buf op) dsh_ser
      (fun regs => bv_unsigned (getr regs 21) mod 2 ^ 32 = count /\ getr regs 26 = w64 buf)
      (fun W m => d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m /\ a3_buf op T1 now buf W m /\
         disco_json_reader_model.json_read (a3_text T1 now) 9 = Some (count, os) /\ length vpad = 4%nat /\
         garr8 SEGS (rd W m) (d_obj cx OO)
           (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os))) W3 c3.

Definition r14_in (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  : world SEGS -> config -> Prop :=
  fun W3 c3 => a3_from cx h i n now op T0 W0 c0 W3 /\
    d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx R14_OFF h i n now (a3_xb buf op) dsh_ser2
      (fun regs => getr regs 10 = w64 (shadow_addr (d_FB cx)) /\ getr regs 26 = w64 buf)
      (fun W m => d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m) W3 c3.

Definition r14x_in (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  : world SEGS -> config -> Prop :=
  fun W3 c3 => a3_from cx h i n now op T0 W0 c0 W3 /\
    d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx R14X_OFF h i n now (a3_xb buf op) dsh_loop
      (fun regs => getr regs 26 = w64 buf)
      (fun W m => d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m) W3 c3.

Definition a3_age_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W : world SEGS) (c : config),
  arm3_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W c ->
  SRr SEGS W c (fun W' c' => exists (T0 T1 : list byte) (buf : Z),
    r10_in cx h i n now op W c T0 T1 buf W' c' \/ r14x_in cx h i n now op W c T0 T1 buf W' c').

Definition a3_json_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (W : world SEGS) (c : config),
  r10_in cx h i n now op W0 c0 T0 T1 buf W c ->
  SRr SEGS W c (fun W' c' => exists (count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte),
    r12_in cx h i n now op W0 c0 T0 T1 buf count os vpad W' c').

Definition a3_field_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (W : world SEGS) (c : config),
  r12_in cx h i n now op W0 c0 T0 T1 buf count os vpad W c ->
  SRr SEGS W c (r14_in cx h i n now op W0 c0 T0 T1 buf).

Definition a3_tail_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (W : world SEGS) (c : config),
  r14_in cx h i n now op W0 c0 T0 T1 buf W c \/ r14x_in cx h i n now op W0 c0 T0 T1 buf W c ->
  SRr SEGS W c (lat_pre B MT XM_LIB RLO RHI tfib_K cx h i n now).

Lemma arm3_of_parts :
  a3_age_spec -> a3_json_spec -> a3_field_spec -> a3_tail_spec -> arm3_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros HA HJ HF HT cx h i n now op W c H.
  eapply SRr_bind; [exact (HA cx h i n now op W c H)|].
  intros W1 c1 _ H1. destruct H1 as (T0 & T1 & buf & [H1 | H1]).
  - eapply SRr_bind; [eapply HJ; exact H1|].
    intros W2 c2 _ H2. destruct H2 as (count & os & vpad & H2).
    eapply SRr_bind; [eapply HF; exact H2|].
    intros W3 c3 _ H3. eapply HT. left. exact H3.
  - eapply HT. right. exact H1.
Qed.

End h.
End f.
End d.
