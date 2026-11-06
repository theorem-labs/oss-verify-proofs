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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoArm3.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv disco_table_c reac_disco_table_age_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition P_AGE_RA : Z := 0x9b8.
Definition P_CHK_RA : Z := 0x9c4.
Definition P_MAL_RA : Z := 0xa98.
Definition P_TJ_RA : Z := 0xab8.
Definition P_SL_RA : Z := 0xb1c.

Definition a3_stale (T : list byte) (now : Z) : Z :=
  age_count (fun j => disco_stale T j now) (Z.to_nat (n_of T)).
Definition a3_cap (op : Z) : Z := slot_ser_defs.ser_cap op.
Definition a3_jres (op : Z) (T1 : list byte) (now r : Z) : Prop :=
  (r = -1 /\ (a3_cap op < 3 \/ a3_cap op <= a3_r T1 now)) \/
  (r = a3_r T1 now /\ 3 <= a3_cap op /\ r < a3_cap op).

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

Definition a3_st (cx : dcx) (pc kmax h i n now : Z) (xb : list (Z * Z))
  (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop) : world SEGS -> config -> Prop :=
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax (ACC_HEAD MT i + mo_malloc MT REC_MAX)
    (fun regs ly3 S3 W3 mem3 md3 =>
    0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\
    d_rL B cx regs /\ R regs /\ X W3 mem3 /\ d_sp0 cx i now W3 mem3 /\ d_body B cx h n xb dsh_loop ly3 S3 W3 mem3).

Definition a3_t0 (cx : dcx) (T0 : list byte) (W : world SEGS) (mem : word -> option byte) : Prop :=
  length T0 = 400%nat /\ table_ok T0 /\
  garr8 SEGS (rd W mem) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T0).

Definition a3_age_regs (cx : dcx) (op : Z) (T0 : list byte) (regs : bvmap 5 word) : Prop :=
  getr regs 21 = w64 (s32_at T0 392) /\ getr regs 23 = w64 (n_of T0) /\
  getr regs 24 = w64 (d_obj cx OT) /\ getr regs 26 = w64 STALE_NS /\ getr regs 27 = w64 op.

Definition a3_aged (cx : dcx) (now : Z) (T0 T1 : list byte) (removed : Z) (W : world SEGS) (mem : word -> option byte) : Prop :=
  age_model T0 now = (T1, removed) /\ age_post T0 now T1 removed /\
  garr8 SEGS (rd W mem) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T1).

Definition p_age (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 : list byte)
  : world SEGS -> config -> Prop :=
  fun W c => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W /\
    a3_st cx AF_reac_disco_table_age (EV_HEAD i) h i n now []
      (fun regs => getr regs 1 = w64 (BASE + P_AGE_RA) /\ getr regs 10 = w64 (d_obj cx OT) /\
         getr regs 11 = w64 now /\ getr regs 22 = w64 (a3_stale T0 now) /\ a3_age_regs cx op T0 regs)
      (fun W m => d_sp1 cx i n now W m /\ a3_t0 cx T0 W m) W c.

Definition q_age (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (removed : Z)
  : world SEGS -> config -> Prop :=
  fun W c => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W /\
    a3_st cx P_AGE_RA (EV_HEAD i) h i n now []
      (fun regs => getr regs 10 = w64 removed /\ getr regs 22 = w64 removed /\ a3_age_regs cx op T0 regs)
      (fun W m => d_sp1 cx i n now W m /\ a3_aged cx now T0 T1 removed W m) W c.

Definition p_chk (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (removed : Z)
  : world SEGS -> config -> Prop :=
  fun W c => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W /\
    a3_st cx AF_check_table (EV_HEAD i) h i n now []
      (fun regs => getr regs 1 = w64 (BASE + P_CHK_RA) /\ getr regs 10 = w64 (d_obj cx OT) /\
         getr regs 19 = w64 removed /\ getr regs 22 = w64 removed /\ a3_age_regs cx op T0 regs)
      (fun W m => d_sp1 cx i n now W m /\ a3_aged cx now T0 T1 removed W m) W c.

Definition q_chk (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (removed : Z)
  : world SEGS -> config -> Prop :=
  fun W c => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W /\
    a3_st cx P_CHK_RA (EV_HEAD i) h i n now []
      (fun regs => getr regs 19 = w64 removed /\ getr regs 22 = w64 removed /\ a3_age_regs cx op T0 regs)
      (fun W m => d_sp1 cx i n now W m /\ a3_aged cx now T0 T1 removed W m) W c.

Definition p_mal (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  : world SEGS -> config -> Prop :=
  fun W c => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W /\
    a3_st cx (SIGMA DS___interceptor_trampoline_malloc - BASE) (EV_HEAD i) h i n now []
      (fun regs => getr regs 1 = w64 (BASE + P_MAL_RA) /\ getr regs 10 = w64 (a3_cap op) /\
         getr regs 19 = w64 (a3_cap op))
      (fun W m => d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m) W c.

Definition q_mal (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  : world SEGS -> config -> Prop :=
  fun W c => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W /\
    a3_st cx P_MAL_RA (EV_HEAD i + 1) h i n now (a3_xb buf op)
      (fun regs => getr regs 10 = w64 buf /\ getr regs 19 = w64 (a3_cap op))
      (fun W m => 4096 <= buf /\ d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m) W c.

Definition p_tj (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  : world SEGS -> config -> Prop :=
  fun W c => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W /\
    a3_st cx AF_reac_disco_table_json (EV_HEAD i + 1) h i n now (a3_xb buf op)
      (fun regs => getr regs 1 = w64 (BASE + P_TJ_RA) /\ getr regs 10 = w64 (d_obj cx OT) /\
         getr regs 11 = w64 now /\ getr regs 12 = w64 buf /\ getr regs 13 = w64 (a3_cap op) /\
         getr regs 19 = w64 (a3_cap op) /\ getr regs 26 = w64 buf)
      (fun W m => 4096 <= buf /\ d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m) W c.

Definition q_tj (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf r : Z)
  : world SEGS -> config -> Prop :=
  fun W c => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W /\
    a3_st cx P_TJ_RA (EV_HEAD i + 1) h i n now (a3_xb buf op)
      (fun regs => getr regs 10 = w64 r /\ getr regs 19 = w64 (a3_cap op) /\ getr regs 26 = w64 buf)
      (fun W m => 4096 <= buf /\ d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m /\ a3_jres op T1 now r /\
         (r = a3_r T1 now -> garr8 SEGS (rd W m) buf (a3_text T1 now ++ [0]))) W c.

Definition p_sl (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  : world SEGS -> config -> Prop :=
  fun W c => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W /\
    a3_st cx (SIGMA DS___interceptor_trampoline_strlen - BASE) (EV_HEAD i + 1) h i n now (a3_xb buf op)
      (fun regs => getr regs 1 = w64 (BASE + P_SL_RA) /\ getr regs 10 = w64 buf /\
         getr regs 19 = w64 (buf + a3_r T1 now) /\ getr regs 22 = w64 (a3_r T1 now) /\ getr regs 26 = w64 buf)
      (fun W m => 4096 <= buf /\ d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m /\ a3_buf op T1 now buf W m) W c.

Definition q_sl (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  : world SEGS -> config -> Prop :=
  fun W c => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W /\
    a3_st cx P_SL_RA (EV_HEAD i + 1) h i n now (a3_xb buf op)
      (fun regs => getr regs 10 = w64 (a3_r T1 now) /\
         getr regs 19 = w64 (buf + a3_r T1 now) /\ getr regs 22 = w64 (a3_r T1 now) /\ getr regs 26 = w64 buf)
      (fun W m => 4096 <= buf /\ d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m /\ a3_buf op T1 now buf W m) W c.

Definition a3_post (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) : world SEGS -> config -> Prop :=
  fun W' c' => exists (T0 T1 : list byte) (buf : Z),
    r10_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W' c' \/
    r14x_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W' c'.

Definition e_ent_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W : world SEGS) (c : config),
  arm3_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W c ->
  SRr SEGS W c (fun W' c' => exists T0, p_age cx h i n now op W c T0 W' c').
Definition c_age_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 : list byte) (W : world SEGS) (c : config),
  p_age cx h i n now op W0 c0 T0 W c ->
  SRr SEGS W c (fun W' c' => exists T1 removed, q_age cx h i n now op W0 c0 T0 T1 removed W' c').
Definition e_chk_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (removed : Z)
    (W : world SEGS) (c : config),
  q_age cx h i n now op W0 c0 T0 T1 removed W c ->
  SRr SEGS W c (p_chk cx h i n now op W0 c0 T0 T1 removed).
Definition c_chk_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (removed : Z)
    (W : world SEGS) (c : config),
  p_chk cx h i n now op W0 c0 T0 T1 removed W c ->
  SRr SEGS W c (q_chk cx h i n now op W0 c0 T0 T1 removed).
Definition e_left_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (removed : Z)
    (W : world SEGS) (c : config),
  q_chk cx h i n now op W0 c0 T0 T1 removed W c ->
  SRr SEGS W c (p_mal cx h i n now op W0 c0 T0 T1).
Definition c_mal_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (W : world SEGS) (c : config),
  p_mal cx h i n now op W0 c0 T0 T1 W c ->
  SRr SEGS W c (fun W' c' => exists buf, q_mal cx h i n now op W0 c0 T0 T1 buf W' c').
Definition e_tj_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
    (W : world SEGS) (c : config),
  q_mal cx h i n now op W0 c0 T0 T1 buf W c ->
  SRr SEGS W c (p_tj cx h i n now op W0 c0 T0 T1 buf).
Definition c_tj_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
    (W : world SEGS) (c : config),
  p_tj cx h i n now op W0 c0 T0 T1 buf W c ->
  SRr SEGS W c (fun W' c' => exists r, q_tj cx h i n now op W0 c0 T0 T1 buf r W' c').
Definition e_res_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf r : Z)
    (W : world SEGS) (c : config),
  q_tj cx h i n now op W0 c0 T0 T1 buf r W c ->
  SRr SEGS W c (fun W' c' => p_sl cx h i n now op W0 c0 T0 T1 buf W' c' \/
    r14x_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W' c').
Definition c_sl_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
    (W : world SEGS) (c : config),
  p_sl cx h i n now op W0 c0 T0 T1 buf W c ->
  SRr SEGS W c (q_sl cx h i n now op W0 c0 T0 T1 buf).
Definition e_brk_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
    (W : world SEGS) (c : config),
  q_sl cx h i n now op W0 c0 T0 T1 buf W c ->
  SRr SEGS W c (r10_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf).

Lemma a3_age_of_parts :
  e_ent_spec -> c_age_spec -> e_chk_spec -> c_chk_spec -> e_left_spec -> c_mal_spec -> e_tj_spec -> c_tj_spec ->
  e_res_spec -> c_sl_spec -> e_brk_spec -> a3_age_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros HE0 HCA HE1 HCC HE2 HCM HE3 HCT HE4 HCS HE5 cx h i n now op W c H.
  eapply SRr_bind; [exact (HE0 cx h i n now op W c H)|]. intros W1 c1 _ (T0 & H1).
  eapply SRr_bind; [exact (HCA _ _ _ _ _ _ _ _ _ _ _ H1)|]. intros W2 c2 _ (T1 & removed & H2).
  eapply SRr_bind; [exact (HE1 _ _ _ _ _ _ _ _ _ _ _ _ _ H2)|]. intros W3 c3 _ H3.
  eapply SRr_bind; [exact (HCC _ _ _ _ _ _ _ _ _ _ _ _ _ H3)|]. intros W4 c4 _ H4.
  eapply SRr_bind; [exact (HE2 _ _ _ _ _ _ _ _ _ _ _ _ _ H4)|]. intros W5 c5 _ H5.
  eapply SRr_bind; [exact (HCM _ _ _ _ _ _ _ _ _ _ _ _ H5)|]. intros W6 c6 _ (buf & H6).
  eapply SRr_bind; [exact (HE3 _ _ _ _ _ _ _ _ _ _ _ _ _ H6)|]. intros W7 c7 _ H7.
  eapply SRr_bind; [exact (HCT _ _ _ _ _ _ _ _ _ _ _ _ _ H7)|]. intros W8 c8 _ (r & H8).
  eapply SRr_bind; [exact (HE4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H8)|]. intros W9 c9 _ [H9 | H9].
  - eapply SRr_bind; [exact (HCS _ _ _ _ _ _ _ _ _ _ _ _ _ H9)|]. intros W10 c10 _ H10.
    eapply SRr_mono; [exact (HE5 _ _ _ _ _ _ _ _ _ _ _ _ _ H10)|].
    intros W' c' _ HR. exists T0, T1, buf. left. exact HR.
  - apply SRr_ret. exists T0, T1, buf. right. exact H9.
Qed.

End h.
End f.
End d.
