(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths, module names and numbers changed; 361 of its 413 lines of code are new or changed and 1226 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacBoxNameSeg1.v, with its module paths changed; 159 of its 186 lines of code are new or changed and 386 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntBodyStmt.v, with its module paths and module names changed; 139 of its 172 lines of code are new or changed and 153 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP03 YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbp YC5d YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoArm3JsonJs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition JSC_KEY_RA : Z := 0x1120.
Definition JSC_KEY_OFF : Z := 448.

Lemma jb_slot24_len : forall buf vpad t, length vpad = 4%nat ->
  length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t Hv. unfold slot_ser_defs.slot24. destruct (tv_kind t =? 0).
  - apply repeat_length.
  - rewrite !length_app, Mem.length_le8, Mem.length_le4, Hv. reflexivity.
Qed.

Lemma jb_obj_bytes_len : forall buf vpad o, length vpad = 4%nat -> length o = 6%nat ->
  length (slot_ser_defs.obj_bytes buf vpad o) = 144%nat.
Proof.
  intros buf vpad o Hv Ho. unfold slot_ser_defs.obj_bytes.
  destruct o as [|a [|b [|c [|d [|e [|f [|g o]]]]]]]; try discriminate Ho.
  cbn [map concat]. rewrite !length_app, !(jb_slot24_len buf vpad _ Hv). reflexivity.
Qed.

Lemma jb_objs_bytes_len : forall buf vpad os, length vpad = 4%nat ->
  Forall (fun o : jobj => length o = 6%nat) os ->
  length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os Hv. induction os as [|o os IH]; intros HF; [reflexivity|].
  apply Forall_cons_iff in HF as [Hx Hl]. unfold slot_ser_defs.objs_bytes in *.
  cbn [map concat length]. rewrite length_app, (jb_obj_bytes_len buf vpad o Hv Hx), (IH Hl). lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition jb_R (cx : dcx) (T1 : list byte) (now count : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 19 = w64 (- a3_r T1 now) /\ getr regs 27 = w64 1 /\ getr regs 23 = w64 (jcur cx count).

Definition jb_X (cx : dcx) (T1 : list byte) (now buf : Z) (fin : Z * list jobj) (ii count : Z)
  (acc : list jobj) (vpad : list byte) : world SEGS -> (word -> option byte) -> Prop :=
  fun W m => jfin_ok T1 now fin /\ 0 <= ii /\ 0 <= count /\ length acc = Z.to_nat count /\
    jpairs_from (a3_text T1 now) fin (ii + 1) jobj_empty count acc /\
    jmem cx buf count vpad (acc ++ [jobj_empty]) W m.

Definition jb_call (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (fin : Z * list jobj) (ii count : Z) (acc : list jobj) (vpad : list byte) : world SEGS -> config -> Prop :=
  jsc_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf dsh_scr JSC_KEY_RA (ii + 1) JSC_KEY_OFF
    (jb_R cx T1 now count) (jb_X cx T1 now buf fin ii count acc vpad).

Definition jseg_B1 : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (fin : Z * list jobj) (ii count : Z) (acc : list jobj) (vpad : list byte) (W : world SEGS) (c : config),
  jobj_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W c ->
  SRr SEGS W c (fun W' c' =>
    jb_call cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W' c' \/
    joend_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf fin (ii + 1) jobj_empty count acc vpad W' c').

Definition jseg_B2 : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (fin : Z * list jobj) (ii count : Z) (acc : list jobj) (vpad : list byte)
         (j kk ks kl : Z) (W : world SEGS) (c : config),
  jscalar (a3_text T1 now) (ii + 1) = Some (j, kk, ks, kl) ->
  jsc_out B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf dsh_scr JSC_KEY_RA JSC_KEY_OFF j kk ks kl
    (jb_R cx T1 now count) (jb_X cx T1 now buf fin ii count acc vpad) W c ->
  SRr SEGS W c (jpair_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf fin (ii + 1) j kk ks kl
    jobj_empty count acc vpad).

Lemma jb_empty_in : forall Bx, Forall (slot_ser_tokb.tok_inb Bx) jobj_empty.
Proof.
  intros Bx. unfold jobj_empty. cbn [repeat]. repeat apply Forall_cons; try apply Forall_nil;
  unfold slot_ser_tokb.tok_inb, tok_none, tv_kind; cbn [fst snd]; left; reflexivity.
Qed.

Lemma jb_call_x : forall cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W c,
  jb_call cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W c ->
  exists m, jb_X cx T1 now buf fin ii count acc vpad W m.
Proof. intros. eapply jcut_x. unfold jb_call, jsc_in in H. exact H. Qed.

Lemma jb_keepX : forall cx T1 now buf fin ii count acc vpad W1 m1 W2 m2,
  jb_X cx T1 now buf fin ii count acc vpad W1 m1 ->
  jsc_kept cx JSC_KEY_OFF W1 m1 W2 m2 ->
  jb_X cx T1 now buf fin ii count acc vpad W2 m2.
Proof.
  intros cx T1 now buf fin ii count acc vpad W1 m1 W2 m2 (HF & Hii & Hc & Hal & HP & HM) HK.
  pose proof HK as (GF & GFA & GAS & GS & HKK).
  unfold TJSON_SCALAR_STK, ESTACK in GFA.
  assert (HA0 : 0 <= d_A cx) by lia.
  pose proof (jpairs_from_count (a3_text T1 now) fin (ii + 1) jobj_empty count acc HP) as Hcnt.
  pose proof HF as (_ & Hfin & _).
  destruct HM as (M408 & M368 & Mlen & Mpad & Mobjs & Mall).
  assert (Hlen : length (acc ++ [jobj_empty]) = Z.to_nat (count + 1)).
  { rewrite length_app, Hal. cbn [length]. lia. }
  pose proof (jb_objs_bytes_len buf vpad (acc ++ [jobj_empty]) Mlen Mall) as Hob.
  rewrite Hlen in Hob.
  assert (Hbd : (length (slot_ser_defs.objs_bytes buf vpad (acc ++ [jobj_empty])) <= 1296)%nat) by lia.
  assert (HKb : forall a nb v, 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 ->
    (forall x, a <= x < a + Z.of_nat nb ->
       ~ (d_A cx - TJSON_SCALAR_STK <= x < d_A cx \/ d_A cx + JSC_KEY_OFF <= x < d_A cx + JSC_KEY_OFF + 20)) ->
    val_mem SEGS (rd W1 m1) a nb v -> val_mem SEGS (rd W2 m2) a nb v)
    by (intros a nb v Ha Hb Hd Hv; exact (jsc_val_mem_kept _ W1 m1 W2 m2 a nb v HKK Ha Hb Hd Hv)).
  split; [exact HF|]. split; [exact Hii|]. split; [exact Hc|]. split; [exact Hal|]. split; [exact HP|].
  split; [apply HKb; [lia | cbn; lia | intros x Hx [Hp|Hp]; unfold JSC_KEY_OFF in *; lia | exact M408]|].
  split; [apply HKb; [lia | cbn; lia | intros x Hx [Hp|Hp]; unfold JSC_KEY_OFF in *; lia | exact M368]|].
  split; [exact Mlen|].
  split.
  { eapply (jsc_garr8_kept _ W1 m1 W2 m2); [exact HKK | lia | | | exact Mpad].
    - rewrite length_map, Mlen. lia.
    - intros x Hx [Hp|Hp]; rewrite length_map, Mlen in Hx; unfold JSC_KEY_OFF in *; lia. }
  split; [|exact Mall].
  assert (EOO : d_obj cx OO = d_FB cx + 240) by reflexivity.
  eapply (jsc_garr8_kept _ W1 m1 W2 m2); [exact HKK | rewrite EOO; lia | | | exact Mobjs].
  - rewrite length_map, EOO. lia.
  - intros x Hx [Hp|Hp]; rewrite length_map, EOO in Hx;
    unfold JSC_KEY_OFF, TJSON_SCALAR_STK, ESTACK in *; lia.
Qed.

Lemma jb_keepR : forall cx T1 now count rg rg',
  aregs_preserved rg rg' -> jb_R cx T1 now count rg -> jb_R cx T1 now count rg'.
Proof.
  intros cx T1 now count rg rg' HP (Q19 & Q27 & Q23).
  assert (E19 : getr rg' 19 = getr rg 19) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
  assert (E27 : getr rg' 27 = getr rg 27) by exact (HP 27 ltac:(unfold acallee_saved; lia)).
  assert (E23 : getr rg' 23 = getr rg 23) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
  split; [rewrite E19; exact Q19|]. split; [rewrite E27; exact Q27|].
  rewrite E23; exact Q23.
Qed.

Lemma jseg_B_of_parts : jsc_step_stmt B MT XM_LIB RLO RHI tfib_K -> jseg_B1 -> jseg_B2 ->
  jseg_B B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros HJS H1 H2 cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W c HO.
  eapply SRr_bind; [exact (H1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HO)|].
  intros W1 c1 _ [HC | HE].
  - destruct (jb_call_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as (m & HX).
    pose proof HX as (_ & Hii & _ & _ & HP & _).
    destruct (jpairs_from_step (a3_text T1 now) fin (ii + 1) jobj_empty count acc HP)
      as (j & kk & ks & kl & _ & _ & _ & _ & _ & Hjs & _).
    eapply SRr_bind.
    { refine (HJS cx h i n now op W0 c0 T0 T1 buf dsh_scr JSC_KEY_RA (ii + 1) JSC_KEY_OFF j kk ks kl _ _ W1 c1
        _ _ _ _ _ _ Hjs _ _ HC).
      - unfold JSC_KEY_RA. lia.
      - unfold JSC_KEY_RA. reflexivity.
      - unfold JSC_KEY_OFF. reflexivity.
      - unfold JSC_KEY_OFF. lia.
      - unfold JSC_KEY_OFF. lia.
      - lia.
      - exact (jb_keepR cx T1 now count).
      - exact (jb_keepX cx T1 now buf fin ii count acc vpad). }
    intros W2 c2 _ HR.
    eapply SRr_mono; [exact (H2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HR)|].
    intros W3 c3 _ HPr. left. exists (ii + 1), j, kk, ks, kl. split; [lia | exact HPr].
  - apply SRr_ret. right. exists (ii + 1). split; [lia | exact HE].
Qed.

End h.
End f.
End d.
