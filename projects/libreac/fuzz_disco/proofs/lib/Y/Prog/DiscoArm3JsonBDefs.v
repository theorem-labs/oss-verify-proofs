(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of kind_of_link1 on fuzz_grant.asan, written for libreac/fuzz_grant: the entry seat, the walk loop and the return are adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v and proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v; the contract and the branch lemmas are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/KindOfLink1.v, with its module paths and module names changed; 58 of its 174 lines of code are new or changed and 53 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/KindOfLink1.v, with its module paths and module names changed; 160 of its 184 lines of code are new or changed and 150 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntBodyStmt.v, with its module paths and module names changed; 141 of its 171 lines of code are new or changed and 154 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0d YP0c YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntBodyStmt DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoArm3JsonJs DiscoArm3JsonK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition JSC_KEY_RA : Z := 0x129c.
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

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition jb_R (cx : dcx) (count : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 22 = w64 count /\ getr regs 23 = w64 (jcur cx count).

Definition jb_X (cx : dcx) (T1 : list byte) (now buf : Z) (fin : Z * list jobj) (ii count : Z)
  (acc : list jobj) (vpad : list byte) : world SEGS -> (word -> option byte) -> Prop :=
  fun W m => jfin_ok T1 now fin /\ 0 <= ii /\ 0 <= count /\ length acc = Z.to_nat count /\
    jpairs_from (a3_text T1 now) fin (ii + 1) jobj_empty count acc /\
    jmem cx buf count vpad (acc ++ [jobj_empty]) W m /\
    val_mem SEGS (rd W m) (d_A cx + 352) 8 count.

Definition jb_call (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (fin : Z * list jobj) (ii count : Z) (acc : list jobj) (vpad : list byte) : world SEGS -> config -> Prop :=
  jsc_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf dsh_scr JSC_KEY_RA (ii + 1) JSC_KEY_OFF
    (jb_R cx count) (jb_X cx T1 now buf fin ii count acc vpad).

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
    (jb_R cx count) (jb_X cx T1 now buf fin ii count acc vpad) W c ->
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
  intros cx T1 now buf fin ii count acc vpad W1 m1 W2 m2 (HF & Hii & Hc & Hal & HP & HM & M352) HK.
  pose proof HK as (GF & GFA & GAS & GS & HKK).
  unfold TJSON_SCALAR_STK, ESTACK in GFA.
  assert (HA0 : 0 <= d_A cx) by lia.
  pose proof (jpairs_from_count (a3_text T1 now) fin (ii + 1) jobj_empty count acc HP) as Hcnt.
  pose proof HF as (_ & Hfin & _).
  destruct HM as (Mlen & Mpad & Mobjs & Mall).
  assert (Hlen : length (acc ++ [jobj_empty]) = Z.to_nat (count + 1)).
  { rewrite length_app, Hal. cbn [length]. lia. }
  pose proof (jb_objs_bytes_len buf vpad (acc ++ [jobj_empty]) Mlen Mall) as Hob.
  rewrite Hlen in Hob.
  assert (Hbd : (length (slot_ser_defs.objs_bytes buf vpad (acc ++ [jobj_empty])) <= 1296)%nat) by lia.
  assert (HKb : forall a nb v, 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 ->
    (forall x, a <= x < a + Z.of_nat nb ->
       ~ (d_A cx - TJSON_SCALAR_STK <= x < d_A cx \/ d_A cx + JSC_KEY_OFF <= x < d_A cx + JSC_KEY_OFF + 20)) ->
    val_mem SEGS (rd W1 m1) a nb v -> val_mem SEGS (rd W2 m2) a nb v)
    by (intros a nb v Ha Hb Hd Hv; exact (jk_val_mem_kept _ W1 m1 W2 m2 a nb v HKK Ha Hb Hd Hv)).
  split; [exact HF|]. split; [exact Hii|]. split; [exact Hc|]. split; [exact Hal|]. split; [exact HP|].
  split.
  { split; [exact Mlen|].
    split.
    { eapply (jk_garr8_kept _ W1 m1 W2 m2); [exact HKK | lia | | | exact Mpad].
      - rewrite length_map, Mlen. lia.
      - intros x Hx [Hp|Hp]; rewrite length_map, Mlen in Hx; unfold JSC_KEY_OFF in *; lia. }
    split; [|exact Mall].
    assert (EOO : d_obj cx OO = d_FB cx + 240) by reflexivity.
    eapply (jk_garr8_kept _ W1 m1 W2 m2); [exact HKK | rewrite EOO; lia | | | exact Mobjs].
    - rewrite length_map, EOO. lia.
    - intros x Hx [Hp|Hp]; rewrite length_map, EOO in Hx;
      unfold JSC_KEY_OFF, TJSON_SCALAR_STK, ESTACK in *; lia. }
  apply HKb; [lia | cbn; lia | intros x Hx [Hp|Hp]; unfold JSC_KEY_OFF in *; lia | exact M352].
Qed.

Lemma jb_keepR : forall cx count rg rg',
  aregs_preserved rg rg' -> jb_R cx count rg -> jb_R cx count rg'.
Proof.
  intros cx count rg rg' HP (Q22 & Q23).
  assert (E22 : getr rg' 22 = getr rg 22) by exact (HP 22 ltac:(unfold acallee_saved; lia)).
  assert (E23 : getr rg' 23 = getr rg 23) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
  split; [rewrite E22; exact Q22 | rewrite E23; exact Q23].
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
      - exact (jb_keepR cx count).
      - exact (jb_keepX cx T1 now buf fin ii count acc vpad). }
    intros W2 c2 _ HR.
    eapply SRr_mono; [exact (H2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hjs HR)|].
    intros W3 c3 _ HPr. left. exists (ii + 1), j, kk, ks, kl. split; [lia | exact HPr].
  - apply SRr_ret. right. exists (ii + 1). split; [lia | exact HE].
Qed.

End h.
End f.
End d.
