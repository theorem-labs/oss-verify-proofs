(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module paths and module names changed; 62 of its 92 lines of code are new or changed and 466 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3TailDefs.v, with its module paths and module names changed; 230 of its 271 lines of code are new or changed and 51 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0d YP0c YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv DiscoArm3 DiscoArm3JsonModel.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition OBJ_OFF : Z := 0x11dc.
Definition PAIR_OFF : Z := 0x12d0.
Definition OEND_OFF : Z := 0x15f4.
Definition VAL_OFF : Z := 0x13bc.
Definition SLOT_OFF : Z := 0x1528.

Definition live_scr (o : dobj) : bool :=
  match o with OCUR | OO | OOUR | OT | OG | OLOCK => true | _ => false end.
Definition dsh_scr : Z -> Z := dsh live_scr.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition jcut (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (pc : Z) (shf : Z -> Z) (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop)
  : world SEGS -> config -> Prop :=
  fun W3 c3 => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W3 /\
    d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx pc h i n now (a3_xb buf op) shf
      (fun regs => getr regs 26 = w64 (a3_r T1 now) /\ getr regs 24 = w64 buf /\
         getr regs 25 = w64 (Z.lnot buf) /\ R regs)
      (fun W m => d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m /\ a3_buf op T1 now buf W m /\ X W m) W3 c3.

Definition jcur (cx : dcx) (count : Z) : Z := d_obj cx OO + 144 * count.

Definition jmem (cx : dcx) (buf count : Z) (vpad : list byte) (objs : list jobj)
  (W : world SEGS) (m : word -> option byte) : Prop :=
  length vpad = 4%nat /\ garr8 SEGS (rd W m) (d_A cx + 444) (map (fun b : byte => bv_unsigned b) vpad) /\
  garr8 SEGS (rd W m) (d_obj cx OO) (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad objs)) /\
  Forall (fun o : jobj => length o = 6%nat) objs.

Definition jslots (cx : dcx) (count : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  val_mem SEGS (rd W m) (d_A cx + 408) 8 (jcur cx count + 24) /\
  val_mem SEGS (rd W m) (d_A cx + 368) 8 (jcur cx count + 48) /\
  val_mem SEGS (rd W m) (d_A cx + 360) 8 (jcur cx count + 72) /\
  val_mem SEGS (rd W m) (d_A cx + 328) 8 (jcur cx count + 96) /\
  val_mem SEGS (rd W m) (d_A cx + 296) 8 (jcur cx count + 120) /\
  val_mem SEGS (rd W m) (d_A cx + 352) 8 count.

Definition jfin_ok (T1 : list byte) (now : Z) (fin : Z * list jobj) : Prop :=
  json_read (a3_text T1 now) 9 = Some fin /\ 0 <= fst fin <= 8 /\ jno_ws (a3_text T1 now) /\
  (length (a3_text T1 now) <= 969)%nat /\ Forall (Forall (slot_ser_tokb.tok_inb (a3_text T1 now))) (snd fin).

Definition jobj_in (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (fin : Z * list jobj) (ii count : Z) (acc : list jobj) (vpad : list byte) : world SEGS -> config -> Prop :=
  jcut cx h i n now op W0 c0 T0 T1 buf OBJ_OFF dsh_scr
    (fun regs => getr regs 21 = w64 ii /\ getr regs 22 = w64 count /\ getr regs 23 = w64 (jcur cx count))
    (fun W m => jfin_ok T1 now fin /\ 0 <= ii /\ 0 <= count /\ length acc = Z.to_nat count /\
       jobjs_from (a3_text T1 now) fin ii count acc /\ jmem cx buf count vpad (acc ++ [jobj_empty]) W m).

Definition jpair_in (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (fin : Z * list jobj) (ip j kk ks kl : Z) (cur : jobj) (count : Z) (acc : list jobj) (vpad : list byte)
  : world SEGS -> config -> Prop :=
  jcut cx h i n now op W0 c0 T0 T1 buf PAIR_OFF dsh_scr
    (fun regs => getr regs 10 = w64 j /\
       getr regs 22 = w64 (jcur cx count mod 8) /\ getr regs 23 = w64 (jcur cx count))
    (fun W m => jfin_ok T1 now fin /\ 0 <= ip /\ 0 <= count /\ length acc = Z.to_nat count /\
       jscalar (a3_text T1 now) ip = Some (j, kk, ks, kl) /\ jpairs_from (a3_text T1 now) fin ip cur count acc /\
       length cur = 6%nat /\ Forall (slot_ser_tokb.tok_inb (a3_text T1 now)) cur /\
       jmem cx buf count vpad (acc ++ [cur]) W m /\ jslots cx count W m /\
       val_mem SEGS (rd W m) (d_A cx + 448) 8 (buf + ks) /\ val_mem SEGS (rd W m) (d_A cx + 456) 8 kl /\
       val_mem SEGS (rd W m) (d_A cx + 464) 4 kk).

Definition joend_in (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (fin : Z * list jobj) (p : Z) (cur : jobj) (count : Z) (acc : list jobj) (vpad : list byte)
  : world SEGS -> config -> Prop :=
  jcut cx h i n now op W0 c0 T0 T1 buf OEND_OFF dsh_scr
    (fun regs => getr regs 21 = w64 p /\ getr regs 22 = w64 count)
    (fun W m => jfin_ok T1 now fin /\ 0 <= p /\ 0 <= count /\ length acc = Z.to_nat count /\
       at_byte (a3_text T1 now) p 125 = true /\ jobjs_after (a3_text T1 now) fin (p + 1) count acc cur /\
       length cur = 6%nat /\ Forall (slot_ser_tokb.tok_inb (a3_text T1 now)) cur /\
       jmem cx buf count vpad (acc ++ [cur]) W m).

Definition jval_in (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (fin : Z * list jobj) (ip j2 kk ks kl vk vs vl : Z) (cur c : jobj) (count : Z) (acc : list jobj)
  (vpad : list byte) : world SEGS -> config -> Prop :=
  jcut cx h i n now op W0 c0 T0 T1 buf VAL_OFF dsh_scr
    (fun regs => getr regs 10 = w64 j2 /\
       getr regs 22 = w64 (jcur cx count mod 8) /\ getr regs 23 = w64 (jcur cx count))
    (fun W m => jfin_ok T1 now fin /\ 0 <= ip < j2 /\ 0 <= count /\ length acc = Z.to_nat count /\
       kk = 1 /\ 1 <= vk <= 3 /\
       jslot_upd (a3_text T1 now) (kk, ks, kl) (vk, vs, vl) cur = Some c /\
       jpairs_cont (a3_text T1 now) fin (json_ws (a3_text T1 now) j2) c count acc /\
       length cur = 6%nat /\ Forall (slot_ser_tokb.tok_inb (a3_text T1 now)) cur /\
       slot_ser_tokb.tok_inb (a3_text T1 now) (kk, ks, kl) /\ slot_ser_tokb.tok_inb (a3_text T1 now) (vk, vs, vl) /\
       jmem cx buf count vpad (acc ++ [cur]) W m /\ jslots cx count W m /\
       val_mem SEGS (rd W m) (d_A cx + 448) 8 (buf + ks) /\ val_mem SEGS (rd W m) (d_A cx + 456) 8 kl /\
       val_mem SEGS (rd W m) (d_A cx + 464) 4 kk /\
       val_mem SEGS (rd W m) (d_A cx + 424) 8 (buf + vs) /\ val_mem SEGS (rd W m) (d_A cx + 432) 8 vl /\
       val_mem SEGS (rd W m) (d_A cx + 440) 4 vk).

Definition jslot_in (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (fin : Z * list jobj) (ip t : Z) (c : jobj) (count : Z) (acc : list jobj) (vpad : list byte)
  : world SEGS -> config -> Prop :=
  jcut cx h i n now op W0 c0 T0 T1 buf SLOT_OFF dsh_scr
    (fun regs => getr regs 21 = w64 t /\
       getr regs 22 = w64 (jcur cx count mod 8) /\ getr regs 23 = w64 (jcur cx count))
    (fun W m => jfin_ok T1 now fin /\ 0 <= ip < t /\ 0 <= count /\ length acc = Z.to_nat count /\
       jpairs_cont (a3_text T1 now) fin t c count acc /\
       length c = 6%nat /\ Forall (slot_ser_tokb.tok_inb (a3_text T1 now)) c /\
       jmem cx buf count vpad (acc ++ [c]) W m /\ jslots cx count W m).

Definition jr12 (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  : world SEGS -> config -> Prop :=
  fun W' c' => exists (count : Z) (os : list jobj) (vpad : list byte),
    r12_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad W' c'.

Definition jseg_A : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (W : world SEGS) (c : config),
  r10_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W c ->
  SRr SEGS W c (fun W' c' => jr12 cx h i n now op W0 c0 T0 T1 buf W' c' \/
    exists (fin : Z * list jobj) (ii : Z) (vpad : list byte),
      jobj_in cx h i n now op W0 c0 T0 T1 buf fin ii 0 [] vpad W' c').

Definition jseg_B : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (fin : Z * list jobj) (ii count : Z) (acc : list jobj) (vpad : list byte) (W : world SEGS) (c : config),
  jobj_in cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W c ->
  SRr SEGS W c (fun W' c' =>
    (exists ip j kk ks kl, ii < ip /\
       jpair_in cx h i n now op W0 c0 T0 T1 buf fin ip j kk ks kl jobj_empty count acc vpad W' c') \/
    (exists p, ii < p /\ joend_in cx h i n now op W0 c0 T0 T1 buf fin p jobj_empty count acc vpad W' c')).

Definition jseg_C : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (fin : Z * list jobj) (ip j kk ks kl : Z) (cur : jobj) (count : Z) (acc : list jobj) (vpad : list byte)
         (W : world SEGS) (c : config),
  jpair_in cx h i n now op W0 c0 T0 T1 buf fin ip j kk ks kl cur count acc vpad W c ->
  SRr SEGS W c (fun W' c' =>
    (exists ip' j' kk' ks' kl' cur', ip < ip' /\
       jpair_in cx h i n now op W0 c0 T0 T1 buf fin ip' j' kk' ks' kl' cur' count acc vpad W' c') \/
    (exists p cur', ip < p /\ joend_in cx h i n now op W0 c0 T0 T1 buf fin p cur' count acc vpad W' c')).

Definition jseg_C1 : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (fin : Z * list jobj) (ip j kk ks kl : Z) (cur : jobj) (count : Z) (acc : list jobj) (vpad : list byte)
         (W : world SEGS) (c : config),
  jpair_in cx h i n now op W0 c0 T0 T1 buf fin ip j kk ks kl cur count acc vpad W c ->
  SRr SEGS W c (fun W' c' => exists j2 vk vs vl c2,
    jval_in cx h i n now op W0 c0 T0 T1 buf fin ip j2 kk ks kl vk vs vl cur c2 count acc vpad W' c').

Definition jseg_C2 : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (fin : Z * list jobj) (ip j2 kk ks kl vk vs vl : Z) (cur c2 : jobj) (count : Z) (acc : list jobj)
         (vpad : list byte) (W : world SEGS) (c : config),
  jval_in cx h i n now op W0 c0 T0 T1 buf fin ip j2 kk ks kl vk vs vl cur c2 count acc vpad W c ->
  SRr SEGS W c (fun W' c' => exists t, jslot_in cx h i n now op W0 c0 T0 T1 buf fin ip t c2 count acc vpad W' c').

Definition jseg_C3 : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (fin : Z * list jobj) (ip t : Z) (c2 : jobj) (count : Z) (acc : list jobj) (vpad : list byte)
         (W : world SEGS) (c : config),
  jslot_in cx h i n now op W0 c0 T0 T1 buf fin ip t c2 count acc vpad W c ->
  SRr SEGS W c (fun W' c' =>
    (exists ip' j' kk' ks' kl', ip < ip' /\
       jpair_in cx h i n now op W0 c0 T0 T1 buf fin ip' j' kk' ks' kl' c2 count acc vpad W' c') \/
    (exists p, ip < p /\ joend_in cx h i n now op W0 c0 T0 T1 buf fin p c2 count acc vpad W' c')).

Lemma jseg_C_of_parts : jseg_C1 -> jseg_C2 -> jseg_C3 -> jseg_C.
Proof.
  intros H1 H2 H3 cx h i n now op W0 c0 T0 T1 buf fin ip j kk ks kl cur count acc vpad W c HP.
  eapply SRr_bind; [exact (H1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP)|].
  intros W1 c1 _ (j2 & vk & vs & vl & c2 & HV).
  eapply SRr_bind; [exact (H2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HV)|].
  intros W2 c2' _ (t & HS).
  eapply SRr_mono; [exact (H3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS)|].
  intros W3 c3 _ [(ip' & j' & kk' & ks' & kl' & Hlt & HP') | (p & Hlt & HE)].
  - left. exists ip', j', kk', ks', kl', c2. split; [exact Hlt | exact HP'].
  - right. exists p, c2. split; [exact Hlt | exact HE].
Qed.

Definition jseg_D : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
         (fin : Z * list jobj) (p : Z) (cur : jobj) (count : Z) (acc : list jobj) (vpad : list byte)
         (W : world SEGS) (c : config),
  joend_in cx h i n now op W0 c0 T0 T1 buf fin p cur count acc vpad W c ->
  SRr SEGS W c (fun W' c' => jr12 cx h i n now op W0 c0 T0 T1 buf W' c' \/
    exists ii, p < ii /\ jobj_in cx h i n now op W0 c0 T0 T1 buf fin ii (count + 1) (acc ++ [cur]) vpad W' c').

Lemma jcut_x : forall cx h i n now op W0 c0 T0 T1 buf pc shf R X W c,
  jcut cx h i n now op W0 c0 T0 T1 buf pc shf R X W c -> exists m, X W m.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf pc shf R X W c (_ & H).
  destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & _ & _ & _ & _ & _ & _ & _ & _ & _ & P).
  destruct P as (_ & _ & _ & _ & _ & (_ & _ & _ & HX) & _). exists mem3. exact HX.
Qed.

Lemma jpair_lt : forall cx h i n now op W0 c0 T0 T1 buf fin ip j kk ks kl cur count acc vpad W c,
  jpair_in cx h i n now op W0 c0 T0 T1 buf fin ip j kk ks kl cur count acc vpad W c -> 0 <= ip < a3_r T1 now.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf fin ip j kk ks kl cur count acc vpad W c H.
  destruct (jcut_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (m & _ & Hip & _ & _ & HJ & _).
  pose proof (jscalar_in (a3_text T1 now) ip j kk ks kl HJ). unfold a3_r. unfold jlen in *. lia.
Qed.

Lemma jobj_lt : forall cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W c,
  jobj_in cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W c -> 0 <= ii < a3_r T1 now.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W c H.
  destruct (jcut_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (m & _ & Hii & _ & _ & HO & _).
  pose proof (jobjs_from_lt (a3_text T1 now) fin ii count acc HO). unfold a3_r. unfold jlen in *. lia.
Qed.

Lemma jpair_loop : jseg_C ->
  forall cx h i n now op W0 c0 T0 T1 buf fin count acc vpad lb ip j kk ks kl cur W c,
  lb < ip -> jpair_in cx h i n now op W0 c0 T0 T1 buf fin ip j kk ks kl cur count acc vpad W c ->
  SRr SEGS W c (fun W' c' => exists p cur', lb < p /\
    joend_in cx h i n now op W0 c0 T0 T1 buf fin p cur' count acc vpad W' c').
Proof.
  intros HC cx h i n now op W0 c0 T0 T1 buf fin count acc vpad lb ip j kk ks kl cur W c Hlb HP.
  set (X := (Z * Z * Z * Z * Z * jobj)%type).
  set (P := fun (x : X) W c => let '(ip, j, kk, ks, kl, cur) := x in
              lb < ip /\ jpair_in cx h i n now op W0 c0 T0 T1 buf fin ip j kk ks kl cur count acc vpad W c).
  set (m := fun (x : X) => let '(ip, _, _, _, _, _) := x in a3_r T1 now - ip).
  apply (SRr_loopZ SEGS X m P _ ) with (x := (ip, j, kk, ks, kl, cur)); [|subst P; cbv beta iota; split; assumption].
  intros [[[[[ip0 j0] kk0] ks0] kl0] cur0] W1 c1 [Hlb0 HP0].
  pose proof (jpair_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP0) as Hr0.
  eapply SRr_mono; [exact (HC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP0)|].
  intros W2 c2 _ [(ip' & j' & kk' & ks' & kl' & cur' & Hlt & HP') | (p & cur' & Hlt & HO')].
  - right. exists (ip', j', kk', ks', kl', cur').
    pose proof (jpair_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP') as Hr'.
    subst m P. cbv beta iota. split; [lia|]. split; [lia | exact HP'].
  - left. exists p, cur'. split; [lia | exact HO'].
Qed.

Lemma jobj_loop : jseg_B -> jseg_C -> jseg_D ->
  forall cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W c,
  jobj_in cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W c ->
  SRr SEGS W c (jr12 cx h i n now op W0 c0 T0 T1 buf).
Proof.
  intros HB HC HD cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W c HO.
  set (X := (Z * Z * list jobj)%type).
  set (P := fun (x : X) W c => let '(ii, count, acc) := x in
              jobj_in cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W c).
  set (m := fun (x : X) => let '(ii, _, _) := x in a3_r T1 now - ii).
  apply (SRr_loopZ SEGS X m P _) with (x := (ii, count, acc)); [|exact HO].
  intros [[ii0 count0] acc0] W1 c1 HO0. cbv beta iota in HO0.
  pose proof (jobj_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HO0) as Hr0.
  eapply SRr_bind; [exact (HB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HO0)|].
  intros W2 c2 _ H2.
  assert (H3 : SRr SEGS W2 c2 (fun W' c' => exists p cur', ii0 < p /\
                 joend_in cx h i n now op W0 c0 T0 T1 buf fin p cur' count0 acc0 vpad W' c')).
  { destruct H2 as [(ip & j & kk & ks & kl & Hlt & HP) | (p & Hlt & HE)].
    - exact (jpair_loop HC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hlt HP).
    - apply SRr_ret. exists p, jobj_empty. split; [exact Hlt | exact HE]. }
  eapply SRr_bind; [exact H3|]. intros W3 c3 _ (p & cur & Hlt & HE).
  eapply SRr_mono; [exact (HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE)|].
  intros W4 c4 _ [HR | (ii' & Hlt' & HO')].
  - left. exact HR.
  - right. exists (ii', count0 + 1, acc0 ++ [cur]).
    pose proof (jobj_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HO') as Hr'.
    subst m P. cbv beta iota. split; [lia | exact HO'].
Qed.

Lemma a3_json_of_parts : jseg_A -> jseg_B -> jseg_C -> jseg_D -> a3_json_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros HA HB HC HD cx h i n now op W0 c0 T0 T1 buf W c H.
  eapply SRr_bind; [exact (HA _ _ _ _ _ _ _ _ _ _ _ _ _ H)|].
  intros W1 c1 _ [HR | (fin & ii & vpad & HO)].
  - apply SRr_ret. exact HR.
  - exact (jobj_loop HB HC HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HO).
Qed.

End h.
End f.
End d.
