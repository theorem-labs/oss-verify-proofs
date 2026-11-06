(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 959 of its 988 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntObs.v, with its module paths and module names changed; 172 of its 221 lines of code are new or changed and 939 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_jscalar_model disco_json_text disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition C2_RET (k : nat) : Z := 0x12c4 + 32 * Z.of_nat k.
Definition C2_M : Z := 0x1370.

Lemma set_nth_length : forall (k : nat) (o : jobj) (t : tokv), length (set_nth k o t) = length o.
Proof.
  intros k o. revert k. induction o as [|x o IH]; intros k t; destruct k as [|k]; cbn [set_nth length];
    try reflexivity. rewrite IH. reflexivity.
Qed.

Lemma slot_of_lt : forall (Bz : list Z) (t : tokv) (k : nat), slot_of Bz t = Some k -> (k < 6)%nat.
Proof.
  intros Bz t k H. unfold slot_of, keys in H. cbn [slot_from] in H.
  repeat (match type of H with context [if ?c then _ else _] => destruct c end;
    [injection H as <-; lia|]). discriminate H.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Record jc2p : Type := mkJC2 {
  p_cx : dcx; p_h : Z; p_i : Z; p_n : Z; p_now : Z; p_op : Z;
  p_W0 : world SEGS; p_c0 : config; p_T0 : list byte; p_T1 : list byte; p_buf : Z;
  p_fin : Z * list jobj; p_ip : Z; p_j2 : Z; p_kk : Z; p_ks : Z; p_kl : Z;
  p_vk : Z; p_vs : Z; p_vl : Z; p_cur : jobj; p_c2 : jobj; p_count : Z;
  p_acc : list jobj; p_vpad : list byte }.

Definition p_B (P : jc2p) : list Z := a3_text (p_T1 P) (p_now P).
Definition p_kt (P : jc2p) : tokv := (p_kk P, p_ks P, p_kl P).
Definition p_vt (P : jc2p) : tokv := (p_vk P, p_vs P, p_vl P).
Definition p_slot (P : jc2p) (k : nat) : Z := jcur (p_cx P) (p_count P) + 24 * Z.of_nat k.

Definition jc2_R (P : jc2p) (regs : bvmap 5 word) : Prop :=
  getr regs 19 = w64 (- a3_r (p_T1 P) (p_now P)) /\ getr regs 21 = w64 (p_j2 P) /\
  getr regs 23 = w64 (jcur (p_cx P) (p_count P)) /\ getr regs 24 = w64 (jcur (p_cx P) (p_count P) + 24) /\
  getr regs 27 = w64 (jcur (p_cx P) (p_count P) + 48).

Definition jc2_x (P : jc2p) (W : world SEGS) (m : word -> option byte) : Prop :=
  jfin_ok (p_T1 P) (p_now P) (p_fin P) /\ 0 <= p_ip P < p_j2 P /\ 0 <= p_count P /\
  length (p_acc P) = Z.to_nat (p_count P) /\ p_kk P = 1 /\ 1 <= p_vk P <= 3 /\
  jslot_upd (p_B P) (p_kt P) (p_vt P) (p_cur P) = Some (p_c2 P) /\
  jpairs_cont (p_B P) (p_fin P) (json_ws (p_B P) (p_j2 P)) (p_c2 P) (p_count P) (p_acc P) /\
  length (p_cur P) = 6%nat /\ Forall (slot_ser_tokb.tok_inb (p_B P)) (p_cur P) /\
  slot_ser_tokb.tok_inb (p_B P) (p_kt P) /\ slot_ser_tokb.tok_inb (p_B P) (p_vt P) /\
  jmem (p_cx P) (p_buf P) (p_count P) (p_vpad P) (p_acc P ++ [p_cur P]) W m /\
  val_mem SEGS (rd W m) (d_A (p_cx P) + 392) 8 (jcur (p_cx P) (p_count P) + 72) /\
  val_mem SEGS (rd W m) (d_A (p_cx P) + 336) 8 (jcur (p_cx P) (p_count P) + 96) /\
  val_mem SEGS (rd W m) (d_A (p_cx P) + 280) 8 (jcur (p_cx P) (p_count P) + 120) /\
  val_mem SEGS (rd W m) (d_A (p_cx P) + 448) 8 (p_buf P + p_ks P) /\
  val_mem SEGS (rd W m) (d_A (p_cx P) + 456) 8 (p_kl P) /\
  val_mem SEGS (rd W m) (d_A (p_cx P) + 464) 4 (p_kk P) /\
  val_mem SEGS (rd W m) (d_A (p_cx P) + 424) 8 (p_buf P + p_vs P) /\
  val_mem SEGS (rd W m) (d_A (p_cx P) + 432) 8 (p_vl P) /\
  val_mem SEGS (rd W m) (d_A (p_cx P) + 440) 4 (p_vk P).

Definition jc2_at (P : jc2p) (pc : Z) (R : bvmap 5 word -> Prop) (XX : Prop)
  : world SEGS -> config -> Prop :=
  jcut B MT XM_LIB RLO RHI tfib_K (p_cx P) (p_h P) (p_i P) (p_n P) (p_now P) (p_op P) (p_W0 P) (p_c0 P)
    (p_T0 P) (p_T1 P) (p_buf P) pc dsh_scr
    (fun regs => jc2_R P regs /\ R regs)
    (fun W m => jc2_x P W m /\ XX).

Definition jc2_kb (P : jc2p) (kb : nat) : Prop :=
  (kb <= 6)%nat /\ slot_of (p_B P) (p_kt P) = slot_from (p_B P) (p_kt P) (skipn kb keys) kb.

Definition jc2_res (P : jc2p) (kb : nat) (res : Z) : Prop :=
  (res = 1 /\ jtok_is (p_B P) (p_kt P) 1 (nth kb keys []) = true) \/
  (res = 0 /\ jtok_is (p_B P) (p_kt P) 1 (nth kb keys []) = false).

Definition jc2_call (P : jc2p) (kb : nat) : world SEGS -> config -> Prop :=
  jc2_at P AF_jtok_is
    (fun regs => getr regs 1 = w64 (BASE + C2_RET kb) /\ getr regs 10 = w64 (d_A (p_cx P) + 448) /\
       getr regs 11 = w64 1 /\ getr regs 12 = w64 (VAL (A_OBJ (4 + kb))))
    (jc2_kb P kb).

Definition jc2_ret (P : jc2p) (kb : nat) (res : Z) : world SEGS -> config -> Prop :=
  jc2_at P (C2_RET kb)
    (fun regs => getr regs 10 = w64 res)
    (jc2_kb P kb /\ jc2_res P kb res).

Definition jc2_mat (P : jc2p) (ksl : nat) : world SEGS -> config -> Prop :=
  jc2_at P C2_M
    (fun regs => getr regs 10 = w64 (p_slot P ksl))
    (slot_of (p_B P) (p_kt P) = Some ksl).

Definition jc2_cpy (P : jc2p) (ksl : nat) : world SEGS -> config -> Prop :=
  jc2_at P (SIGMA DS___asan_memcpy - BASE)
    (fun regs => getr regs 1 = w64 (BASE + SLOT_OFF) /\ getr regs 10 = w64 (p_slot P ksl) /\
       getr regs 11 = w64 (d_A (p_cx P) + 424) /\ getr regs 12 = w64 24)
    (slot_of (p_B P) (p_kt P) = Some ksl).

Definition jc2_out (P : jc2p) : world SEGS -> config -> Prop :=
  jslot_in B MT XM_LIB RLO RHI tfib_K (p_cx P) (p_h P) (p_i P) (p_n P) (p_now P) (p_op P) (p_W0 P) (p_c0 P)
    (p_T0 P) (p_T1 P) (p_buf P) (p_fin P) (p_ip P) (p_j2 P) (p_c2 P) (p_count P) (p_acc P) (p_vpad P).

Definition jc2_val (P : jc2p) : world SEGS -> config -> Prop :=
  jval_in B MT XM_LIB RLO RHI tfib_K (p_cx P) (p_h P) (p_i P) (p_n P) (p_now P) (p_op P) (p_W0 P) (p_c0 P)
    (p_T0 P) (p_T1 P) (p_buf P) (p_fin P) (p_ip P) (p_j2 P) (p_kk P) (p_ks P) (p_kl P)
    (p_vk P) (p_vs P) (p_vl P) (p_cur P) (p_c2 P) (p_count P) (p_acc P) (p_vpad P).

Definition jc2_hopV_stmt : Prop :=
  forall (P : jc2p) (W : world SEGS) (c : config), jc2_val P W c -> SRr SEGS W c (jc2_call P 0).

Definition jc2_jtk_stmt : Prop :=
  forall (P : jc2p) (kb : nat) (W : world SEGS) (c : config),
  (kb < 6)%nat -> jc2_call P kb W c ->
  SRr SEGS W c (fun W' c' => exists res, jc2_ret P kb res W' c').

Definition jc2_hopR_stmt : Prop :=
  forall (P : jc2p) (kb : nat) (res : Z) (W : world SEGS) (c : config),
  (kb < 6)%nat -> jc2_ret P kb res W c ->
  SRr SEGS W c (fun W' c' =>
    jc2_mat P kb W' c' \/ ((S kb < 6)%nat /\ jc2_call P (S kb) W' c') \/ jc2_out P W' c').

Definition jc2_hopM_stmt : Prop :=
  forall (P : jc2p) (ksl : nat) (W : world SEGS) (c : config),
  jc2_mat P ksl W c -> SRr SEGS W c (jc2_cpy P ksl).

Definition jc2_cp_stmt : Prop :=
  forall (P : jc2p) (ksl : nat) (W : world SEGS) (c : config),
  jc2_cpy P ksl W c -> SRr SEGS W c (jc2_out P).

Definition jc2_obj_stmt : Prop :=
  forall (buf : Z) (vpad : list byte) (acc : list jobj) (cur : jobj) (k : nat) (t : tokv),
  Forall (fun o => length o = 6%nat) acc -> length cur = 6%nat -> (k < 6)%nat -> tv_kind t <> 0 ->
  length vpad = 4%nat ->
  length (slot_ser_defs.objs_bytes buf vpad (acc ++ [set_nth k cur t])) =
    length (slot_ser_defs.objs_bytes buf vpad (acc ++ [cur])) /\
  (forall j, (j < length (slot_ser_defs.objs_bytes buf vpad (acc ++ [cur])))%nat ->
     nth j (slot_ser_defs.objs_bytes buf vpad (acc ++ [set_nth k cur t])) (Z_to_bv 8 0) =
     (if ((144 * length acc + 24 * k <=? j)%nat && (j <? 144 * length acc + 24 * k + 24)%nat)
      then nth (j - (144 * length acc + 24 * k))%nat (slot_ser_defs.slot24 buf vpad t) (Z_to_bv 8 0)
      else nth j (slot_ser_defs.objs_bytes buf vpad (acc ++ [cur])) (Z_to_bv 8 0))).

Definition jc2_zero_stmt : Prop :=
  forall (buf : Z) (vpad : list byte) (acc : list jobj) (cur : jobj) (k : nat),
  Forall (fun o => length o = 6%nat) acc -> length cur = 6%nat -> (k < 6)%nat -> length vpad = 4%nat ->
  tv_kind (nth k cur tok_none) = 0 ->
  forall j, (144 * length acc + 24 * k <= j < 144 * length acc + 24 * k + 24)%nat ->
  nth j (slot_ser_defs.objs_bytes buf vpad (acc ++ [cur])) (Z_to_bv 8 0) = Z_to_bv 8 0.

Lemma jc2_ws : forall (P : jc2p) (W : world SEGS) (m : word -> option byte),
  jc2_x P W m -> json_ws (p_B P) (p_j2 P) = p_j2 P.
Proof.
  intros P W m (HF & Hip & _). apply json_ws_id; [exact (proj1 (proj2 (proj2 HF))) | lia].
Qed.

Lemma jc2_acc6 : forall (P : jc2p) (W : world SEGS) (m : word -> option byte),
  jc2_x P W m -> Forall (fun o : jobj => length o = 6%nat) (p_acc P).
Proof.
  intros P W m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & HL) & _).
  exact (proj1 (proj1 (Forall_app _ _ _) HL)).
Qed.

Lemma jc2_count : forall (P : jc2p) (W : world SEGS) (m : word -> option byte),
  jc2_x P W m -> 0 <= p_count P <= 7.
Proof.
  intros P W m (HF & _ & Hc & _ & _ & _ & _ & HJ & _).
  pose proof (proj1 (proj2 HF)) as Hfin.
  destruct (jpairs_cont_step (p_B P) (p_fin P) _ _ _ _ HJ) as [(_ & HP) | (_ & _ & HA)].
  - pose proof (jpairs_from_count (p_B P) (p_fin P) _ _ _ _ HP). lia.
  - pose proof (jobjs_after_count (p_B P) (p_fin P) _ _ _ _ HA). lia.
Qed.

Lemma jc2_c2_ok : forall (P : jc2p) (W : world SEGS) (m : word -> option byte),
  jc2_x P W m -> length (p_c2 P) = 6%nat /\ Forall (slot_ser_tokb.tok_inb (p_B P)) (p_c2 P).
Proof.
  intros P W m (_ & _ & _ & _ & _ & _ & HU & _ & HL & HA & _ & HV & _).
  unfold jslot_upd in HU. destruct (slot_of (p_B P) (p_kt P)) as [k|] eqn:ES.
  - destruct (tv_kind (nth k (p_cur P) tok_none) =? 0); [|discriminate HU].
    injection HU as <-. rewrite set_nth_length. split; [exact HL|].
    apply slot_ser_tokb.set_nth_forall; [exact HA | exact HV].
  - injection HU as <-. split; [exact HL | exact HA].
Qed.

Lemma jc2_none : forall (P : jc2p) (W : world SEGS) (m : word -> option byte),
  jc2_x P W m -> slot_of (p_B P) (p_kt P) = None -> p_c2 P = p_cur P.
Proof.
  intros P W m (_ & _ & _ & _ & _ & _ & HU & _) HS. unfold jslot_upd in HU. rewrite HS in HU.
  injection HU as <-. reflexivity.
Qed.

Lemma jc2_some : forall (P : jc2p) (W : world SEGS) (m : word -> option byte) (k : nat),
  jc2_x P W m -> slot_of (p_B P) (p_kt P) = Some k ->
  tv_kind (nth k (p_cur P) tok_none) = 0 /\ p_c2 P = set_nth k (p_cur P) (p_vt P).
Proof.
  intros P W m k (_ & _ & _ & _ & _ & _ & HU & _) HS. unfold jslot_upd in HU. rewrite HS in HU.
  destruct (tv_kind (nth k (p_cur P) tok_none) =? 0) eqn:EK; [|discriminate HU].
  injection HU as <-. split; [apply Z.eqb_eq; exact EK | reflexivity].
Qed.

Lemma jc2_kb0 : forall P, jc2_kb P 0.
Proof. intros P. split; [lia | reflexivity]. Qed.

Lemma jc2_kb_step : forall (P : jc2p) (kb : nat), (kb < 6)%nat ->
  jc2_kb P kb -> jtok_is (p_B P) (p_kt P) 1 (nth kb keys []) = false -> jc2_kb P (S kb).
Proof.
  intros P kb Hk (_ & HE) HF. split; [lia|]. rewrite HE.
  replace (skipn kb keys) with (nth kb keys [] :: skipn (S kb) keys).
  - cbn [slot_from]. rewrite HF. reflexivity.
  - unfold keys in *. do 6 (destruct kb as [|kb]; [reflexivity|]). lia.
Qed.

Lemma jc2_kb_hit : forall (P : jc2p) (kb : nat), (kb < 6)%nat ->
  jc2_kb P kb -> jtok_is (p_B P) (p_kt P) 1 (nth kb keys []) = true ->
  slot_of (p_B P) (p_kt P) = Some kb.
Proof.
  intros P kb Hk (_ & HE) HT. rewrite HE.
  replace (skipn kb keys) with (nth kb keys [] :: skipn (S kb) keys).
  - cbn [slot_from]. rewrite HT. reflexivity.
  - unfold keys in *. do 6 (destruct kb as [|kb]; [reflexivity|]). lia.
Qed.

Lemma jc2_kb_end : forall (P : jc2p), jc2_kb P 6 -> slot_of (p_B P) (p_kt P) = None.
Proof. intros P (_ & HE). rewrite HE. reflexivity. Qed.

End h.
End f.
End d.
