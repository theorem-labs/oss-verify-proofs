(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzMRun. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzMRun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.

Module GD.
Import AX2. Import AX2S. Import AX2B. Import MR.

(* [comment removed for export] *)
Definition RANGES : list (Z * nat) :=
  [(0x82578, 20%nat); (0x833ac, 14%nat); (0x82cf0, 360%nat); (0x835f8, 180%nat); (0x7ff38, 24%nat); (0x7bf84, 13%nat)].
Definition IT : itab := APC.mk_itab_ranges ASEGS RANGES.
Lemma IT_ok : itab_sound ASEGS IT.
Proof. exact (APS.mk_itab_ranges_sound ASEGS RANGES). Qed.

(* [comment removed for export] *)
Definition SR : list expr := ELit 0 :: map EVar (seq 1 31).
Definition LITA (a : Z) : saddr := SA (ELit 0) a.
Definition KN : list kentry :=
  [ KRange (EVar 2) (2 ^ 32 + 4096) (2 ^ 47 - 16); KAlign (EVar 2) 16;
    KRange (EVar 18) 4096 (2 ^ 47 - 1);
    KWr (SA (EVar 2) (-1072)) (ELit 1168);
    KWord (SA (EVar 2) 44) 4 (EVar 0);
    KWord (LITA 0x1e23c) 8 (ELit 0x612079726f6d656d);     (* [comment removed for export] *)
    KWord (LITA 0x1e244) 8 (ELit 0x7365726464612074);     (* [comment removed for export] *)
    KWord (LITA 0x1e24c) 4 (ELit 0x70252073);             (* [comment removed for export] *)
    KWord (LITA 0x1e250) 1 (ELit 0);                      (* [comment removed for export] *)
    KWord (LITA 0x22760) 4 (ELit 0x60940);                (* [comment removed for export] *)
    KWord (LITA 0x104b0) 8 (ELit 0xaaaaaaaaaaaaaaaa);     (* [comment removed for export] *)
    KWord (LITA 0xff2b0) 8 (ELit 1);
    KWord (LITA 0x19909c) 4 (ELit 0) ].
Definition SPIN : Z := 0x7bfb4.
Definition ENTRY : Z := 0x82578.
Definition BF : nat := 30000.

(* [comment removed for export] *)
Definition DIG (k : mplan) : mplan := MJoin (SReg 17) 9 [0x8383c] (MRun [0x83864; SPIN] k).
Fixpoint digs (n : nat) : mplan := match n with O => MSpin | S n' => DIG (digs n') end.
Definition CLS (k : nat) : mplan := MRun [0x83864; SPIN] (digs k).
Fixpoint classes (k : nat) (n : nat) : mplan :=
  match n with
  | O => CLS k
  | S n' => MCase (SExpr (EVar 18)) (16 ^ Z.of_nat k - 1) (CLS k) (classes (S k) n')
  end.
Definition PLAN : mplan := MRun [SPIN] (classes 4 8).

Lemma cert : mcheck ASEGS IT 0 BF SPIN PLAN ENTRY SR KN 32 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Definition genv (regs : bvmap 5 word) (v44 : word) : env :=
  Env (fun n => match n with O => v44 | _ => getr regs (Z_to_bv 5 (Z.of_nat n)) end) (fun _ => []).

Lemma regs_ok_genv : forall regs v44, regs_ok (genv regs v44) SR regs.
Proof.
  intros regs v44 r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - unfold getr. rewrite Hr0. reflexivity.
  - pose proof (ridx_range r) as Hlt.
    rewrite <- (ridx_roundtrip r) at 1. rewrite <- (ridx_roundtrip r) in Hr0.
    set (n := ridx r) in *. clearbody n.
    destruct n as [|n]; [vm_compute in Hr0; discriminate|].
    do 31 (destruct n as [|n]; [reflexivity|]).
    exfalso. lia.
Qed.

Lemma adenot_lit : forall E c, adenot E (LITA c) = Z_to_bv 64 c.
Proof. intros. reflexivity. Qed.

Lemma flat_lit : forall E c n, 0 <= c < 2 ^ 64 -> 0 <= n -> c + n <= 2 ^ 64 -> flat E (LITA c) n.
Proof.
  intros E c n Hc Hn Hcn. unfold flat, estart, LITA. cbn [a_base a_off edenot].
  change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
Qed.

Theorem grow_die :
  forall (fx : FPState) (regs : bvmap 5 word) (M rom : word -> option byte) (sp addr v44 : word),
    fx_ok fx ->
    getr regs 2 = sp -> getr regs 18 = addr ->
    2 ^ 32 + 4096 <= U sp <= 2 ^ 47 - 16 -> U sp mod 16 = 0 ->
    4096 <= U addr < 2 ^ 47 ->
    store_ok ASEGS M (at_ sp (-1072)) 1168 = true ->
    rdn ASEGS M (at_ sp 44) 4 = Some (word_to_le_bytes 4 v44) ->
    rdn ASEGS M (Z_to_bv 64 0x1e23c) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x612079726f6d656d)) ->
    rdn ASEGS M (Z_to_bv 64 0x1e244) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7365726464612074)) ->
    rdn ASEGS M (Z_to_bv 64 0x1e24c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x70252073)) ->
    rdn ASEGS M (Z_to_bv 64 0x1e250) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
    rdn ASEGS M (Z_to_bv 64 0x22760) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x60940)) ->
    rdn ASEGS M (Z_to_bv 64 0x104b0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xaaaaaaaaaaaaaaaa)) ->
    rdn ASEGS M (Z_to_bv 64 0xff2b0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
    rdn ASEGS M (Z_to_bv 64 0x19909c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    exists fx' r M', msteps ASEGS (@mkst fx regs (Z_to_bv 64 0x82578) M rom) (@mkst fx' r (Z_to_bv 64 0x7bfb4) M' rom).
Proof.
  intros fx regs M rom sp addr v44 HF H2 H18 Hsp Hal Haddr Hstk R44 R1 R2 R3 R4 R5 R6 R7 R8.
  pose proof (u64_range sp) as Hspr.
  assert (E2 : ev (genv regs v44) 2 = sp) by (cbn [genv ev]; rewrite <- H2; f_equal).
  assert (E18 : ev (genv regs v44) 18 = addr) by (cbn [genv ev]; rewrite <- H18; f_equal).
  refine (mcheck_sound ASEGS IT 0 BF SPIN IT_ok PLAN ENTRY SR KN 32 cert (genv regs v44) regs M rom fx (regs_ok_genv regs v44) _ HF).
  unfold KN, know_ok.
  repeat (apply Forall_cons); [ .. | apply Forall_nil];
    cbn [kentry_ok]; rewrite ?adenot_lit; cbn [edenot]; rewrite ?E2, ?E18;
    try (split; [lia | split; [apply flat_lit; lia | assumption]]).
  - lia.
  - split; [lia | exact Hal].
  - lia.
  - (* [comment removed for export] *)
    unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite E2. rewrite u_small by lia.
    split; [lia|]. intros d m Hd Hm.
    eapply (store_ok_sub ASEGS M (at_ sp (-1072)) _ 1168 m); [ | exact Hstk | | ];
      unfold at_; rewrite ?u_small by lia; lia.
  - (* [comment removed for export] *)
    split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off edenot]; rewrite E2; lia|].
    unfold adenot. cbn [a_base a_off edenot]. rewrite E2. exact R44.
Qed.

(* [comment removed for export] *)
Lemma pc_entry_w : Z_to_bv 64 0x82578 = (0x82578%bv : word).
Proof. apply bv_eq. reflexivity. Qed.
Lemma pc_spin_w : Z_to_bv 64 0x7bfb4 = (0x7bfb4%bv : word).
Proof. apply bv_eq. reflexivity. Qed.

Theorem grow_die_w :
  forall (fx : FPState) (regs : bvmap 5 word) (M rom : word -> option byte) (sp addr v44 : word),
    fx_ok fx ->
    getr regs 2 = sp -> getr regs 18 = addr ->
    2 ^ 32 + 4096 <= U sp <= 2 ^ 47 - 16 -> U sp mod 16 = 0 ->
    4096 <= U addr < 2 ^ 47 ->
    store_ok ASEGS M (at_ sp (-1072)) 1168 = true ->
    rdn ASEGS M (at_ sp 44) 4 = Some (word_to_le_bytes 4 v44) ->
    rdn ASEGS M (Z_to_bv 64 0x1e23c) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x612079726f6d656d)) ->
    rdn ASEGS M (Z_to_bv 64 0x1e244) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7365726464612074)) ->
    rdn ASEGS M (Z_to_bv 64 0x1e24c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x70252073)) ->
    rdn ASEGS M (Z_to_bv 64 0x1e250) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
    rdn ASEGS M (Z_to_bv 64 0x22760) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x60940)) ->
    rdn ASEGS M (Z_to_bv 64 0x104b0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xaaaaaaaaaaaaaaaa)) ->
    rdn ASEGS M (Z_to_bv 64 0xff2b0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
    rdn ASEGS M (Z_to_bv 64 0x19909c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    exists fx' r M', msteps ASEGS (@mkst fx regs (0x82578%bv : word) M rom) (@mkst fx' r (0x7bfb4%bv : word) M' rom).
Proof. intros. rewrite <- pc_entry_w, <- pc_spin_w. eapply grow_die; eassumption. Qed.

End GD.
