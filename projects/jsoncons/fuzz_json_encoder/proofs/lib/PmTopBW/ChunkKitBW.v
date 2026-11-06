(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound SegRun HeapIface HeapIfaceA L5Defs PmLibDefs PmLibDefsA PmLibSpecsA PmRef PmRefRead.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutHeap2.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopBW Require Import TopSpecsBW PsKitBW.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CKAW.
(* [comment removed for export] *)
Lemma chunkw_plain : forall s bof, (s = [] \/ bof = false) -> PMRR.chunkw s bof = (0%nat, 0, match s with [] => bof | _ => false end).
Proof. intros s bof H. unfold PMRR.chunkw. destruct s as [|b r]; [reflexivity|]. destruct H as [H | ->]; [discriminate H | reflexivity]. Qed.
Lemma chunkw_bom : forall s j, s <> [] -> PMR.detect s = Some j -> PMRR.chunkw s true = (j, 0, false).
Proof. intros s j Hs Hd. unfold PMRR.chunkw. destruct s as [|b r]; [exfalso; exact (Hs eq_refl)|]. rewrite Hd. reflexivity. Qed.
Lemma chunkw_bad : forall s, s <> [] -> PMR.detect s = None -> PMRR.chunkw s true = (0%nat, PMR.E_ILLEGAL_UNICODE, true).
Proof. intros s Hs Hd. unfold PMRR.chunkw. destruct s as [|b r]; [exfalso; exact (Hs eq_refl)|]. rewrite Hd. reflexivity. Qed.
Lemma eof_of_len : forall (s : list Z) k0, Z.of_nat (length s) = k0 -> (if (length s <? Z.to_nat PMR.CHUNK)%nat then 2 else 0) = (if k0 <? 16384 then 2 else 0).
Proof. intros s k0 H. change (Z.to_nat PMR.CHUNK) with (Z.to_nat 16384). destruct (Nat.ltb_spec (length s) (Z.to_nat 16384)); destruct (Z.ltb_spec k0 16384); lia. Qed.
Lemma match_same : forall (s : list Z) (b : bool), match s with [] => b | _ :: _ => b end = b.
Proof. intros [|x r] b; reflexivity. Qed.
Lemma nil_of_len0 : forall (s : list Z), Z.of_nat (length s) = 0 -> s = [].
Proof. intros [|b r] H; [reflexivity | cbn in H; lia]. Qed.
Lemma cons_of_len : forall (s : list Z) k0, Z.of_nat (length s) = k0 -> 0 < k0 -> s <> [].
Proof. intros [|b r] k0 H Hk; [cbn in H; lia | discriminate]. Qed.

(* [comment removed for export] *)
Lemma opt_some : forall (o : option nat) (A : nat -> Prop) (B : Prop), match o with Some j => A j | None => B end -> ~ B -> exists j, o = Some j /\ A j.
Proof. intros [j|] A B H NB; [exists j; split; [reflexivity | exact H] | exfalso; exact (NB H)]. Qed.
Lemma opt_none : forall (o : option nat) (A : nat -> Prop) (B : Prop), match o with Some j => A j | None => B end -> (forall j, ~ A j) -> o = None /\ B.
Proof. intros [j|] A B H NA; [exfalso; exact (NA j H) | split; [reflexivity | exact H]]. Qed.

(* [comment removed for export] *)
Lemma retE_a1 : forall E' nx R2, ev (CH2.retE E' nx R2) (nx + 5) = getr R2 11%bv.
Proof. intros E' nx R2. unfold CH2.retE. rewrite APS.ext_list_at by (clear; cbn; lia). cbn [APC.caller_saved map nth]. f_equal. Qed.
Lemma retEx_a1 : forall E' nx ghosts R2, ev (CH2.retEx E' nx ghosts R2) (nx + length ghosts + 5) = getr R2 11%bv.
Proof. intros. unfold CH2.retEx. apply retE_a1. Qed.

(* [comment removed for export] *)
Definition HALF (v : nat) : expr :=
  EAlu ALU_SLTU (EAlu ALU_SUB (EMd M_MUL (ELit 2) (EAluw ALU_SRL (EVar v) (ELit 1))) (ELit 0)) (ELit 1).
Lemma half_err : forall E v, 2 <= bv_unsigned (ev E v) <= 5 -> bv_unsigned (edenot E (HALF v)) = 0.
Proof.
  intros E v Hk. unfold HALF. cbn [edenot]. rewrite u_sltu64, u_sub64, u_mul64, !u_lit64a.
  rewrite (u_srlw_small (ev E v) (Z_to_bv 64 1) 1); [| rewrite u_lit64a; reflexivity | clear - Hk; lia | change (2 ^ (1 mod 32)) with 2; apply Z.div_lt_upper_bound; clear - Hk; lia].
  change (2 ^ (1 mod 32)) with 2. change (2 mod 2 ^ 64) with 2. change (0 mod 2 ^ 64) with 0. change (1 mod 2 ^ 64) with 1.
  pose proof (Z.div_le_mono 2 (bv_unsigned (ev E v)) 2 ltac:(clear; lia) ltac:(clear - Hk; lia)) as L1. pose proof (Z.div_le_mono (bv_unsigned (ev E v)) 5 2 ltac:(clear; lia) ltac:(clear - Hk; lia)) as L2.
  change (2 / 2) with 1 in L1. change (5 / 2) with 2 in L2. set (q := bv_unsigned (ev E v) / 2) in *.
  rewrite (Z.mod_small (2 * q)) by (clear - L1 L2; lia). rewrite Z.mod_small by (clear - L1 L2; lia).
  destruct (Z.ltb_spec (2 * q - 0) 1) as [X|X]; [exfalso; clear - X L1; lia | reflexivity].
Qed.

(* [comment removed for export] *)
Section W.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Lemma chunk_w_plain : forall (M' : PMSA.mem) IS rep gp bof ch p k2 k gp' rdst' code bof',
  (TPSAW.chunk_of IS rep gp = [] \/ bof = false) -> Z.of_nat (length (TPSAW.chunk_of IS rep gp)) = k ->
  p = ch -> k2 = k -> gp' = gp + k -> rdst' = (if k <? 16384 then 2 else 0) -> code = 0 -> bof' = bof ->
  L5.bytes_at (hl_segs L) M' ch (TPSAW.chunk_of IS rep gp) ->
  TPSAW.chunk_w L M' IS rep gp bof ch p k2 gp' rdst' code bof'.
Proof.
  intros M' IS rep gp bof ch p k2 k gp' rdst' code bof' KB LNS -> -> -> -> -> -> CT. unfold TPSAW.chunk_w. cbv zeta. set (s := TPSAW.chunk_of IS rep gp) in *.
  rewrite (chunkw_plain s bof KB). split; [clear - LNS; lia|]. split; [symmetry; apply eof_of_len; exact LNS|]. split; [reflexivity|].
  split; [destruct KB as [-> | ->]; [reflexivity | symmetry; apply match_same]|]. split; [| intros X; exfalso; exact (X eq_refl)].
  intros _. split; [clear - LNS; lia|]. intros _. split; [clear; lia | exact CT].
Qed.
Lemma chunk_w_bom : forall (M' : PMSA.mem) IS rep gp ch p k2 k gp' rdst' code bof' j,
  TPSAW.chunk_of IS rep gp <> [] -> PMR.detect (TPSAW.chunk_of IS rep gp) = Some j -> Z.of_nat (length (TPSAW.chunk_of IS rep gp)) = k ->
  p = ch + Z.of_nat j -> k2 = k - Z.of_nat j -> gp' = gp + k -> rdst' = (if k <? 16384 then 2 else 0) -> code = 0 -> bof' = false ->
  L5.bytes_at (hl_segs L) M' ch (TPSAW.chunk_of IS rep gp) ->
  TPSAW.chunk_w L M' IS rep gp true ch p k2 gp' rdst' code bof'.
Proof.
  intros M' IS rep gp ch p k2 k gp' rdst' code bof' j SNE DS LNS -> -> -> -> -> -> CT. unfold TPSAW.chunk_w. cbv zeta. set (s := TPSAW.chunk_of IS rep gp) in *.
  rewrite (chunkw_bom s j SNE DS). split; [clear - LNS; lia|]. split; [symmetry; apply eof_of_len; exact LNS|]. split; [reflexivity|].
  split; [reflexivity|]. split; [| intros X; exfalso; exact (X eq_refl)].
  intros _. split; [clear - LNS; lia|]. intros _. split; [reflexivity | exact (PKAW.bytes_at_skipn L M' ch s j CT)].
Qed.
Lemma chunk_w_bad : forall (M' : PMSA.mem) IS rep gp ch p k2 k gp' rdst' code bof',
  TPSAW.chunk_of IS rep gp <> [] -> PMR.detect (TPSAW.chunk_of IS rep gp) = None -> Z.of_nat (length (TPSAW.chunk_of IS rep gp)) = k ->
  k2 = 0 -> gp' = gp + k -> rdst' = (if k <? 16384 then 2 else 0) -> code = PMR.E_ILLEGAL_UNICODE -> bof' = true ->
  TPSAW.chunk_w L M' IS rep gp true ch p k2 gp' rdst' code bof'.
Proof.
  intros M' IS rep gp ch p k2 k gp' rdst' code bof' SNE DS LNS -> -> -> -> ->. unfold TPSAW.chunk_w. cbv zeta. set (s := TPSAW.chunk_of IS rep gp) in *.
  rewrite (chunkw_bad s SNE DS). split; [clear - LNS; lia|]. split; [symmetry; apply eof_of_len; exact LNS|]. split; [reflexivity|].
  split; [reflexivity|]. split; [intros X; discriminate X | intros _; reflexivity].
Qed.
End W.
End CKAW.
