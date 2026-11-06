(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3B AxSymExec3Sound HeapIface HeapIfaceA FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibDefs PmLibDefsA PmCurDefs AsanAcct LibSym.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutL5A.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module NKA.
Section Agree.
Variable segs : list Segment.
Variable IC : PMLA.consts.
Variables (M M' : PTA.mem) (S : Z -> Prop).
Hypothesis AG : forall a, S a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).

Lemma parser_at_more : forall P ps (m : bool),
  (forall k n, 0 <= k -> k + n <= 272 -> (k + n <= 211 \/ 212 <= k) -> PTA.out S (P + k) n) -> PTA.out S (PML.ps_bptr ps) (PML.ps_bcap ps) -> PTA.out S (PML.ps_sb ps) (PML.ps_scap ps) ->
  PMLA.parser_at segs IC M P ps -> L5.u8_at segs M' (P + 211) (PML.b2z m) -> M' (Z_to_bv 64 (P + 211)) <> None ->
  PMLA.parser_at segs IC M' P (PMCUR.ps_set_more ps m).
Proof.
  intros P ps m HP HB HS H H211 HDEF. unfold PMCUR.ps_set_more. unfold PMLA.parser_at, PMLA.u64, PMLA.u32, PMLA.u8 in *.
  cbn [PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win].
  destruct H as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30).
  assert (O : forall k n, 0 <= k -> k + n <= 272 -> (k + n <= 211 \/ 212 <= k) -> PTA.out S (P + k) n) by exact HP.
  split; [apply (PTA.u64_ag segs M M' S AG); [replace P with (P + 0) by lia; apply O; lia | exact A0]|].
  split; [apply (PTA.u32_ag segs M M' S AG); [apply O; lia | exact A1]|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply O; lia | exact A2]|]. split; [apply (PTA.u8_ag segs M M' S AG); [apply O; lia | exact A3]|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply O; lia | exact A4]|]. split; [apply (PTA.u8_ag segs M M' S AG); [apply O; lia | exact A5]|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply O; lia | exact A6]|]. split; [apply (PTA.u8_ag segs M M' S AG); [apply O; lia | exact A7]|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply O; lia | exact A8]|].
  split; [apply (PTA.lstr_short_nil_ag segs M M' S AG); [apply O; lia | exact A9]|]. split; [apply (PTA.lstr_short_nil_ag segs M M' S AG); [apply O; lia | exact A10]|].
  split; [apply (PTA.lstr_short_nil_ag segs M M' S AG); [apply O; lia | exact A11]|].
  split; [apply (PTA.u64_ag segs M M' S AG); [apply O; lia | exact A12]|]. split; [apply (PTA.u64_ag segs M M' S AG); [apply O; lia | exact A13]|].
  split; [apply (PTA.u32_ag segs M M' S AG); [apply O; lia | exact A14]|].
  split; [destruct (PML.ps_win ps) as [[p e]|]; [destruct A15 as (X & Y & Z); split; [apply (PTA.u64_ag segs M M' S AG); [apply O; lia | exact X] | split; [apply (PTA.u64_ag segs M M' S AG); [apply O; lia | exact Y] | exact Z]]
                                                 | destruct A15 as (X & Y); split; apply (PTA.u64_ag segs M M' S AG); try (apply O; lia); assumption]|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply O; lia | exact A16]|]. split; [apply (PTA.u8_ag segs M M' S AG); [apply O; lia | exact A17]|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply O; lia | exact A18]|].
  split; [exact H211|]. split; [apply (PTA.u8_ag segs M M' S AG); [apply O; lia | exact A20]|]. split; [apply (PTA.u8_ag segs M M' S AG); [apply O; lia | exact A21]|].
  split; [apply (PTA.u32_ag segs M M' S AG); [apply O; lia | exact A22]|].
  split; [apply (PTA.str_long_ag segs M M' S AG); [apply O; lia | exact HB | exact A23]|]. split; [exact A24|].
  split; [apply (PTA.u64_ag segs M M' S AG); [apply O; lia | exact A25]|]. split; [apply (PTA.u64_ag segs M M' S AG); [apply O; lia | exact A26]|].
  split; [apply (PTA.u64_ag segs M M' S AG); [apply O; lia | exact A27]|].
  split; [apply (PTA.bytes_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ HS); lia | exact A28]|]. split; [exact A29|].
  intros i Hi. destruct (Z.eq_dec i 211) as [->|Hne]; [exact HDEF|]. destruct (O i 1 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & G). rewrite AG; [exact (A30 i Hi) | apply G; lia].
Qed.
End Agree.

Lemma u8_defined : forall segs (M : PTA.mem) top a v, segs_below_b segs top = true -> 0 <= top -> top <= a < 2 ^ 64 -> L5.u8_at segs M a v -> M (Z_to_bv 64 a) <> None.
Proof.
  intros segs M top a v Hb H0 Ha Hu Hn. unfold L5.u8_at in Hu. cbn [rdn] in Hu. rewrite Hn in Hu. unfold seg_rom, memory_read in Hu.
  rewrite (u64_of_Z a ltac:(lia)) in Hu. change (Z.of_N 1) with 1 in Hu. rewrite (find_segment1_none_above segs top a Hb ltac:(lia)) in Hu. discriminate Hu.
Qed.
Lemma u8_byte : forall segs (M : PTA.mem) top a v, segs_below_b segs top = true -> 0 <= top -> top <= a < 2 ^ 64 -> L5.u8_at segs M a v -> byte_at M a v.
Proof. intros segs M top a v Hb H0 Ha Hu. exact (CL5A.u8_byte_at segs M a v (u8_defined segs M top a v Hb H0 Ha Hu) Hu). Qed.
End NKA.
