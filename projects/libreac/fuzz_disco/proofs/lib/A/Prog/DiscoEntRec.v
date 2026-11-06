(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 60 of its 91 lines of code are new or changed and 38 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YE00 YE01 YC5d YO09 YCbp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoSites DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntShChk.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
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
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Lemma d_call_chain : forall (pc0 off : Z) (cx : dcx) ly3 S3 (W3 : world SEGS) mem3 md3 k
  (regs : bvmap 5 word) (V0 : Z),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  pc0 < BASE -> 0 <= off -> 4096 <= BASE + off ->
  In [pc0; BASE + off] (as_universe B) -> In [pc0; BASE + off; RA_LLVMF] (as_universe B) ->
  spZ regs = d_A cx -> s0Z regs = d_S cx -> d_A cx + 16 <= d_S cx -> raZ regs = BASE + off ->
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 8) = Some RA_LLVMF ->
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 16) = Some V0 ->
  (bad_next (d_S cx) (ly_top ly3) V0 = true \/ fpchain (rdword (aview SEGS (w_H W3) mem3)) V0 (ly_top ly3) []) ->
  exists ch, chain_pre ly3 (aview SEGS (w_H W3) mem3) regs ch /\
    In (call_trace0 pc0 regs ch) (as_universe B).
Proof.
intros pc0 off cx ly3 S3 W3 mem3 md3 k regs V0 Hctx Hpc0 Hoff Hra4 HU2 HU3 Hsp Hs0 HAS Hra Hsave HV0 HCH.
assert (Hrane : (BASE + off =? pc0) = false) by (apply Z.eqb_neq; lia).
assert (Htr0 : forall l, (length l <= 1)%nat -> In (pc0 :: [BASE + off] ++ l) (as_universe B) ->
          In (firstn kUnwindMax (pc0 :: (if BASE + off =? pc0 then [] else [BASE + off]) ++ l)) (as_universe B)).
{ intros l Hlen Hl. rewrite Hrane. cbn [app] in *.
  destruct l as [|x [|y l']]; cbn [length] in Hlen; try lia;
  change kUnwindMax with 30%nat; cbn [firstn]; exact Hl. }
assert (Htr1 : In (firstn kUnwindMax (pc0 :: (if BASE + off =? pc0 then [] else [BASE + off]) ++
          (if RA_LLVMF =? pc0 then [] else [RA_LLVMF]) ++ [])) (as_universe B)).
{ destruct (Z.eqb_spec RA_LLVMF pc0) as [He|Hne].
  - apply Htr0; [cbn [length app]; lia|]. cbn [app]. exact HU2.
  - apply Htr0; [cbn [length app]; lia|]. cbn [app]. exact HU3. }
unfold chain_pre, frame0_ok, call_trace0, unwind_of_chain.
rewrite Hra.
destruct (spZ regs + 16 <? ly_top ly3) eqn:Hf0.
- destruct (bad_next (spZ regs) (ly_top ly3) (s0Z regs)) eqn:Hbn.
  + exists []. split; [split; [lia | reflexivity]|].
    cbn [flat_map app]. apply Htr0; [cbn [length]; lia|]. cbn [app]. exact HU2.
  + exists [(s0Z regs, RA_LLVMF, V0)]. split.
    { unfold bad_next in Hbn.
      apply Bool.orb_false_elim in Hbn as [Hbn1 Hbn3].
      apply Bool.orb_false_elim in Hbn1 as [Hbn1 Hbn2].
      apply Z.leb_gt in Hbn1. apply Z.leb_gt in Hbn2.
      apply Bool.negb_false_iff, Z.eqb_eq in Hbn3.
      split; [lia|]. split; [lia|].
      cbn [fpchain]. split; [reflexivity|]. split; [exact Hbn3|].
      rewrite <- Hs0 in Hsave, HV0. split; [exact Hsave|]. split; [exact HV0|].
      split; [unfold RA_LLVMF; lia|].
      rewrite Hs0. destruct HCH as [Hb|Hf].
      - rewrite Hb. reflexivity.
      - destruct (bad_next (d_S cx) (ly_top ly3) V0); [reflexivity | exact Hf]. }
    { cbn [flat_map app]. exact Htr1. }
- exists []. split; [split; [lia | reflexivity]|].
  cbn [flat_map app]. apply Htr0; [cbn [length]; lia|]. cbn [app]. exact HU2.
Qed.

End h.
End f.
End d.
