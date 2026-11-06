(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmSpecs PmParKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMTK2.
Section G.
Variable segs : list Segment. Context {bmK : BMode}.
Variable A : pm_addrs.
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').

Definition with_tb (s : PM.pst) (tb : PM.vstr) (tg : Z) : PM.pst :=
  PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) (PM.p_src s) tb tg (PM.p_b s) (PM.p_k s) (PM.p_stk s).

Lemma parser_tb_set op ois s tb tg :
  PM.parser_at segs A T3 T4 M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 -> ag op 336 -> ag (op + 360) 24 ->
  PMPK.dkr M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> ag (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  PM.vstr_at segs T3 M' (op + 336) tb -> L5.defined M' op 384 ->
  PM.parser_at segs A T3 T4 M' op ois (with_tb s tb tg).
Proof.
  intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) Ho Ho' AG AGv DKC Hb Hb' AGV TB' D'.
  assert (SUB : forall a n, op <= a -> a + n <= op + 336 -> ag a n) by (intros a n X Y; eapply L5C.agree_on_sub; [exact AG|lia|lia]).
  unfold with_tb, PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H0]|].
  split; [exact D'|]. split; [exact I|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H8]|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H9]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H12]|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H20]|].
  split; [apply (PMF.nullis_at_agree segs A M M'); [lia|lia| apply SUB; lia| exact NI]|].
  split.
  { destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
    split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact F1]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact F2]|].
    split; [apply (L5C.defined_agree M M'); [apply SUB; lia|exact F3]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact F4]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact F5]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact F6]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact F7]|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [apply (PMPK.defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H320]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H328]|].
  split; [exact I|]. split; [exact TB'|].
  split; [apply (PMF.vec_at_agree segs M M'); [lia|lia|exact Hb|exact Hb'| exact AGv| exact AGV| exact VEC]|].
  split; [exact B1|]. split; [exact B2| exact B3].
Qed.
End G.

Lemma u8_of_u32 (segs : list Segment) (M : word -> option byte) a w : 0 <= w < 2 ^ 32 -> L5.u32_at segs M a w -> L5.u8_at segs M a (w mod 256).
Proof.
  intros Hw H. unfold L5.u32_at, L5.u8_at in *. unfold word_to_le_bytes in H. rewrite L5.unsigned_lit in H by lia.
  change (Z_to_le_bytes 4 w) with (Z_to_bv 8 w :: Z_to_le_bytes 3 (Z.shiftr w 8)) in H.
  change (rdn segs M (Z_to_bv 64 a) 4) with
    (match (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) with
     | Some b => match rdn segs M (Z_to_bv 64 a + 1) 3 with Some rest => Some (b :: rest) | None => None end | None => None end) in H.
  cbn [rdn]. destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) as [b0|]; [|discriminate].
  destruct (rdn segs M (Z_to_bv 64 a + 1) 3) as [rest|]; [|discriminate]. injection H as Hb _. rewrite Hb. f_equal. f_equal.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
End PMTK2.
