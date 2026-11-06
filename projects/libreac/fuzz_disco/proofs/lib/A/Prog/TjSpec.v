(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-148
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:388-392 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFfi.v:262-264 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC4t.v:438 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_identity_ingest.v, with its module paths, module names and numbers changed; 4001 of its 4244 lines of code are new or changed and 2822 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacDiscoGateShouldPush.v, with its module paths and module names changed; 30 of its 60 lines of code are new or changed and 4214 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Definition TJ_FRAME : Z := 640.
Definition tj_fp (buf cap : Z) : list (Z * Z) := if cap <? 3 then [] else [(buf, buf + cap)].
Definition tj_len (T : list byte) (now : Z) : Z := Z.of_nat (length (reac_disco_table_json_c.tj_text T now)).
Definition tj_postP (STK EV : Z) (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (T : list byte) (now buf cap : Z) : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B STK (tj_fp buf cap) regs ly S W mem md EV
    (fun ly' S' W' regs' mem' md' =>
       Permutation (ablocks B ly' S') (ablocks B ly S) /\
       (cap < 3 -> getr regs' 10 = w64 (-1)) /\
       (3 <= cap -> tj_len T now < cap ->
          getr regs' 10 = w64 (tj_len T now) /\
          garr8 SEGS (mrestrict (w_H W') mem') buf (reac_disco_table_json_c.tj_text T now ++ [0])) /\
       (3 <= cap -> cap <= tj_len T now -> getr regs' 10 = w64 (-1))).
Definition tj_specP (STK EV : Z) (IMG : world SEGS -> (word -> option byte) -> Prop) : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (t now buf cap Nb : Z) (T : list byte),
  afn_pre SEGS B STK ly S W regs mem md ch ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fq)) 5) 7 = 0 ->
  Z.of_nat (length (frames S)) <= 7 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  IMG W mem ->
  getr regs 10 = w64 t -> getr regs 11 = w64 now -> getr regs 12 = w64 buf -> getr regs 13 = w64 cap ->
  0 <= now < 2 ^ 64 -> 0 <= cap < 2 ^ 31 ->
  afobj SEGS B ly S W mem t 400 ->
  garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) -> length T = 400%nat -> disco_table_c.table_ok T ->
  (3 <= cap -> In (buf, Nb) (ablocks B ly S) /\ cap <= req_size Nb) ->
  st_nev S + EV <= EV_MAX ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_disco_table_json) regs mem md)
    (tj_postP STK EV fq regs ly S W mem md T now buf cap).
End h.
End f.
End d.
