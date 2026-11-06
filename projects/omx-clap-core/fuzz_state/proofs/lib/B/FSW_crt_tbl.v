(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lane CRT's lib/A/FSW_crt_tbl.v (PORTED from
   a working branch e4ee8f8727e, blob 2dc90cb69d9; itself the table pattern of
   proofs/omx-clap-core/fuzz_state/lib/A/AB1k.v), in the form of lib/B/FSW_parse_string_tbl.v (a Theorem Labs lane). *)
(* fs program part, lane CRT, image B (fs.asan-ubsan): the decode table of check_round_trip's own text, for the walk's
   symbolic runs (lib/B FSW_K.v fsw_run_AJU / fsw_run_to_AJU and their tok twins take `table_ok tfibsegs tbl`). The range
   is RELOC-B's B/YB1w.v:446 names: tfib_A_check_round_trip = 0x81b9c .. tfib_E_check_round_trip = 0x82670, 2,772 bytes.
   build_table steps pc + 4 (Reusable/YP02.v), so the count is in 32-bit words: 693. MEASURED (capstone RISCV64 + C over
   the pinned fs.asan-ubsan, sha256 5ac5ce0954f87e2d...): those 2,772 bytes decode to exactly 693 four-byte instructions,
   so check_round_trip has no compressed instruction on B either and every instruction it executes is a table entry;
   52 jal sites, as on A (A's 667 instructions plus 26 more on B). Its calls leave the range; a run stops at the callee's
   entry, and the call step takes over there.
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from d25a984c903 via the lane's
   lib/A/FSW_crt_tbl.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1e.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition crt_text_start : Z := tfib_A_check_round_trip.
Definition crt_text_count : nat := Z.to_nat ((tfib_E_check_round_trip - tfib_A_check_round_trip) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma crt_text_exact : Z.of_nat crt_text_count * 4 = tfib_E_check_round_trip - tfib_A_check_round_trip.
Proof. vm_compute. reflexivity. Qed.
Lemma crt_text_count_693 : crt_text_count = 693%nat.
Proof. vm_compute. reflexivity. Qed.

Definition crt_tbl : ctable := Eval vm_compute in (build_table tfibsegs crt_text_start crt_text_count TEmpty).
Lemma crt_tbl_eq : crt_tbl = build_table tfibsegs crt_text_start crt_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl crt_tbl). Qed.
Lemma crt_tbl_ok : table_ok tfibsegs crt_tbl.
Proof. rewrite crt_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
(* the first word, the first call word (0x81c10), the ret 0x8261c, the last word 0x8266c and nothing past the range,
   as the listing gives them *)
Lemma crt_tbl_probe :
  clookup crt_tbl 0x81b9c = Some 0xf4010113 /\ clookup crt_tbl 0x81c10 = Some 0xbe9bb0ef /\
  clookup crt_tbl 0x8261c = Some 0x00008067 /\ clookup crt_tbl 0x8266c = Some 0xb85d60ef /\
  clookup crt_tbl 0x82670 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
