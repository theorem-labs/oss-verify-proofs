(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: start-up row img-su-printf-A (CF-UNIT-HYPS.md (sha256 77b3f94c95d2; internal record) Table 4, line 154,
   "printf callback cell = AppendToErrorMessageBuffer"), at plugin-hostd/fuzz_reply's asan image A: in reply A's
   start-up records, each of the 50 hand-off states (AB01.v HS_tfib_list) and the join state (AB03.v JS_tfib_band)
   holds the 8-byte printf-callback cell with the post-init value AppendToErrorMessageBuffer.  The records are the
   twins of cgif's YB01.v HS_tfib_0_kn / YB03.v JS_tfib_band (cgif: *0x137f90 = 0x54bec).
   Kind: START-UP fact (a measurement of the start-up certificate), no function proved (rule 24).

   Measurement (python3 pyelftools + capstone 5.0.7, RISCV64 + C):
   pinned image fuzz_reply.asan sha256 42c58610e125e0b47770217f7175ffe2f23ed5ee1399b3e81539eff364611d5a; symbols from
   the unstripped twin sha256 d751b179ea493ead8cda011f65c1503ba46920e9d4eefe8638cf412fb1a55709, whose R+X PT_LOAD
   (0x30994 + 0x6baa4) and both RW PT_LOADs (0x9d438, 0x9f6e0) are byte-equal to the pinned file's (only PT_LOAD[0],
   the ELF header / build-id / rodata, differs).
   (a) The cell.  _ZN11__sanitizer26SetPrintfAndReportCallbackEPFvPKcE = 0x68574 (size 12; AB1w.v:350
       tfib_A_SetPrintfAndReportCallback):
         0x68574  97050d00  auipc a1, 0xd0
         0x68578  23bea584  sd    a0, -0x7a4(a1)        -> stores a0 to 0x68574 + 0xd0000 - 0x7a4 = 0x137dd0
         0x6857c  67800000  ret
       0x137dd0 is the symtab object _ZN11__sanitizerL23PrintfAndReportCallbackE (size 8), in .bss
       [0xa2a00, 0x5fad50) (past the file size of PT_LOAD 0x9f6e0 + 0x3300), so the image holds 0 there.  The text
       has one other reference to it, the reader in SharedPrintfCodeNoBuffer+0x100 (0x68c8c auipc a0, 0xcf;
       0x68c90 ld a1, 0x144(a0)), and no other store.
   (b) The value.  The text has one call of SetPrintfAndReportCallback (no auipc+jalr pair and no data pointer to
       0x68574), in _ZN6__asanL16AsanInitInternalEv (0x5ab3c, size 692):
         0x5ac58  17450400  auipc a0, 0x44
         0x5ac5c  03350591  ld    a0, -0x6f0(a0)        -> a0 := *(0x5ac58 + 0x44000 - 0x6f0) = *0x9e568
         0x5ac60  efd05011  jal   0x68574
       0x9e568 is in .got [0x9d970, 0x9e6c8) and holds 0x563c0 in the pinned file (static link, no relocation),
       = _ZN6__asan26AppendToErrorMessageBufferEPKc (0x563c0, size 716).
   So init runs SetPrintfAndReportCallback(AppendToErrorMessageBuffer): *0x137dd0 = 0x563c0 after AsanInitInternal,
   i.e. a_off 1277392 holds ELit 353216.  Cross-check of the records: AB01.v:19 (HS_tfib_0_kn) and AB03.v:15
   (JS_tfib_band) each carry `KWord {| a_base := ELit 0; a_off := 1277392 |} 8 (ELit 353216)`; the other 49
   hand-off lists are built from HS_tfib_0_kn by seg/++, and the lemmas below check every list by computation.

   Symbol constants: lib/A/AB1w.v names neither address (no 0x137dd0, no 0x563c0, no PrintfAndReportCallback, no
   AppendToErrorMessageBuffer row), so the cell and the value are RAW numerals here, read from the ELF as above;
   the only AB1w.v constant on the path is the setter's entry tfib_A_SetPrintfAndReportCallback = 0x68574.

   cf name: CF-UNIT-HYPS.md (sha256 77b3f94c95d2; internal record) Table 4 has no Definition for "printf callback cell = AppendToErrorMessageBuffer" and the
   reply tree carries none, so the statements below are the UNFOLDED text of that row at reply A. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0c YK09 YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AB01 AB03.
Import ListNotations. Import AX2. Import APC.
Open Scope Z_scope.

(* _ZN11__sanitizerL23PrintfAndReportCallbackE (raw; (a) above). *)
Definition replyA_printf_cb_cell : Z := 0x137dd0.
(* _ZN6__asan26AppendToErrorMessageBufferEPKc (raw; (b) above). *)
Definition replyA_printf_cb_fn : Z := 0x563c0.

(* Every hand-off state of reply A's start-up certificate (AB01.v, 50 states: AB01.HS_tfib_length) knows the
   callback cell holds AppendToErrorMessageBuffer. *)
Lemma replyA_su_printf_handoff_all : forall s, In s AB01.HS_tfib_list ->
  In (KWord {| a_base := ELit 0; a_off := replyA_printf_cb_cell |} 8 (ELit replyA_printf_cb_fn))
     (s_know (a_ss s)).
Proof.
  assert (H : forallb (kn_mem (KWord {| a_base := ELit 0; a_off := replyA_printf_cb_cell |} 8
                                       (ELit replyA_printf_cb_fn)))
                AB01.HS_tfib_list = true) by (vm_compute; reflexivity).
  intros s Hs. exact (kn_mem_In _ s (proj1 (forallb_forall _ _) H s Hs)).
Qed.

(* The same, indexed as AB01.v indexes the hand-off states. *)
Corollary replyA_su_printf_handoff : forall h s, AB01.HS_tfib h = Some s ->
  In (KWord {| a_base := ELit 0; a_off := replyA_printf_cb_cell |} 8 (ELit replyA_printf_cb_fn))
     (s_know (a_ss s)).
Proof. intros h s H. exact (replyA_su_printf_handoff_all s (AB01.HS_tfib_In h s H)). Qed.

(* The join state of reply A's start-up certificate (AB03.v). *)
Lemma replyA_su_printf_join :
  In (KWord {| a_base := ELit 0; a_off := replyA_printf_cb_cell |} 8 (ELit replyA_printf_cb_fn))
     (s_know (a_ss AB03.JS_tfib_band)).
Proof.
  assert (H : kn_mem (KWord {| a_base := ELit 0; a_off := replyA_printf_cb_cell |} 8 (ELit replyA_printf_cb_fn))
                AB03.JS_tfib_band = true) by (vm_compute; reflexivity).
  exact (kn_mem_In _ _ H).
Qed.

(* Row img-su-printf-A: the hand-off states and the join state together. *)
Theorem replyA_su_printf :
  (forall s, In s AB01.HS_tfib_list ->
     In (KWord {| a_base := ELit 0; a_off := replyA_printf_cb_cell |} 8 (ELit replyA_printf_cb_fn))
        (s_know (a_ss s)))
  /\ In (KWord {| a_base := ELit 0; a_off := replyA_printf_cb_cell |} 8 (ELit replyA_printf_cb_fn))
        (s_know (a_ss AB03.JS_tfib_band)).
Proof. exact (conj replyA_su_printf_handoff_all replyA_su_printf_join). Qed.

About replyA_su_printf_handoff_all.
About replyA_su_printf_handoff.
About replyA_su_printf_join.
About replyA_su_printf.
Print Assumptions replyA_su_printf.
