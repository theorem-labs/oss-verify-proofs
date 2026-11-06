(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_su_printf.v (commit 4d286b2e618d, file sha256 90edc3226891) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 2 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 9 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: start-up row img-su-printf-B (the internal file CF-UNIT-HYPS.md Table 4, line 154,
   "printf callback cell = AppendToErrorMessageBuffer"), at plugin-hostd/fuzz_reply's asan-ubsan image B: in reply B's
   start-up records, each of the 50 hand-off states (YB01.v HS_tfib_list) and the join state (YB03.v JS_tfib_band)
   holds the 8-byte printf-callback cell with the post-init value AppendToErrorMessageBuffer.  The records are the
   twins of cgif's YB01.v HS_tfib_0_kn / YB03.v JS_tfib_band (cgif: *0x137f90 = 0x54bec).  The B twin of
   lib/A/PresetImg_su_printf.v (a prior worker, row img-su-printf-A): same statements, image B's numbers.
   Kind: START-UP fact (a measurement of the start-up certificate), no function proved (rule 24).
   Reuse search (proof-index, 2026-10-30 04:5xZ): PrintfAndReportCallback 0 named, 0 released;
   AppendToErrorMessageBuffer 0 named, 17 files of other units use its address, no released lemma states this fact.

   Measurement (python3 pyelftools + capstone, RISCV64 + C):
   pinned image fuzz_reply.asan-ubsan sha256 10ffb5f9202ae2bdb01b7a49df9866843a6a6a0e0c50bc67cdba6ce2f6d3cf2c; symbols
   from the unstripped twin sha256 3389287e1d6107841f4e2bb22c691542a11433094c1a07d94fd5828afc3671f7, whose R+X PT_LOAD
   (0x309ec + 0x6bfcc) and both RW PT_LOADs (0xa2240, 0x9fc60) are byte-equal to the pinned file's (only PT_LOAD[0],
   the ELF header / build-id / rodata, differs).
   (a) The cell.  _ZN11__sanitizer26SetPrintfAndReportCallbackEPFvPKcE = 0x685cc (size 12; YB1w.v:349
       tfib_A_SetPrintfAndReportCallback):
         0x685cc  97050d00  auipc a1, 0xd0
         0x685d0  23b2a5d8  sd    a0, -0x27c(a1)        -> stores a0 to 0x685cc + 0xd0000 - 0x27c = 0x13d410
         0x685d4  67800000  ret
       0x13d410 is the symtab object _ZN11__sanitizerL23PrintfAndReportCallbackE (size 8), in .bss
       [0xa2f80, 0x5fb2d0) (past the file size of PT_LOAD 0x9fc60 + 0x3300), so the image holds 0 there.  The text
       has one other reference to it, the reader in SharedPrintfCodeNoBuffer+0x104 (0x68ce8 ld), and no other store.
   (b) The value.  The text has one call of SetPrintfAndReportCallback (no auipc+jalr pair and no data pointer to
       0x685cc), in _ZN6__asanL16AsanInitInternalEv (0x5ab94, size 692):
         0x5acb0  17450400  auipc a0, 0x44
         0x5acb4  033585e3  ld    a0, -0x1c8(a0)        -> a0 := *(0x5acb0 + 0x44000 - 0x1c8) = *0x9eae8
         0x5acb8  efd05011  jal   0x685cc
       0x9eae8 is in .got [0x9def0, 0x9ec48) and holds 0x55df8 in the pinned file (static link, no relocation),
       = _ZN6__asan26AppendToErrorMessageBufferEPKc (0x55df8, size 716).
   So init runs SetPrintfAndReportCallback(AppendToErrorMessageBuffer): *0x13d410 = 0x55df8 after AsanInitInternal,
   i.e. a_off 1278800 holds ELit 353304.  Cross-check of the records: YB01.v:19 (HS_tfib_0_kn) and YB03.v:15
   (JS_tfib_band) each carry `KWord {| a_base := ELit 0; a_off := 1278800 |} 8 (ELit 353304)`; the other 49
   hand-off lists are built from HS_tfib_0_kn by seg/++, and the lemmas below check every list by computation.

   Symbol constants: lib/B/YB1w.v names neither address (no 0x13d410, no 0x55df8, no PrintfAndReportCallback, no
   AppendToErrorMessageBuffer row), so the cell and the value are RAW numerals here, read from the ELF as above;
   the only YB1w.v constant on the path is the setter's entry tfib_A_SetPrintfAndReportCallback = 0x685cc.

   cf name: the internal file CF-UNIT-HYPS.md Table 4 has no Definition for "printf callback cell = AppendToErrorMessageBuffer" and the
   reply tree carries none, so the statements below are the UNFOLDED text of that row at reply B. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0c YK09 YA0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YB01 YB03.
Import ListNotations. Import AX2. Import APC.
Open Scope Z_scope.

(* _ZN11__sanitizerL23PrintfAndReportCallbackE (raw; (a) above). *)
Definition presetB_printf_cb_cell : Z := 0x13d410.
(* _ZN6__asan26AppendToErrorMessageBufferEPKc (raw; (b) above). *)
Definition presetB_printf_cb_fn : Z := 0x55df8.

(* Every hand-off state of reply B's start-up certificate (YB01.v, 50 states: YB01.HS_tfib_length) knows the
   callback cell holds AppendToErrorMessageBuffer. *)
Lemma presetB_su_printf_handoff_all : forall s, In s YB01.HS_tfib_list ->
  In (KWord {| a_base := ELit 0; a_off := presetB_printf_cb_cell |} 8 (ELit presetB_printf_cb_fn))
     (s_know (a_ss s)).
Proof.
  assert (H : forallb (kn_mem (KWord {| a_base := ELit 0; a_off := presetB_printf_cb_cell |} 8
                                       (ELit presetB_printf_cb_fn)))
                YB01.HS_tfib_list = true) by (vm_compute; reflexivity).
  intros s Hs. exact (kn_mem_In _ s (proj1 (forallb_forall _ _) H s Hs)).
Qed.

(* The same, indexed as YB01.v indexes the hand-off states. *)
Corollary presetB_su_printf_handoff : forall h s, YB01.HS_tfib h = Some s ->
  In (KWord {| a_base := ELit 0; a_off := presetB_printf_cb_cell |} 8 (ELit presetB_printf_cb_fn))
     (s_know (a_ss s)).
Proof. intros h s H. exact (presetB_su_printf_handoff_all s (YB01.HS_tfib_In h s H)). Qed.

(* The join state of reply B's start-up certificate (YB03.v). *)
Lemma presetB_su_printf_join :
  In (KWord {| a_base := ELit 0; a_off := presetB_printf_cb_cell |} 8 (ELit presetB_printf_cb_fn))
     (s_know (a_ss YB03.JS_tfib_band)).
Proof.
  assert (H : kn_mem (KWord {| a_base := ELit 0; a_off := presetB_printf_cb_cell |} 8 (ELit presetB_printf_cb_fn))
                YB03.JS_tfib_band = true) by (vm_compute; reflexivity).
  exact (kn_mem_In _ _ H).
Qed.

(* Row img-su-printf-B: the hand-off states and the join state together. *)
Theorem presetB_su_printf :
  (forall s, In s YB01.HS_tfib_list ->
     In (KWord {| a_base := ELit 0; a_off := presetB_printf_cb_cell |} 8 (ELit presetB_printf_cb_fn))
        (s_know (a_ss s)))
  /\ In (KWord {| a_base := ELit 0; a_off := presetB_printf_cb_cell |} 8 (ELit presetB_printf_cb_fn))
        (s_know (a_ss YB03.JS_tfib_band)).
Proof. exact (conj presetB_su_printf_handoff_all presetB_su_printf_join). Qed.

About presetB_su_printf_handoff_all.
About presetB_su_printf_handoff.
About presetB_su_printf_join.
About presetB_su_printf.
Print Assumptions presetB_su_printf.
