(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The addresses fuzz_pcap.asan-ubsan (v1.9.0, pin sha256
   9e66f771f22af67aadc8b8ddcd7ee91f46c4c63442c694faaf2375f9c5b79321) gives the
   listing's names, objects and auipc values.
   The objects past the ones the slots build are the cells the walks read
   through a GOT word: __asan_shadow_memory_dynamic_address (the shadow base) and
   __asan_option_detect_stack_use_after_return. *)
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition pcap_text : Z := Eval compute in Symbols.AsanUbsan.s_libreac_fuzz_fopen.  (* the listing's first function *)
Definition pcap_sigma (s : psym) : Z :=
match s with
| PS___interceptor_trampoline_strcmp => (symaddr Symbols.AsanUbsan.s___wrap_strcmp)
| PS___interceptor_trampoline_fopen => (symaddr Symbols.AsanUbsan.s___wrap_fopen)
| PS___interceptor_trampoline_fmemopen => (symaddr Symbols.AsanUbsan.s___wrap_fmemopen)
| PS___asan_stack_malloc_1 => (symaddr Symbols.AsanUbsan.s___asan_stack_malloc_1)
| PS___interceptor_trampoline_malloc => (symaddr Symbols.AsanUbsan.s___wrap_malloc)
| PS___asan_memcpy => (symaddr Symbols.AsanUbsan.s___asan_memcpy)
| PS___asan_memset => (symaddr Symbols.AsanUbsan.s___asan_memset)
| PS_pcap_source_open => (symaddr Symbols.AsanUbsan.s_pcap_source_open)
| PS_rd32 => (symaddr Symbols.AsanUbsan.s_rd32)
| PS___interceptor_trampoline_free => (symaddr Symbols.AsanUbsan.s___wrap_free)
| PS_pcap_source_next => (symaddr Symbols.AsanUbsan.s_pcap_source_next)
| PS___interceptor_trampoline_bcmp => (symaddr Symbols.AsanUbsan.s___wrap_bcmp)
| PS___asan_report_load1 => (symaddr Symbols.AsanUbsan.s___asan_report_load1)
| PS_pcap_source_close => (symaddr Symbols.AsanUbsan.s_pcap_source_close)
| PS___asan_handle_no_return => (symaddr Symbols.AsanUbsan.s___asan_handle_no_return)
| PS_abort => (symaddr Symbols.AsanUbsan.s_abort)
| PS___asan_init => (symaddr Symbols.AsanUbsan.s___asan_init)
| PS___asan_version_mismatch_check_v8 => (symaddr Symbols.AsanUbsan.s___asan_version_mismatch_check_v8)
| PS___asan_register_elf_globals => (symaddr Symbols.AsanUbsan.s___asan_register_elf_globals)
| PS___asan_unregister_elf_globals => (symaddr Symbols.AsanUbsan.s___asan_unregister_elf_globals)
| PS_libreac_fuzz_fopen => (symaddr Symbols.AsanUbsan.s_libreac_fuzz_fopen)
| PS___interceptor_trampoline_fread => (symaddr Symbols.AsanUbsan.s___wrap_fread)
| PS___interceptor_trampoline_fclose => (symaddr Symbols.AsanUbsan.s___wrap_fclose)
| PS___asan_report_store8 => (symaddr Symbols.AsanUbsan.s___asan_report_store8)
| PS___asan_report_store4 => (symaddr Symbols.AsanUbsan.s___asan_report_store4)
| PS___asan_report_store2 => (symaddr Symbols.AsanUbsan.s___asan_report_store2)
| PS___asan_report_load8 => (symaddr Symbols.AsanUbsan.s___asan_report_load8)
| PS___asan_stack_malloc_0 => (symaddr Symbols.AsanUbsan.s___asan_stack_malloc_0)
| PS_rd_u32 => (symaddr Symbols.AsanUbsan.s_rd_u32)
| PS___asan_memmove => (symaddr Symbols.AsanUbsan.s___asan_memmove)
| PS___asan_report_load4 => (symaddr Symbols.AsanUbsan.s___asan_report_load4)
end.
Definition pcap_obj (i : nat) : Z :=
match i with
| 0%nat => (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xb8)%Z)
| 1%nat => (symaddr (Symbols.AsanUbsan.Sec.s_got + 0x60)%Z)
| 2%nat => (symaddr Symbols.AsanUbsan.s_g_file)
| 3%nat => (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z)
| 4%nat => (symaddr Symbols.AsanUbsan.s_g_file_len)
| 5%nat => (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x3414)%Z)
| 6%nat => (symaddr Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput)
| 7%nat => (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xcd8)%Z)
| 8%nat => (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xce0)%Z)
| 9%nat => (symaddr Symbols.AsanUbsan.s____asan_globals_registered)
| 10%nat => (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xd9c3)%Z)
| 11%nat => (symaddr Symbols.AsanUbsan.s_pcap_source_open)
| 12%nat => (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68192)%Z)
| 13%nat => (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x4c4a)%Z)
| 14%nat => (symaddr Symbols.AsanUbsan.s_pcap_source_next)
| 15%nat => (symaddr Symbols.AsanUbsan.s___asan_shadow_memory_dynamic_address)
| 16%nat => (symaddr Symbols.AsanUbsan.s___asan_option_detect_stack_use_after_return)
| _ => 0
end.
Definition pcap_hi (j : nat) : Z :=
match j with
| 0%nat => 0x207a4
| 1%nat => 0x5d37d4
| 2%nat => 0x5d37e0
| 3%nat => 0x99864
| 4%nat => 0x99868
| 5%nat => 0x138c4
| 6%nat => 0x808c8
| 7%nat => 0x5d3984
| 8%nat => 0x5d39a8
| 9%nat => 0x20a00
| 10%nat => 0x20e40
| 11%nat => 0x9906c
| 12%nat => 0x9a188
| 13%nat => 0x9a18c
| 14%nat => 0x9e198
| 15%nat => 0x9a1b8
| 16%nat => 0x9a1bc
| 17%nat => 0x9e1c8
| 18%nat => 0x99224
| 19%nat => 0x99228
| 20%nat => 0x1e284
| 21%nat => 0x81288
| 22%nat => 0x212e8
| 23%nat => 0x9960c
| 24%nat => 0x99610
| 25%nat => 0x15670
| 26%nat => 0x81674
| 27%nat => 0x99c40
| 28%nat => 0x99d6c
| _ => 0
end.
Definition pcap_nobj : nat := 17%nat.
Definition pcap_nhi : nat := 29%nat.
