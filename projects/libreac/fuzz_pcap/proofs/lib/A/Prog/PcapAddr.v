(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The addresses fuzz_pcap.asan gives the listing's names, objects and
   auipc values. The objects past the
   ones the slots build are the cells the walks read through a GOT word:
   __asan_shadow_memory_dynamic_address (the shadow base) and
   __asan_option_detect_stack_use_after_return. *)
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSyms.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition pcap_text : Z := Eval compute in Symbols.Asan.s_libreac_fuzz_fopen.  (* the listing's first function *)
Definition pcap_sigma (s : psym) : Z :=
match s with
| PS___interceptor_trampoline_strcmp => (symaddr Symbols.Asan.s___wrap_strcmp)
| PS___interceptor_trampoline_fopen => (symaddr Symbols.Asan.s___wrap_fopen)
| PS___interceptor_trampoline_fmemopen => (symaddr Symbols.Asan.s___wrap_fmemopen)
| PS___asan_stack_malloc_1 => (symaddr Symbols.Asan.s___asan_stack_malloc_1)
| PS___interceptor_trampoline_malloc => (symaddr Symbols.Asan.s___wrap_malloc)
| PS___asan_memcpy => (symaddr Symbols.Asan.s___asan_memcpy)
| PS___asan_memset => (symaddr Symbols.Asan.s___asan_memset)
| PS_pcap_source_open => (symaddr Symbols.Asan.s_pcap_source_open)
| PS___interceptor_trampoline_free => (symaddr Symbols.Asan.s___wrap_free)
| PS_pcap_source_next => (symaddr Symbols.Asan.s_pcap_source_next)
| PS___interceptor_trampoline_bcmp => (symaddr Symbols.Asan.s___wrap_bcmp)
| PS___asan_report_load1 => (symaddr Symbols.Asan.s___asan_report_load1)
| PS_pcap_source_close => (symaddr Symbols.Asan.s_pcap_source_close)
| PS___asan_handle_no_return => (symaddr Symbols.Asan.s___asan_handle_no_return)
| PS_abort => (symaddr Symbols.Asan.s_abort)
| PS___asan_init => (symaddr Symbols.Asan.s___asan_init)
| PS___asan_version_mismatch_check_v8 => (symaddr Symbols.Asan.s___asan_version_mismatch_check_v8)
| PS___asan_register_elf_globals => (symaddr Symbols.Asan.s___asan_register_elf_globals)
| PS___asan_unregister_elf_globals => (symaddr Symbols.Asan.s___asan_unregister_elf_globals)
| PS_libreac_fuzz_fopen => (symaddr Symbols.Asan.s_libreac_fuzz_fopen)
| PS___interceptor_trampoline_fread => (symaddr Symbols.Asan.s___wrap_fread)
| PS___interceptor_trampoline_fclose => (symaddr Symbols.Asan.s___wrap_fclose)
| PS___asan_report_store8 => (symaddr Symbols.Asan.s___asan_report_store8)
| PS___asan_report_store4 => (symaddr Symbols.Asan.s___asan_report_store4)
| PS___asan_report_store2 => (symaddr Symbols.Asan.s___asan_report_store2)
| PS___asan_report_load8 => (symaddr Symbols.Asan.s___asan_report_load8)
| PS___asan_stack_malloc_0 => (symaddr Symbols.Asan.s___asan_stack_malloc_0)
| PS___asan_memmove => (symaddr Symbols.Asan.s___asan_memmove)
| PS___asan_report_load4 => (symaddr Symbols.Asan.s___asan_report_load4)
end.
Definition pcap_obj (i : nat) : Z :=
match i with
| 0%nat => (symaddr (Symbols.Asan.Sec.s_got + 0xb8)%Z)
| 1%nat => (symaddr (Symbols.Asan.Sec.s_got + 0x60)%Z)
| 2%nat => (symaddr Symbols.Asan.s_g_file)
| 3%nat => (symaddr (Symbols.Asan.Sec.s_rodata + 68128)%Z)
| 4%nat => (symaddr Symbols.Asan.s_g_file_len)
| 5%nat => (symaddr (Symbols.Asan.Sec.s_rodata + 0x3414)%Z)
| 6%nat => (symaddr Symbols.Asan.s_LLVMFuzzerTestOneInput)
| 7%nat => (symaddr (Symbols.Asan.Sec.s_got + 0xcd8)%Z)
| 8%nat => (symaddr (Symbols.Asan.Sec.s_got + 0xce0)%Z)
| 9%nat => (symaddr Symbols.Asan.s____asan_globals_registered)
| 10%nat => (symaddr (Symbols.Asan.Sec.s_rodata + 0xd9c3)%Z)
| 11%nat => (symaddr Symbols.Asan.s_pcap_source_open)
| 12%nat => (symaddr (Symbols.Asan.Sec.s_rodata + 68192)%Z)
| 13%nat => (symaddr (Symbols.Asan.Sec.s_rodata + 0x4c4a)%Z)
| 14%nat => (symaddr Symbols.Asan.s_pcap_source_next)
| 15%nat => (symaddr Symbols.Asan.s___asan_shadow_memory_dynamic_address)
| 16%nat => (symaddr Symbols.Asan.s___asan_option_detect_stack_use_after_return)
| _ => 0
end.
Definition pcap_hi (j : nat) : Z :=
match j with
| 0%nat => 0x20754
| 1%nat => 0x5d3784
| 2%nat => 0x5d3790
| 3%nat => 0x99814
| 4%nat => 0x99818
| 5%nat => 0x13874
| 6%nat => 0x80878
| 7%nat => 0x5d3924
| 8%nat => 0x5d3928
| 9%nat => 0x20990
| 10%nat => 0x210b8
| 11%nat => 0x9a404
| 12%nat => 0x9a408
| 13%nat => 0x9e414
| 14%nat => 0x9a434
| 15%nat => 0x9a438
| 16%nat => 0x9e444
| 17%nat => 0x994a0
| 18%nat => 0x994a4
| 19%nat => 0x1d500
| 20%nat => 0x81504
| 21%nat => 0x20564
| 22%nat => 0x99870
| 23%nat => 0x99874
| 24%nat => 0x148cc
| 25%nat => 0x818d0
| 26%nat => 0x99ea0
| _ => 0
end.
Definition pcap_nobj : nat := 17%nat.
Definition pcap_nhi : nat := 27%nat.
