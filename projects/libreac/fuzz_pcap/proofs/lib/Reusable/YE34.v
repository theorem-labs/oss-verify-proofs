From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE34.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
(* Modified by Theorem Labs, 2026-10: icpt_ranges' trampoline row is pcap's own run, measured on the unstripped twin
   c969d83cdd59 of pin 9e66f771f22a: 40 four-byte __wrap_* / __interceptor_trampoline_* functions from __wrap_strlen
   0x415ac to __wrap_sigaction (ends 0x4164c); the relocation kept cgif's 38, which left __wrap_sigaltstack 0x41644 and
   __wrap_sigaction 0x41648 outside (pcap's run has __wrap_fread and __wrap_fmemopen in addition). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP02 YB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Fixpoint build_ranges (rs : list (Z * nat)) (t : ctable) : ctable :=
match rs with [] => t | (lo, n) :: rest => build_ranges rest (build_table tfibsegs lo n t) end.
Lemma build_ranges_ok : forall rs t,
Forall (fun r => 0 <= fst r) rs -> table_ok tfibsegs t -> table_ok tfibsegs (build_ranges rs t).
Proof.
induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.
Definition musl_sel_ranges : list (Z * nat) :=
[ ((symaddr Symbols.AsanUbsan.s_open), (symwords Symbols.AsanUbsan.s_open (Symbols.AsanUbsan.s___syscall_ret + 0x38)%Z)); ((symaddr Symbols.AsanUbsan.s_dprintf), 25%nat); ((symaddr Symbols.AsanUbsan.s___lockfile), (symwords Symbols.AsanUbsan.s___lockfile (Symbols.AsanUbsan.s___unlockfile + 0x60)%Z)); ((symaddr Symbols.AsanUbsan.s___stdio_write), (symwords Symbols.AsanUbsan.s___stdio_write (Symbols.AsanUbsan.s___stdio_exit + 0x1c)%Z)); ((symaddr Symbols.AsanUbsan.s_vfprintf), (symwords Symbols.AsanUbsan.s_vfprintf (Symbols.AsanUbsan.s_pad + 0xd4)%Z)); ((symaddr Symbols.AsanUbsan.s_vprintf), (symwords Symbols.AsanUbsan.s_vprintf (Symbols.AsanUbsan.s_vsnprintf + 0xa0)%Z));
((symaddr Symbols.AsanUbsan.s_sccp), (symwords Symbols.AsanUbsan.s_sccp (Symbols.AsanUbsan.s___syscall_cp + 0x4)%Z)); ((symaddr Symbols.AsanUbsan.s_close), (symwords Symbols.AsanUbsan.s_close (Symbols.AsanUbsan.s_read + 0x34)%Z)) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ ((symaddr Symbols.AsanUbsan.s___wrap_strlen), (symwords Symbols.AsanUbsan.s___wrap_strlen (Symbols.AsanUbsan.s___interceptor_trampoline_sigaction + 0x4)%Z));  ((symaddr Symbols.AsanUbsan.s___interceptor_strnlen), 165%nat); ((symaddr Symbols.AsanUbsan.s__Z23MemcmpInterceptorCommonPvPFiPKvS1_mES1_S1_m), 549%nat); ((symaddr Symbols.AsanUbsan.s___interceptor_memcmp), (symwords Symbols.AsanUbsan.s___interceptor_memcmp (Symbols.AsanUbsan.s____interceptor_bcmp + 0xbc)%Z)); ((symaddr Symbols.AsanUbsan.s___interceptor_memchr), 180%nat);
((symaddr Symbols.AsanUbsan.s___interceptor_read), 156%nat); ((symaddr Symbols.AsanUbsan.s___interceptor_fwrite), 157%nat); ((symaddr Symbols.AsanUbsan.s___interceptor_vprintf), (symwords Symbols.AsanUbsan.s___interceptor_vprintf (Symbols.AsanUbsan.s__ZL13printf_commonPvPKcS_ + 0xac8)%Z)); ((symaddr Symbols.AsanUbsan.s___interceptor_vfprintf), 45%nat); ((symaddr Symbols.AsanUbsan.s___interceptor_fprintf), 54%nat);
((symaddr Symbols.AsanUbsan.s__ZL21format_get_value_sizecPKcb), 102%nat); ((symaddr Symbols.AsanUbsan.s___wrap_memset), (symwords Symbols.AsanUbsan.s___wrap_memset (Symbols.AsanUbsan.s___asan_memset + 0x240)%Z)); ((symaddr Symbols.AsanUbsan.s___asan_memmove), 220%nat); ((symaddr Symbols.AsanUbsan.s___interceptor_memset), (symwords Symbols.AsanUbsan.s___interceptor_memset (Symbols.AsanUbsan.s____interceptor_memcpy + 0x5f0)%Z)); ((symaddr (Symbols.AsanUbsan.s__ZN6__asan12PoisonShadowEmmh + 0x4fc)%Z), 79%nat); ((symaddr Symbols.AsanUbsan.s___asan_region_is_poisoned), 209%nat); ((symaddr Symbols.AsanUbsan.s__ZN6__asan10AsanInitedEv), 6%nat);
((symaddr Symbols.AsanUbsan.s__ZN6__asan18TryAsanInitFromRtlEv), 40%nat);  ((symaddr Symbols.AsanUbsan.s__ZN11__sanitizer15internal_strchrEPKci), 13%nat);  ((symaddr Symbols.AsanUbsan.s__ZN11__sanitizer15internal_strlenEPKc), 7%nat);   ((symaddr Symbols.AsanUbsan.s__ZN11__sanitizer16internal_strnlenEPKcm), 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt (symaddr Symbols.AsanUbsan.s___interceptor_memcpy) = Some 0x81010113 /\ clookup tbl_icpt (symaddr Symbols.AsanUbsan.s_memcpy) = None /\ clookup tbl_icpt (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer11mem_is_zeroEPKcm) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
