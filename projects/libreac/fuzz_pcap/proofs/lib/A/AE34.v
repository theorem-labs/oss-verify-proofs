From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v.
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
[ ((symaddr Symbols.Asan.s_open), (symwords Symbols.Asan.s_open (Symbols.Asan.s___syscall_ret + 0x38)%Z)); ((symaddr Symbols.Asan.s_dprintf), 25%nat); ((symaddr Symbols.Asan.s___lockfile), (symwords Symbols.Asan.s___lockfile (Symbols.Asan.s___unlockfile + 0x60)%Z)); ((symaddr Symbols.Asan.s___stdio_write), (symwords Symbols.Asan.s___stdio_write (Symbols.Asan.s___stdio_exit + 0x1c)%Z)); ((symaddr Symbols.Asan.s_vfprintf), (symwords Symbols.Asan.s_vfprintf (Symbols.Asan.s_pad + 0xd4)%Z)); ((symaddr Symbols.Asan.s_vprintf), (symwords Symbols.Asan.s_vprintf (Symbols.Asan.s_vsnprintf + 0xa0)%Z));
((symaddr Symbols.Asan.s_sccp), (symwords Symbols.Asan.s_sccp (Symbols.Asan.s___syscall_cp + 0x4)%Z)); ((symaddr Symbols.Asan.s_close), (symwords Symbols.Asan.s_close (Symbols.Asan.s_read + 0x34)%Z)) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ ((symaddr Symbols.Asan.s___wrap_strlen), (symwords Symbols.Asan.s___wrap_strlen (Symbols.Asan.s___interceptor_trampoline_sigaction + 0x4)%Z)); (* pcap's own __wrap_* trampoline run, __wrap_strlen .. __wrap_sigaction (cgif's run lacks __wrap_fread, __wrap_fmemopen) *)  ((symaddr Symbols.Asan.s___interceptor_strnlen), 165%nat); ((symaddr Symbols.Asan.s__Z23MemcmpInterceptorCommonPvPFiPKvS1_mES1_S1_m), 549%nat); ((symaddr Symbols.Asan.s___interceptor_memcmp), (symwords Symbols.Asan.s___interceptor_memcmp (Symbols.Asan.s____interceptor_bcmp + 0xbc)%Z)); ((symaddr Symbols.Asan.s___interceptor_memchr), 180%nat);
((symaddr Symbols.Asan.s___interceptor_read), 156%nat); ((symaddr Symbols.Asan.s___interceptor_fwrite), 157%nat); ((symaddr Symbols.Asan.s___interceptor_vprintf), (symwords Symbols.Asan.s___interceptor_vprintf (Symbols.Asan.s__ZL13printf_commonPvPKcS_ + 0xac8)%Z)); ((symaddr Symbols.Asan.s___interceptor_vfprintf), 45%nat); ((symaddr Symbols.Asan.s___interceptor_fprintf), 54%nat);
((symaddr Symbols.Asan.s__ZL21format_get_value_sizecPKcb), 102%nat); ((symaddr Symbols.Asan.s___wrap_memset), (symwords Symbols.Asan.s___wrap_memset (Symbols.Asan.s___asan_memset + 0x240)%Z)); ((symaddr Symbols.Asan.s___asan_memmove), 220%nat); ((symaddr Symbols.Asan.s___interceptor_memset), (symwords Symbols.Asan.s___interceptor_memset (Symbols.Asan.s____interceptor_memcpy + 0x5f0)%Z)); ((symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x4fc)%Z), 79%nat); ((symaddr Symbols.Asan.s___asan_region_is_poisoned), 209%nat); ((symaddr Symbols.Asan.s__ZN6__asan10AsanInitedEv), 6%nat);
((symaddr Symbols.Asan.s__ZN6__asan18TryAsanInitFromRtlEv), 40%nat);  ((symaddr Symbols.Asan.s__ZN11__sanitizer15internal_strchrEPKci), 13%nat);  ((symaddr Symbols.Asan.s__ZN11__sanitizer15internal_strlenEPKc), 7%nat);   ((symaddr Symbols.Asan.s__ZN11__sanitizer16internal_strnlenEPKcm), 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt (symaddr Symbols.Asan.s___interceptor_memcpy) = Some 0x81010113 /\ clookup tbl_icpt (symaddr Symbols.Asan.s_memcpy) = None /\ clookup tbl_icpt (symaddr Symbols.Asan.s__ZN11__sanitizer11mem_is_zeroEPKcm) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
