From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE2l.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP02 YB1v YE34.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition ff_ranges : list (Z * nat) :=
[ ((symaddr Symbols.AsanUbsan.s___interceptor_strchr), 184%nat); ((symaddr Symbols.AsanUbsan.s___interceptor_fopen), 283%nat); ((symaddr Symbols.AsanUbsan.s___interceptor_fflush), (symwords Symbols.AsanUbsan.s___interceptor_fflush (Symbols.AsanUbsan.s____interceptor_fclose + 0x1ac)%Z)); ((symaddr Symbols.AsanUbsan.s__ZN11__sanitizer11AddrHashMapI25CommonInterceptorMetadataLm31051EE7acquireEPNS2_6HandleE), (symwords Symbols.AsanUbsan.s__ZN11__sanitizer11AddrHashMapI25CommonInterceptorMetadataLm31051EE7acquireEPNS2_6HandleE (Symbols.AsanUbsan.s__ZN11__sanitizer11AddrHashMapI25CommonInterceptorMetadataLm31051EE7releaseEPNS2_6HandleE + 0x38c)%Z)); ((symaddr Symbols.AsanUbsan.s_fdopen), (symwords Symbols.AsanUbsan.s_fdopen (Symbols.AsanUbsan.s___stdio_close + 0x2c)%Z)); ((symaddr Symbols.AsanUbsan.s_fopen), (symwords Symbols.AsanUbsan.s_fopen (Symbols.AsanUbsan.s___fmodeflags + 0xb4)%Z)); ((symaddr Symbols.AsanUbsan.s___fwritex), (symwords Symbols.AsanUbsan.s___fwritex (Symbols.AsanUbsan.s___ofl_add + 0x40)%Z));
((symaddr Symbols.AsanUbsan.s_strchr), (symwords Symbols.AsanUbsan.s_strchr (Symbols.AsanUbsan.s___strchrnul + 0xe0)%Z)); ((symaddr Symbols.AsanUbsan.s___lock), 3%nat); ((symaddr (Symbols.AsanUbsan.s___lock + 0x1f8)%Z), 1%nat); ((symaddr Symbols.AsanUbsan.s___unlock), 3%nat) ].
Definition tbl_ff : ctable := Eval vm_compute in build_ranges ff_ranges tbl_icpt.
Lemma tbl_ff_eq : tbl_ff = build_ranges ff_ranges tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_ff). Qed.
Lemma tbl_ff_ok : table_ok tfibsegs tbl_ff.
Proof.
rewrite tbl_ff_eq. apply build_ranges_ok; [| apply tbl_icpt_ok].
unfold ff_ranges. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_ff_probe :
clookup tbl_ff (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer11AddrHashMapI25CommonInterceptorMetadataLm31051EE7acquireEPNS2_6HandleE) = Some 0xf5010113 /\ clookup tbl_ff (symaddr Symbols.AsanUbsan.s___interceptor_fopen) = Some 0x81010113 /\ clookup tbl_ff (symaddr Symbols.AsanUbsan.s___interceptor_strchr) = Some 0x81010113 /\
clookup tbl_ff (symaddr Symbols.AsanUbsan.s___wrap_malloc) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
