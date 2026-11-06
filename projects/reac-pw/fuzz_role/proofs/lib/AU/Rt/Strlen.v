(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of the strlen wrapper of libreac/fuzz_identity.asan (trampoline 0x4218c -> ___interceptor_strlen 0x4221c -> musl strlen 0x94c64 -> the inline range check -> the epilogue), over cgif_file_fuzzer's lib/A/AE6x.v (the memchr wrapper: the entry phase, the lift of a musl msteps walk, the check, the epilogue) and lib/A/AE7d.v (the strnlen wrapper: the 2144-byte frame and its eight saved registers). The walked function is released as proofs/coturn/FuzzStunClient/lib/VAsanIcStrlenWalk.v:819 isl_run at coturn's addresses; this is that walk at fuzz_identity.asan's addresses in this release's engine, and its statement is lib/A/Rt/StrlenDef.v astrlen_realizes (cgif lib/YG0d.v:401-419 astrnlen_realizes without the n bound). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Rt/Strlen.v, with its module paths and module names changed; 15 of its 25 lines of code are new or changed and 495 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_identity/lib/A/Rt/Strlen.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Rt/Strlen.v at origin/ossv/recipes 7cbe5270d908 (donor image sha256 c954b804786c); module paths changed and addresses moved to reac-pw/fuzz_role's ASan build (fuzz_role.asan sha256 614cffc0864c) by port_core.py 1e42da8952ec, cross-checked numeral by numeral with alreloc a5c53bb2bed4 (ledger provenance/reloc/A-Rt-Strlen.tsv). *)
(* libreac/fuzz_identity, build asan: the strlen wrapper's contract, lib/A/Rt/StrlenDef.v astrlen_realizes at
   STRLEN_ENTRY = 0x4218c, from the shared strlen walk lib/A/FMstrlen.v strlen_icpt_srr: port-fm's walk
   (origin/cold/port-fm-rtscan f8664b31b9c, cgif_file_fuzzer coordinates, SL_ENTRY 0x418f0) relocated to
   fuzz_identity.asan (SL_ENTRY 0x4218c). The walk asks the contract's premises plus mconsts_view (the two musl
   constants at 0x10350 and 0x10368), which lib/A/Rt/WrapRoM.v derives from the contract's aro_unowned; the
   post-conditions are the same text. The proof names only the binders of the contract and finds each premise
   by its type, so it does not depend on the order of the premises. *)
(* Modified by Theorem Labs, 2026-10-29: for r-identity's acceptance (cold/h-rw-ide-6-wrapacc), the record class is TfibSyms, not IdentTfibSyms (DECISIONS-LIVE 05:31Z: TfibSyms in both A and B, no --rename), and the core modules are Required by full path at the applied A core's names (lib/A/A*.v, lib/Reusable/YA0m, YE08, YE21). *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/Rt/Strlen.v of this library at d428443238a6 by derive_y.py: module paths lib.A -> lib.AU (A.Axyz -> AU.Yxyz), addresses moved from reac-pw/fuzz_role's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/Rt/Strlen.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.YB1v
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.YF0m
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.YE39.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require FMstrlen.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.Rt Require Import StrlenDef WrapRo WrapRoM.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma SL_ENTRY_eq : FMstrlen.SL_ENTRY = STRLEN_ENTRY. Proof. reflexivity. Qed.
Theorem strlen_icpt_contract : forall B, AR_laws tfibsegs B -> TfibSyms B -> astrlen_realizes tfibsegs B STRLEN_ENTRY.
Proof.
intros B LAWS TB. unfold astrlen_realizes. intros ly S W regs mem md x k. intros.
rewrite <- SL_ENTRY_eq.
apply (FMstrlen.strlen_icpt_srr B LAWS TB ly S W regs mem md x k).
all: first [ assumption | apply (mconsts_of_aro B W mem TB); assumption ].
Qed.
End d.
