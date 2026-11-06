(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v for libreac/fuzz_grant's program walk: the listing's names are gsym, PALib names fuzz_grant.asan's objects and the wrappers' 4-byte jumps, and fuzz_grant's image bound; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: taken by path from port-grant's copy (origin/cold/pg-prog cb6eddd4032, proofs/libreac/fuzz_grant/lib/A/Prog/GrantPaLib.v) for libreac/fuzz_decode's
   program walk: module paths and the listing's names (gsym -> dsym) changed; PALib names fuzz_decode.asan's objects
   of lib/A/Prog/DecodeAddr.v (the shadow-base GOT slot is object 1 and its cell object 13, the side-stack flag's GOT
   slot object 0 and its cell object 14); the image bounds are lib/Reusable/YImgTop.v's IMG_LO / IMG_TOP, which
   blk_off_imgP reads through IMG_LO_val / IMG_TOP_val (lia cannot see into the computed definitions). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnTransportPaLib.v; 11 of its 34 lines of code are new or changed and 479 lines of the source are left out. *)
(* TransportGRunA: the symbolic runs of lib/A/Prog/PaShadow.v taken over the G journal (lib/A/W_journalG.v
   ajournal_gx G XO OUT), at image A's listing: W_journalG.v's run chain SRr_run_pi_tok_AJX / SRr_run_to_pi_tok_AJX
   instantiated at the listing's PAListing / PAImg (lib/A/Prog/DgnTransportPa.v), as libreac/fuzz_pcap's
   lib/A/W_journal.v Section g states them. It stands beside lib/A/Prog/DgnTransportPaLib.v's paj_run / paj_run_to
   over the donor journal. Image A only: PAListing and PAImg are classes over image A's listing symbols (tsym).
   - paj_run_x G HG XO OUT: a run of sym_runN_pi_tok from a state whose journal is ajournal_gx G XO OUT; the write
     obligation it leaves is W_journalG.v awr_ok_x (an awr_byte of the walk's own window, a byte of G, or an out cell).
   - paj_run_to_x G HG XO OUT: the same for sym_run_toN_pi_tok (a run to a stop pc). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportList DgnTransportPa.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {L : ptable tsym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Definition paj_run_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
  SRr_run_pi_tok_AJX tsym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
  pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq G HG XO OUT.
Definition paj_run_to_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
  SRr_run_to_pi_tok_AJX tsym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
  pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq G HG XO OUT.
End g.
