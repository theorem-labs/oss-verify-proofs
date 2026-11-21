(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1w.v (theorem-labs/oss-verify-proofs@6b32741d849a), with its module paths changed, names TfibSyms -> PcapSyms and its addresses moved to libreac/fuzz_pcap's ASan build. lib_site_x (donor AD1w.v:80-105) RESTATED over pcap's program contract (lib/A/Prog/PcapEntry.v tfib_lib_post_x, porter a Theorem Labs lane rulings 1-3): the callee's journal is W_journal.v's ajournal_gx at the harness globals G_HARNESS (PcapEntry.v:36) with no out window (XO = 0, OUT = []), in place of cgif's YCbq.ajournal, and the callee's output is PWalk.OUT pl (PcapEntry.v:73) in place of cgif's []; FINV is lib/A/AD1u.v's, over pcap's source pcap_KS. The sink head is the Section's SK (no global instance; PcapSinkHeads.v). The fd-names conjunct (Namei.fd_names_path ... YI16.sink_path = false, donor AD1w.v:89, :101, :203) is carried as the donor carries it: sink_path is cgif's literal, inert (no open of it); HOOK: a Theorem Labs lane's image-generic inertness lemma (a working branch lib/Reusable, cited by path once it lands) discharges it. rule 24: no function proved anew. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1w.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.BudgetWit.AW Require Import YA0n_w YA0e_w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0k YG0f YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1v_w AD2h_w AD2f_w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK00 YI00 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.BudgetWit.AW Require Import AD1u_w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Definition STDOUT_MUT (a : Z) : Prop := (STDOUT_LO <= a < STDOUT_HI) \/ (SOBUF_LO <= a < SOBUF_HI).
Definition stdout_img (H : word -> bool) (m : word -> option byte) : Prop :=
forall a, STDOUT_LO <= a < STDOUT_HI -> aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Definition xst_frame_tfa : Prop :=
forall k (H H' : word -> bool) (m m' : word -> option byte),
xst k H m -> (forall a, STDOUT_MUT a -> aview tfibsegs H' m' a = aview tfibsegs H m a) -> xst k H' m'.
End c.
