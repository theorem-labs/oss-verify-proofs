(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Written by Theorem Labs, 2026-10 (a Theorem Labs lane), for libreac/fuzz_pcap's v1.9.0 ASan build. *)
(* The STRCMP bridge (a Theorem Labs lane's owner map 11:3xZ, row C): the literal-instance contract of the strcmp interceptor,
   lib/A/Rt/StrcmpDef.v's astrcmp_lit_realizes (proved by lib/A/Rt/StrcmpIcpt.v's strcmp_lit_contract), gives
   lib/A/Prog/PcapFuzzFopenG.v's astrcmp_path_at, the form libreac_fuzz_fopen's walk takes at its one strcmp call
   (PcapEntryFinal.v / PcapEntryInst.v, hypothesis STRCMP). The two state the same call: a0 = a1 = the "<fuzz-input>"
   literal, 13 bytes with the NUL; the same result 0 and the same post, with the same window [sp - ESTACK, sp).
   astrcmp_path_at is stated for any segments, read-only-image fact, entry pc and literal address, so the bridge
   takes the four as equations / an implication; the instance gives them from its listing (SEGSp = tfibsegs, the
   strcmp trampoline's pc = SM_ENTRY = 0x41564, object FO_PATH's address = A_FUZZ_PATH = 0x20d00, ROI -> ro_img). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t YCe5.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y AE3i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN32 YG0q YN01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Rt Require Import StrcmpDef StrcmpIcpt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapFuzzFopenG.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* astrcmp_lit_realizes B at its one instance (A_FUZZ_PATH, A_FUZZ_PATH, 0) is astrcmp_path_at at tfibsegs, ro_img,
   SM_ENTRY and A_FUZZ_PATH: the premises match one for one (13 = length FUZZ_PATH_BYTES + 1), and astrcmp_post at
   result 0 is astrcmp_path_at's post. *)
Lemma astrcmp_path_of_lit : forall B, astrcmp_lit_realizes B ->
  PcapFuzzFopenG.astrcmp_path_at tfibsegs B ro_img SM_ENTRY A_FUZZ_PATH.
Proof.
intros B H ly S W regs mem md HPRE G10 G11 HRO HRA HHULL.
exact (H A_FUZZ_PATH A_FUZZ_PATH 0 (or_introl eq_refl) ly S W regs mem md HPRE G10 G11 HRO HRA HHULL HRA HHULL).
Qed.

(* The bridge as the instance takes it: any segments, read-only-image fact, pc and address that the listing shows to
   be tfibsegs, one that implies ro_img, SM_ENTRY and A_FUZZ_PATH. *)
Lemma astrcmp_path_at_inst : forall B segs (ROI : (word -> option byte) -> Prop) pc x,
  astrcmp_lit_realizes B ->
  segs = tfibsegs -> (forall m, ROI m -> ro_img m) -> pc = SM_ENTRY -> x = A_FUZZ_PATH ->
  PcapFuzzFopenG.astrcmp_path_at segs B ROI pc x.
Proof.
intros B segs ROI pc x H Hs HROI Hpc Hx. subst segs pc x.
intros ly S W regs mem md HPRE G10 G11 HR HRA HHULL.
exact (astrcmp_path_of_lit B H ly S W regs mem md HPRE G10 G11 (HROI _ HR) HRA HHULL).
Qed.

(* With the proof of the contract (StrcmpIcpt.v's strcmp_lit_contract): what the instance's STRCMP hypothesis needs
   from this side, at every FPState, from AR_laws tfibsegs B and PcapSyms B. *)
Lemma astrcmp_path_at_of_syms : forall B segs (ROI : (word -> option byte) -> Prop) pc x,
  AR_laws tfibsegs B -> PcapSyms B ->
  segs = tfibsegs -> (forall m, ROI m -> ro_img m) -> pc = SM_ENTRY -> x = A_FUZZ_PATH ->
  PcapFuzzFopenG.astrcmp_path_at segs B ROI pc x.
Proof.
intros B segs ROI pc x LAWS TB. apply astrcmp_path_at_inst. exact (strcmp_lit_contract B LAWS TB).
Qed.

End s.
