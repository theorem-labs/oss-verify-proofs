(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACfk.v:169-207 (c8557374ad2e), module paths only; with the section lines it sits in (ACfk.v:55-56, 68-69, 208, 305), the file settings (ACfk.v:26-31), and the Requires it needs. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0l.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0n YA0o.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import YC85.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable B : asyms.
Lemma aj_call_tok : AR_laws tfibsegs B ->
forall W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) spw raw ch1
(KQ : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview tfibsegs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre tfibsegs B STK1 lyc Sc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
SRr tfibsegs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom tfibsegs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK1 (spZ (ms_regs ms)) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved (ms_regs ms) regs2 /\ KQ ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr tfibsegs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal tfibsegs B STK1 (sp0 + o) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved (ms_regs ms) regs2 /\ KQ ly2 S2 W2 regs2 mem2 md2).
Proof.
intros LAWS W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o spw raw ch1 KQ
HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Hrv).
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k (ms_regs ms) STK1 o ch1);
try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub_tok tfibsegs B LAWS tfib_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
End h.
End e.
