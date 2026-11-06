(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YG0p.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YC4a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC85.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma aj_callS : forall W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) spw raw ch1
(K : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre segs B STK1 lyc Sc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
SRr segs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK1 (spZ (ms_regs ms)) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal segs B STK1 (sp0 + o) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o spw raw ch1 K
HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _).
unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. lia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k (ms_regs ms) STK1 o ch1);
try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub_tok segs B LAWS segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
End c.
End b.
