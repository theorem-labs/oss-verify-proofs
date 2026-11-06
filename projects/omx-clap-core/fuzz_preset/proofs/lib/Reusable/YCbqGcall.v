(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, cgif's program-call rule aj_call and its stack-region
   keep region_kept_stack_sub (proofs/cgif/cgif_file_fuzzer/lib/YCbq.v:1845-1899, origin/ossv/recipes c8557374ad2e)
   restated over YCbqG.v's journal ajournal_x (allocator invariant a parameter ARx, ghost head set Hp after S, Hpc after
   Sc, program statics PST). One change in aj_call_x: the callee's post is YCbqG.v's apost_base_x itself, so the callee's
   event count is the existential of apost_base_x instead of a fixed EV1. Generic: no image class, no address, no
   ledger. *)
(* Modified by Theorem Labs, 2026-10: the rules over a world relation R (suffix R). A free or realloc of a live block
   can hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle with its journal at
   that relation (YCbqG.v ajournal_xR). aj_call_xR / aj_call_x_spR / aj_call_xFR / aj_call_xF_spR take R and its two
   laws (reflexive, transitive) first, then the plain rule's binders: the caller's journal, the callee's post
   (YCbqG.v apost_base_xR / apost_base_xFR; a callee whose text concludes the plain post lifts it by
   apost_base_x_R_lift / apost_base_xF_R_lift) and the conclusion are at R; the composition is YCbqG.v's
   ajournal_x_subR. region_kept_stack_sub_xR reads two journals at R. Each plain rule is its R form at wle (wle_refl /
   wle_trans); its statement is unchanged. The disjunctive rules aj_call_x_or / aj_call_xF_or are removed: no code
   outside this file used them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YL05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Local Notation AJ := (ajournal_x segs B PST ARx).
Local Notation AJR R := (ajournal_xR segs B PST ARx R).
(* region_kept_stack_sub_x below, the two journals at a world relation R *)
Lemma region_kept_stack_sub_xR : forall (R : world segs -> world segs -> Prop),
forall E STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 n lo hi wlo whi cs sp
STK sp0 FP ly S Hp W0 mem md own k,
AJR R STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
AJR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
bv_unsigned (ew E n) = sp -> sp1 <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros R E STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 n lo hi wlo whi cs sp STK sp0 FP ly S Hp W0 mem md own k
HJ1 HJ Hn Hsp1 Hlo Hhi Hw1 Hw2.
pose proof (ajxR_hi HJ1) as G1.
pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _). pose proof (ajxR_qt HJ) as HQT.
pose proof asan_consts as (C1 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply G1; zlia.
- intros _. apply (apresent_writable segs). apply Hpres. zlia.
Qed.
(* cgif YCbq.v:1884-1899 (origin/ossv/recipes) over ajournal_x: a caller's stack region above the callee's window is
   kept across a call whose journal is HJ1, inside the caller's journal HJ. *)
Lemma region_kept_stack_sub_x : forall E STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 n lo hi wlo whi cs sp
STK sp0 FP ly S Hp W0 mem md own k,
AJ STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
AJ STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
bv_unsigned (ew E n) = sp -> sp1 <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof. exact (region_kept_stack_sub_xR (@wle segs)). Qed.
Section l.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
(* aj_call_x below over a world relation R: R and its two laws first; the caller's journal, the callee's post and the
   conclusion at R. *)
Lemma aj_call_xR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) spw raw ch1
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
 SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
   (apost_base_xR segs B PST ARx R STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
SRrG segs R W (mkCfg ms mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
  AJR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
  AJR R STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o spw raw ch1 Q
HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (ajxR_stk HJ) as (_ & _ & Hceil & Hslo & Hshi & H47 & _). pose proof (ajxR_qt HJ) as HQT.
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply (SRrG_mono segs R).
{ apply Hcallee. eapply (afn_pre_x_atR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k
(ms_regs ms) STK1 o ch1); try eassumption.
- rewrite Hra. exact Hraw.
- unfold raZ. rewrite Hra. exact Hra4.
- rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own). eapply (ajournal_x_subR segs B PST ARx LAWS segs_low R Rt); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.
(* cgif YCbq.v:1845-1883 (origin/ossv/recipes) over ajournal_x: a program call from a state the journal HJ describes.
   The callee entry pre is YCbqG.v's afn_pre_x (built by afn_pre_x_at), the callee's text concludes in apost_base_x at
   the call's registers, and its journal composes with the caller's by ajournal_x_sub. *)
Lemma aj_call_x : forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) spw raw ch1
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
 SRr segs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
   (apost_base_x segs B PST ARx STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
(* the callee's footprint, BY THE NAME YCbqG.v's ajournal_x_sub takes (h-hpreset-7 9052c7a7d74 fp_sub_x :688-691:
   the caller's footprint, a temporary block, a slot of a frame the caller took since its entry, or a byte of the
   caller's own stack window; the window case carries no alloc_ceiling bound, the caller's astk_ok gives it) *)
fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
SRr segs W (mkCfg ms mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
  AJ STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
  AJ STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* aj_call_x_sp below over a world relation R *)
Lemma aj_call_x_spR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
spZ (ms_regs ms) = sp0 + o ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
 SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
   (apost_base_xR segs B PST ARx R STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
SRrG segs R W (mkCfg ms mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
  AJR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
  AJR R STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 Q
HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply (SRrG_mono segs R).
{ apply Hcallee. eapply (afn_pre_x_atR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k
(ms_regs ms) STK1 o ch1); try eassumption.
- rewrite Hra. exact Hraw.
- unfold raZ. rewrite Hra. exact Hra4.
- rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own). eapply (ajournal_x_subR segs B PST ARx LAWS segs_low R Rt); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.
(* aj_call_x for a caller outside this section: the stack-pointer premise is spZ (ms_regs ms) = sp0 + o (the fact the
   proof of aj_call_x derives from its three premises getr 2 = sv_denot E (SOff 2 o), ew E 2 = spw,
   bv_unsigned spw = sp0; the binder spw goes with them); every other premise and the conclusion are those of aj_call_x. *)
Lemma aj_call_x_sp : forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
spZ (ms_regs ms) = sp0 + o ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
 SRr segs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
   (apost_base_x segs B PST ARx STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
SRr segs W (mkCfg ms mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
  AJ STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
  AJ STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_x_spR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* aj_call_xF below over a world relation R *)
Lemma aj_call_xFR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) spw raw ch1
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
 SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
   (apost_base_xFR segs B PST ARx R STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
SRrG segs R W (mkCfg ms mdc)
 (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
  frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
  AJR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
  AJR R STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o spw raw ch1 Q
HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (ajxR_stk HJ) as (_ & _ & Hceil & Hslo & Hshi & H47 & _). pose proof (ajxR_qt HJ) as HQT.
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply (SRrG_mono segs R).
{ apply Hcallee. eapply (afn_pre_x_atR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k
(ms_regs ms) STK1 o ch1); try eassumption.
- rewrite Hra. exact Hraw.
- unfold raZ. rewrite Hra. exact Hra4.
- rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ1 & HP & HQ).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|].
split; [exact HFZ|]. split; [exact HFK|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own). eapply (ajournal_x_subR segs B PST ARx LAWS segs_low R Rt); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.
(* aj_call_x for a callee whose text concludes in YCbqG.v's apost_base_xF (it may change the floating-point state: it
   reaches musl strtod), cgif_rgb lib/YCcc.v:20-58 aj_callF over ajournal_x. The continuation runs at the callee's
   float state fx' (frm back to 0, fs0-fs11 kept); st_ok_pi_xfx below moves a symbolic state to it. *)
Lemma aj_call_xF : forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) spw raw ch1
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
 SRr segs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
   (apost_base_xF segs B PST ARx STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
SRr segs W (mkCfg ms mdc)
 (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
  frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
  AJ STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
  AJ STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xFR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* aj_call_xF_sp below over a world relation R *)
Lemma aj_call_xF_spR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
spZ (ms_regs ms) = sp0 + o ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
 SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
   (apost_base_xFR segs B PST ARx R STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
SRrG segs R W (mkCfg ms mdc)
 (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
  frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
  AJR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
  AJR R STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 Q
HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply (SRrG_mono segs R).
{ apply Hcallee. eapply (afn_pre_x_atR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k
(ms_regs ms) STK1 o ch1); try eassumption.
- rewrite Hra. exact Hraw.
- unfold raZ. rewrite Hra. exact Hra4.
- rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ1 & HP & HQ).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|].
split; [exact HFZ|]. split; [exact HFK|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own). eapply (ajournal_x_subR segs B PST ARx LAWS segs_low R Rt); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.
(* aj_call_xF with aj_call_x_sp's stack-pointer premise spZ (ms_regs ms) = sp0 + o; every other premise and the
   conclusion are those of aj_call_xF. *)
Lemma aj_call_xF_sp : forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
spZ (ms_regs ms) = sp0 + o ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
 SRr segs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
   (apost_base_xF segs B PST ARx STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
SRr segs W (mkCfg ms mdc)
 (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
  frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
  AJ STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
  AJ STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xF_spR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End l.
End x.
(* the symbolic-state facts of a machine state built by mkst do not read the floating-point state: a walk continuing
   after a float-changing call (aj_call_xF) moves its st_ok to the callee's fx' (cgif_rgb lib/YCcc.v:61-67) *)
Lemma st_ok_restrict_xfx : forall (fx1 fx2 : YK11.FPState) segs E ss (H : word -> bool) regs pc mem,
@st_ok segs fx1 E ss (restrict H (@YK11.mkst fx1 regs pc mem (YK11.seg_rom segs))) ->
@st_ok segs fx2 E ss (restrict H (@YK11.mkst fx2 regs pc mem (YK11.seg_rom segs))).
Proof.
intros fx1 fx2 segs E ss H regs pc mem HS.
rewrite (@restrict_mkst_fx fx2). rewrite (@restrict_mkst_fx fx1) in HS. exact (YL05.st_ok_xfx fx1 fx2 segs E ss regs pc _ HS).
Qed.
