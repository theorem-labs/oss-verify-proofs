(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: region_kept_tcj_stack and region_kept_tcj_frame are the text of lib/A/ACem.v's
   region_kept_ownframe_aj (copied there from projects/libreac/fuzz_knock/proofs/lib/A/ACem.v) with the call's acall_kept
   replaced by a callee's tcj_kept (lib/A/Prog/CodecCJ.v), cpw_apresent_of_writable that of lib/A/AE7f.v's
   apresent_of_writable; the re-seat in cpw_call_reseat and cpw_rebase is the text of lib/A/AWalkFw2.v's reseatL (copied
   there from projects/libreac/fuzz_knock/proofs/lib/A/AWalkFw2.v) with the environment equation kept for env_agree,
   cpw_kept_std that of lib/A/AWalkFw1.v's aconstsF with the region_kept_val cases of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgMain3.v:186-194, and cpw_leaf that of lib/A/Prog/CPgWalk.v's cw_leaf with the
   state's layout, astate and model taken through the calls' chain; for libdiginet/fuzz_codec's ASan build (image A).
   cpw_call, cpw_entry, cpw_kept_run, cpw_io, cpw_keep and cpw_sp_off are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalkCall.v, with its module paths and module names changed; 107 of its 140 lines of code are new or changed and 245 lines of the source are left out. *)
(* A tail call of one of codec's own functions from an image-B walk, through the callee's contract.
   At image B diginet_strip_leds_encode and diginet_counter_leds_encode restore ra and sp and jump to
   leds_encode (`j`, no `jal`): the callee returns straight to the walk's caller, so its post, taken at the
   jump state, must be the walk's post.
   - tl_post / tl_call: at the callee's entry (pc = the callee's address, ra and sp those of the walk's entry,
     the callee-saved registers kept), the callee's cdc_post instance gives the walk's cdc_post: the walk's own
     writes lie in its window [sp - T, sp) or its write set (the kept fact over the walk's runs, made into a
     tcj_kept by cw_tcj_of_kept) and compose with the callee's tcj_kept (cw_kept_cj); its window T1 lies inside
     the walk's T; its result R1 implies the walk's R.
   - tl_cdst_kept, tl_garr8_kept, tl_pers_kept, tl_out_kept: the callee's premises at the jump state, from the
     walk's premises at its entry over memory that keeps every byte outside [lo, hi). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkKeptU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.

(* the callee's post, entered by a tail jump at the walk's state (memd, mdd, regsd: same ra and sp as the
   walk's entry, the callee-saved registers kept), is the walk's post *)
Lemma tl_post : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k regs T
(Er : Z -> Prop) (R : world tfibsegs -> (word -> option byte) -> bvmap 5 word -> Prop)
memd mdd regsd T1 (R1 : world tfibsegs -> (word -> option byte) -> bvmap 5 word -> Prop) W2 c2,
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memd mdd k ->
same_io mdc mdd ->
getr regsd 1 = getr regs 1 -> aregs_preserved regs regsd -> spZ regsd = spZ regs ->
alloc_ceiling <= spZ regs - T -> spZ regs <= 2 ^ 47 -> sp0 - STK <= spZ regs - T -> spZ regs <= sp0 ->
0 <= T1 <= T ->
(forall a, Er a -> in_img tfibsegs a -> False) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T <= a < spZ regs) -> ~ Er a ->
  aview tfibsegs (w_H W) memd a = aview tfibsegs (w_H W) memc a) ->
(forall W3 mem3 regs3, R1 W3 mem3 regs3 -> R W3 mem3 regs3) ->
cdc_post tfibsegs B MT STK sp0 FP ly S W0 mem0 md0 own k regsd T1 Er lyc Sc W memd mdd R1 W2 c2 ->
cdc_post tfibsegs B MT STK sp0 FP ly S W0 mem0 md0 own k regs T Er lyc Sc W memc mdc R W2 c2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T Er R memd mdd regsd T1 R1 W2 c2
  HJ0 HJ Hio Hra Hpr Hsp Hce H47 Hwlo Hwhi HT HEimg KE HR
  (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & HP2 & Hfr & HPerm & HIO & HMO & KT2 & HR2).
exists ly2, S2, regs2, mem2, md2.
split; [rewrite Hc, Hra; reflexivity|].
split; [exact HJ2|].
split; [intros r Hr; rewrite (HP2 r Hr); exact (Hpr r Hr)|].
split; [exact Hfr|]. split; [exact HPerm|].
split; [exact (same_io_trans _ _ _ Hio HIO)|].
split; [exact HMO|].
split; [|exact (HR _ _ _ HR2)].
rewrite Hsp in KT2.
assert (KT : tcj_kept tfibsegs B T lyc Sc W memc W memd (spZ regs) Er)
  by exact (cw_tcj_of_kept tfibsegs B LAWS tfib_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
              lyc Sc W memd mdd k (spZ regs) T Er HJ0 HJ Hwlo Hwhi HEimg KE).
eapply (cw_kept_cj B LAWS) with (1 := HJ0) (2 := HJ) (10 := KT) (11 := KT2);
[apply incl_refl | apply Permutation_refl | exact Hce | exact H47 | lia | lia |].
intros a Ha. right. left. split; [exact Ha | intros Him; exact (HEimg a Ha Him)].
Qed.

(* the tail jump: at the callee's entry pc = ss_pc ss, its contract instance, and its post is the walk's *)
Lemma tl_call : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k regs T
(Er : Z -> Prop) (R : world tfibsegs -> (word -> option byte) -> bvmap 5 word -> Prop)
E ss ms mdd T1 (R1 : world tfibsegs -> (word -> option byte) -> bvmap 5 word -> Prop),
YP0l.st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) mdd k ->
same_io mdc mdd ->
getr (ms_regs ms) 1 = getr regs 1 -> aregs_preserved regs (ms_regs ms) -> spZ (ms_regs ms) = spZ regs ->
alloc_ceiling <= spZ regs - T -> spZ regs <= 2 ^ 47 -> sp0 - STK <= spZ regs - T -> spZ regs <= sp0 ->
0 <= T1 <= T ->
(forall a, Er a -> in_img tfibsegs a -> False) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T <= a < spZ regs) -> ~ Er a ->
  aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) memc a) ->
(forall W3 mem3 regs3, R1 W3 mem3 regs3 -> R W3 mem3 regs3) ->
SRr tfibsegs W (cfg_at tfibsegs (ss_pc ss) (ms_regs ms) (ms_mem ms) mdd)
  (cdc_post tfibsegs B MT STK sp0 FP ly S W0 mem0 md0 own k (ms_regs ms) T1 Er lyc Sc W (ms_mem ms) mdd R1) ->
SRr tfibsegs W (mkCfg ms mdd)
  (cdc_post tfibsegs B MT STK sp0 FP ly S W0 mem0 md0 own k regs T Er lyc Sc W memc mdc R).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T Er R E ss ms mdd T1 R1
  HS Hrv HJ0 HJ Hio Hra Hpr Hsp Hce H47 Hwlo Hwhi HT HEimg KE HR HP.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS Hrv).
eapply SRr_mono; [exact HP|]. intros W2 c2 _ H2.
exact (tl_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T Er R (ms_mem ms) mdd (ms_regs ms) T1 R1
  W2 c2 HJ0 HJ Hio Hra Hpr Hsp Hce H47 Hwlo Hwhi HT HEimg KE HR H2).
Qed.

(* the caller's command at the jump: cdst_ok over memory that keeps every byte outside [lo, hi) *)
Lemma tl_cdst_kept : forall STK sp0 FP ly S lyc Sc own (W : world tfibsegs) m m' sp T q n lo hi,
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W m sp T q n ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
kHighShadowEnd <= lo -> (q + n <= lo \/ hi <= q) ->
(forall a, q <= a < q + n -> in_img tfibsegs a -> False) ->
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W m' sp T q n.
Proof.
intros STK sp0 FP ly S lyc Sc own W m m' sp T q n lo hi (Hq & Hqn & Htd & Htw & Hra & Hhv & Ham & Hcw) HK Hlo Hd Himg.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (H47 : q + n <= 2 ^ 47) by (unfold amem_range in Ham; rewrite C3, C4, C5 in Ham; lia).
split; [exact Hq|]. split; [exact Hqn|]. split; [exact Htd|].
split.
{ intros a Ha. destruct (Htw a Ha) as (Haw & Hp & Hno & Hsp). split; [exact Haw|]. split; [|split; [exact Hno | exact Hsp]].
  apply (apresent_transfer tfibsegs (w_H W) (w_H W) m m' a); [lia | intros Hi; exact (Himg a Ha Hi) | apply HK; lia | exact Hp]. }
split; [exact (range_addressable_kept_win _ _ lo hi q n HK Hlo ltac:(lia) H47 Hra)|].
split; [intros Hn; exact (shadow_hull_vis_kept_win _ _ lo hi q n HK Hlo ltac:(lia) H47 Hn (Hhv Hn))|].
split; [exact Ham | exact Hcw].
Qed.

(* a garr8 over memory that keeps its range *)
Lemma tl_garr8_kept : forall (W : world tfibsegs) (m m' : word -> option byte) base (l : list Z),
garr8 tfibsegs (mrestrict (w_H W) m) base l ->
(forall a, base <= a < base + Z.of_nat (length l) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
garr8 tfibsegs (mrestrict (w_H W) m') base l.
Proof.
intros W m m' base l HG HK j Hj. destruct (HG j Hj) as (HV & HR). split; [|exact HR].
intros kk Hk. assert (kk = 0%nat) as -> by lia.
rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) m m' (base + Z.of_nat j + Z.of_nat 0)).
- exact (HV 0%nat ltac:(lia)).
- apply HK. change (Z.of_nat 0) with 0. lia.
Qed.

(* the personality at the jump, over memory that keeps its four bytes *)
Lemma tl_pers_kept : forall (W : world tfibsegs) m m' sp T p d,
pers_argA tfibsegs B W m sp T p (Some d) ->
(forall a, p + 16 <= a < p + 20 -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
pers_argA tfibsegs B W m' sp T p (Some d).
Proof.
intros W m m' sp T p d (Hp0 & Hp63 & R1 & R2 & R3 & R4 & Hg & Hc) HK.
split; [exact Hp0|]. split; [exact Hp63|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
split; [exact R4|]. split; [|exact Hc].
apply (tl_garr8_kept W m m' (p + 16) _ Hg). intros a Ha. cbn [length Z.of_nat Pos.of_succ_nat] in Ha. apply HK. lia.
Qed.

(* the caller's command at the jump *)
Lemma tl_out_kept : forall STK sp0 FP ly S lyc Sc own (W : world tfibsegs) m m' sp T out before lo hi,
cenc_out tfibsegs B STK sp0 FP ly S lyc Sc own W m sp T out before ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
kHighShadowEnd <= lo -> (out + 32 <= lo \/ hi <= out) ->
(forall a, out <= a < out + 32 -> in_img tfibsegs a -> False) ->
cenc_out tfibsegs B STK sp0 FP ly S lyc Sc own W m' sp T out before.
Proof.
intros STK sp0 FP ly S lyc Sc own W m m' sp T out before lo hi (Hc & Hg & Hl) HK Hlo Hd Himg.
pose proof Hc as (Hq & Hqn & _).
split; [exact (tl_cdst_kept STK sp0 FP ly S lyc Sc own W m m' sp T out 32 lo hi Hc HK Hlo Hd Himg)|].
split; [|exact Hl].
apply (tl_garr8_kept W m m' out before Hg). intros a Ha. rewrite Hl in Ha. apply HK; lia.
Qed.
End b.
