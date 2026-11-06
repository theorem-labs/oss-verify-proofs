(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the three call compositions of musl's fread inside libreac/fuzz_pcap
   (libreac v1.9.0, memory-checking build), for the walk lib/A/Stdio/PFreadMW.v.

   rule 24: no function proved. These are composition and transport lemmas over the statement of
   record lib/A/Stdio/PFreadM.v; none of them walks a function, and none of them names a symbolic
   engine state, so the walk applies them at its call sites.

   fread runs with sp = sp_entry - 64 (its frame, 0x8ee5c) and makes three calls:
     the memory-copy trampoline (0x8eee0, returns to 0x8eee4): a0 = dest, a1 = src, a2 = n;
     __toread (0x8ef00, returns to 0x8ef04): a0 = f;
     f->read = mread through `jalr a3` (0x8ef18, returns to 0x8ef1c): a0 = f, a1 = dest, a2 = len.
   In each lemma below `regs` is fread's register file at ITS entry (only spZ regs is used) and
   `regsc` / `regsm` the register file at the callee's entry, with spZ regsc = spZ regs - 64.

   THE DESTINATION OF A CALL IS A SUB-RANGE OF fread's. fread passes the trampoline (d, k0) and
   mread (d + k0, nm - k0) (0x8eee8 `add s3,s3,s4`, 0x8eef4 `sub s4,s6,s4`), so frd_call_memcpy
   and frd_call_mread take fread's rread_dest over (d, nm) and a sub-range d <= d', d' + l <=
   d + nm. frd_dest_sub moves an rread_dest to a sub-range, to a deeper callee window, and to a
   later memory whose shadow band [kLowMemEnd, kHighShadowEnd) is unchanged; the band is all an
   rread_dest reads of memory (range_addressable, shadow_hull_vis).

   STACK BUDGETS. RFREAD_STK = 64 + RTOREAD_STK = 64 + 16 + RMREAD_STK = 64 + 16 + 48 + ESTACK
   (PFreadM.v), so every callee window [spZ regs - 64 - STK1, spZ regs - 64) lies inside fread's
   [spZ regs - RFREAD_STK, spZ regs). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI00 YI04 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YC20.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import YC85G.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma frd_unsigned_small : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia. Qed.

Lemma frd_stk_consts : ESTACK = 4096 /\ RMREAD_STK = 4144 /\ RTOREAD_STK = 4160 /\ RFREAD_STK = 4224.
Proof. repeat split; reflexivity. Qed.

(* The shadow hull of a range of application memory below 2^47 lies in the shadow band. *)
Lemma frd_hull_band : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
  kLowMemEnd <= s < kHighShadowEnd.
Proof.
intros x n s Hx Hn Hxn Hs. unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert ((x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z_div_mod_eq_full (2147450880 + x / 8) 8). pose proof (Z.mod_pos_bound (2147450880 + x / 8) 8 ltac:(lia)).
pose proof (Z_div_mod_eq_full (2147450880 + (x + n - 1) / 8) 8).
pose proof (Z.mod_pos_bound (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.

(* The shadow hull of a sub-range is inside the hull of the range. *)
Lemma frd_hull_sub : forall d nm d' l s, 0 <= d -> d <= d' -> 0 < l -> d' + l <= d + nm ->
  shadow_addr d' / 8 * 8 <= s < shadow_addr (d' + l - 1) / 8 * 8 + 8 ->
  shadow_addr d / 8 * 8 <= s < shadow_addr (d + nm - 1) / 8 * 8 + 8.
Proof.
intros d nm d' l s Hd Hdd Hl Hdl Hs.
pose proof (shadow_mono d d' Hdd) as M1. pose proof (shadow_mono (d' + l - 1) (d + nm - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

Section call.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable K : asource_syms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* ---------------------------------------------------------------------- *)
(* The destination, moved to a sub-range, a deeper window and a later      *)
(* memory with the same shadow band.                                       *)
(* ---------------------------------------------------------------------- *)
Lemma frd_dest_sub : forall STK sp0 FP ly S own lyc Sc We meme W memc RSTK sp RSTK' sp' d nm d' l f b n,
  rread_dest segs B STK sp0 FP ly S own lyc Sc We meme RSTK sp d nm f b n ->
  sp - RSTK <= sp' - RSTK' -> sp' <= sp ->
  d <= d' -> d' + l <= d + nm -> 0 <= l ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W) memc s = aview segs (w_H We) meme s) ->
  rread_dest segs B STK sp0 FP ly S own lyc Sc W memc RSTK' sp' d' l f b n.
Proof.
intros STK sp0 FP ly S own lyc Sc We meme W memc RSTK sp RSTK' sp' d nm d' l f b n
  (Hdf & Hdb & Hd0 & Ham & Hat & Hwr & Hra & Hhull) Hw1 Hw2 Hdd Hdl Hl0 Hband.
assert (Hdhi : d + nm <= 2 ^ 47).
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
split.
{ destruct Hat as [(cid & pos & Hin & Hr) | [Hs | (bb & nn & Hin & H1 & H2)]].
  - left. exists cid, pos. split; [exact Hin|]. intros a Ha. apply Hr. lia.
  - right; left. lia.
  - right; right. exists bb, nn. split; [exact Hin | lia]. }
split.
{ intros a Ha. destruct (Hwr a ltac:(lia)) as [Hw Hn]. split; [exact Hw | lia]. }
split.
{ apply (range_addressable_agree (aview segs (w_H We) meme)).
  - intros x Hx. apply Hband. unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
    assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
  - apply (range_addressable_sub _ _ d nm); [exact Hra | lia | lia]. }
intros Hl s Hs. rewrite (Hband s (frd_hull_band d' l s ltac:(lia) Hl ltac:(lia) Hs)).
apply (Hhull ltac:(lia)). exact (frd_hull_sub d nm d' l s Hd0 Hdd Hl Hdl Hs).
Qed.

(* ---------------------------------------------------------------------- *)
(* 1. __toread, folded into fread's caller journal.                         *)
(* ---------------------------------------------------------------------- *)
(* The fold's footprint side condition: every byte of the FILE block that the caller lets fread
   write is in the caller's footprint or in a block the caller allocated (the stack arm dies on
   f + 1304 <= alloc_ceiling <= ly_stk_lo ly, the frame arm on sep_block_frame, the frame-shadow
   arm on the block being application memory). *)
Lemma frd_toread_fp : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k RSTK sp f,
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) ->
  rread_wr_ok B STK sp0 FP ly S lyc Sc own RSTK sp f SRC_FILE_BLOCK ->
  forall a, inFP (rtoread_fp f) a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k RSTK sp f HJ Hf Hwr a Ha.
destruct Ha as (r & Hr & Ha). unfold rtoread_fp in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
destruct (Hwr a Ha) as [Hw _].
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK HAR Hf)
  as (Hf16 & Hf0 & Hfceil & Hfapp & Hfbytes & Hfdisj & Hfrange).
assert (RQ : req_size SRC_FILE_BLOCK = SRC_FILE_BLOCK) by reflexivity. rewrite RQ in *.
destruct Hw as [Hs | [(Hin & _) | [Ht | (cid & pos & Hown & Hr)]]].
- exfalso. lia.
- left. exact Hin.
- right. exact Ht.
- exfalso.
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  pose proof (sep_block_frame segs B LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK cid pos HAR Hf HinC) as Hd.
  rewrite RQ in Hd.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR HinC) as (Hfa0 & Hfac & Hfah).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as SB1.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as SB2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as SB3.
  unfold zdisjoint, in_zr, in_app in *. cbn [fst snd] in *.
  unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighShadowEnd, kHighMemEnd in *.
  destruct Hr as [Hr | Hr]; lia.
Qed.

(* __toread's own pre, built from the caller's journal (afn_pre_at). *)
Lemma frd_toread_pre : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs regsc : bvmap 5 word) ch1 (f b p fl ra : Z) (C : list Z),
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regsc = spZ regs - 64 -> spZ regs mod 16 = 0 ->
  sp0 - STK <= spZ regs - RFREAD_STK -> spZ regs <= sp0 ->
  getr regsc 1 = Z_to_bv 64 ra -> YK0s.ret_ok (getr regsc 1) -> 4096 <= ra < 2 ^ 64 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) memc) (spZ regsc) (s0Z regsc) ch1 ->
  getr regsc 10 = w64 f ->
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) -> In (b, Z.of_nat (length C)) (ablocks B lyc Sc) ->
  (b + Z.of_nat (length C) <= spZ regs - RFREAD_STK \/ spZ regs <= b) ->
  asource_unbuffered segs K (rd W memc) f b C p -> source_flags segs (rd W memc) f fl ->
  rtoread_pre segs B K regsc lyc Sc W memc mdc ch1 f b p fl C.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsc ch1 f b p fl ra C
  HJ Hspc Hal Hlo Hhi Hra Hret Hra4 Hgp Htp Hch G10 Hf Hb Hboff Hsrc Hfl.
pose proof frd_stk_consts as (E1 & E2 & E3 & E4).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & _) & _ & _).
assert (Hraw : raZ regsc = ra) by (unfold raZ; rewrite Hra; apply frd_unsigned_small; lia).
split.
{ apply (afn_pre_at segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regsc RTOREAD_STK
    (spZ regsc - sp0) ch1 HJ); [lia | | lia | lia | lia | exact Hret | lia | exact Hgp | exact Htp | exact Hch].
  rewrite Hspc. lia. }
split; [exact G10|]. split; [exact Hf|]. split; [exact Hb|]. split; [lia|]. split; [exact Hsrc | exact Hfl].
Qed.

Lemma frd_call_toread : forall pct, rtoread_contract segs B K pct ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs regsc : bvmap 5 word) ch1
    (f b p fl ra : Z) (C : list Z),
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regsc = spZ regs - 64 -> spZ regs mod 16 = 0 ->
  sp0 - STK <= spZ regs - RFREAD_STK -> spZ regs <= sp0 ->
  getr regsc 1 = Z_to_bv 64 ra -> YK0s.ret_ok (getr regsc 1) -> 4096 <= ra < 2 ^ 64 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) memc) (spZ regsc) (s0Z regsc) ch1 ->
  getr regsc 10 = w64 f ->
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) -> In (b, Z.of_nat (length C)) (ablocks B lyc Sc) ->
  (b + Z.of_nat (length C) <= spZ regs - RFREAD_STK \/ spZ regs <= b) ->
  asource_unbuffered segs K (rd W memc) f b C p -> source_flags segs (rd W memc) f fl ->
  rread_wr_ok B STK sp0 FP ly S lyc Sc own RFREAD_STK (spZ regs) f SRC_FILE_BLOCK ->
  SRr segs W (mkCfg (mkst regsc (Z_to_bv 64 pct) memc (seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (getr regsc 1) mem2 (seg_rom segs)) md2 /\
       ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
       ajournal segs B RTOREAD_STK (spZ regsc) (rtoread_fp f) lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 0 /\
       aregs_preserved regsc regs2 /\
       rtoread_post segs K f b p fl C lyc Sc W memc ly2 S2 W2 regs2 mem2 md2).
Proof.
intros pct HTO STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsc ch1 f b p fl ra C
  HJ Hspc Hal Hlo Hhi Hra Hret Hra4 Hgp Htp Hch G10 Hf Hb Hboff Hsrc Hfl Hwr.
pose proof frd_stk_consts as (E1 & E2 & E3 & E4).
eapply SRr_mono.
{ apply (HTO W lyc Sc regsc memc mdc ch1 f b p fl C).
  exact (frd_toread_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsc ch1 f b p fl ra C
    HJ Hspc Hal Hlo Hhi Hra Hret Hra4 Hgp Htp Hch G10 Hf Hb Hboff Hsrc Hfl). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HQ).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
rewrite <- (Z.add_0_r k). change own with ([] ++ own).
eapply (ajournal_sub_tok segs B LAWS segs_low); [exact HJ | exact HJ1 | lia | lia |].
exact (frd_toread_fp STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k RFREAD_STK (spZ regs) f HJ Hf Hwr).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. mread, through f->read: already in the caller-journal form.           *)
(* ---------------------------------------------------------------------- *)
Lemma frd_mread_pre : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs regsm : bvmap 5 word) ch (d nm d' l f b p mo ra : Z) (C : list Z),
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regsm = spZ regs - 64 -> spZ regs mod 16 = 0 ->
  sp0 - STK <= spZ regs - RFREAD_STK -> spZ regs <= sp0 ->
  getr regsm 1 = Z_to_bv 64 ra -> YK0s.ret_ok (getr regsm 1) -> 4096 <= ra < 2 ^ 64 ->
  getr regsm 3 = w64 (as_gp B) -> getr regsm 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) memc) (spZ regsm) (s0Z regsm) ch ->
  getr regsm 10 = w64 f -> getr regsm 11 = w64 d' -> getr regsm 12 = w64 l ->
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) -> In (b, Z.of_nat (length C)) (ablocks B lyc Sc) ->
  (b + Z.of_nat (length C) <= spZ regs - RFREAD_STK \/ spZ regs <= b) ->
  asource_unbuffered segs K (rd W memc) f b C p ->
  source_flags segs (rd W memc) f 8 -> source_mode segs (rd W memc) f mo ->
  rread_wr_ok B STK sp0 FP ly S lyc Sc own RFREAD_STK (spZ regs) f SRC_FILE_BLOCK ->
  1 <= l <= 2 ^ 26 ->
  rread_dest segs B STK sp0 FP ly S own lyc Sc W memc RFREAD_STK (spZ regs) d nm f b (Z.of_nat (length C)) ->
  d <= d' -> d' + l <= d + nm ->
  rmread_pre segs B K STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regsm ch f d' l b p mo C.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsm ch d nm d' l f b p mo ra C
  HJ Hspm Hal Hlo Hhi Hra Hret Hra4 Hgp Htp Hch G10 G11 G12 Hf Hb Hboff Hsrc Hfl Hmo Hwr Hl Hdest Hdd Hdl.
pose proof frd_stk_consts as (E1 & E2 & E3 & E4).
assert (Hraw : raZ regsm = ra) by (unfold raZ; rewrite Hra; apply frd_unsigned_small; lia).
split.
{ split; [exact HJ|]. split; [exact Hret|]. split; [lia|]. split; [exact Hgp|]. split; [exact Htp|].
  split; [rewrite Hspm; lia|]. split; [lia|]. split; [lia | exact Hch]. }
split; [exact G10|]. split; [exact G11|]. split; [exact G12|]. split; [exact Hf|]. split; [exact Hb|].
split; [lia|]. split; [exact Hsrc|]. split; [exact Hfl|]. split; [exact Hmo|].
split.
{ intros a Ha. destruct (Hwr a Ha) as [Hw Hn]. split; [exact Hw | lia]. }
split; [exact Hl|].
apply (frd_dest_sub STK sp0 FP ly S own lyc Sc W memc W memc RFREAD_STK (spZ regs) RMREAD_STK (spZ regsm)
  d nm d' l f b (Z.of_nat (length C)) Hdest); [lia | lia | exact Hdd | exact Hdl | lia | intros; reflexivity].
Qed.

Lemma frd_call_mread : rmread_contract segs B K (as_read K) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs regsm : bvmap 5 word) ch
    (d nm d' l f b p mo ra : Z) (C : list Z),
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regsm = spZ regs - 64 -> spZ regs mod 16 = 0 ->
  sp0 - STK <= spZ regs - RFREAD_STK -> spZ regs <= sp0 ->
  getr regsm 1 = Z_to_bv 64 ra -> YK0s.ret_ok (getr regsm 1) -> 4096 <= ra < 2 ^ 64 ->
  getr regsm 3 = w64 (as_gp B) -> getr regsm 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) memc) (spZ regsm) (s0Z regsm) ch ->
  getr regsm 10 = w64 f -> getr regsm 11 = w64 d' -> getr regsm 12 = w64 l ->
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) -> In (b, Z.of_nat (length C)) (ablocks B lyc Sc) ->
  (b + Z.of_nat (length C) <= spZ regs - RFREAD_STK \/ spZ regs <= b) ->
  asource_unbuffered segs K (rd W memc) f b C p ->
  source_flags segs (rd W memc) f 8 -> source_mode segs (rd W memc) f mo ->
  rread_wr_ok B STK sp0 FP ly S lyc Sc own RFREAD_STK (spZ regs) f SRC_FILE_BLOCK ->
  1 <= l <= 2 ^ 26 ->
  rread_dest segs B STK sp0 FP ly S own lyc Sc W memc RFREAD_STK (spZ regs) d nm f b (Z.of_nat (length C)) ->
  d <= d' -> d' + l <= d + nm ->
  SRr segs W (mkCfg (mkst regsm (Z_to_bv 64 (as_read K)) memc (seg_rom segs)) mdc)
    (rread_post_base segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k RMREAD_STK regsm
       (rread_wrset f d' l) (rmread_post segs K f d' l b p mo C lyc Sc W memc mdc)).
Proof.
intros HMR STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsm ch d nm d' l f b p mo ra C
  HJ Hspm Hal Hlo Hhi Hra Hret Hra4 Hgp Htp Hch G10 G11 G12 Hf Hb Hboff Hsrc Hfl Hmo Hwr Hl Hdest Hdd Hdl.
exact (HMR STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regsm ch f d' l b p mo C
  (frd_mread_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsm ch d nm d' l f b p mo ra C
     HJ Hspm Hal Hlo Hhi Hra Hret Hra4 Hgp Htp Hch G10 G11 G12 Hf Hb Hboff Hsrc Hfl Hmo Hwr Hl Hdest Hdd Hdl)).
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The memory-copy trampoline (aintrin_realizes OCpy), at fread's call.  *)
(* ---------------------------------------------------------------------- *)
(* The source facts aintrin_realizes asks for, when the source lies inside the live FILE block
   (fread's read window [f + SRC_BUF_OFF + i, ...) does). *)
Lemma frd_src_block : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs regsc : bvmap 5 word) (f x n : Z),
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regsc = spZ regs - 64 -> sp0 - STK <= spZ regs - RFREAD_STK ->
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) -> f <= x -> x + n <= f + SRC_FILE_BLOCK -> 0 <= n ->
  0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regsc memc x n /\ amem_range x n /\
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF x n /\
  (0 < n -> shadow_hull_vis (aview segs (w_H W) memc) x n).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsc f x n HJ Hspc Hlo Hf Hfx Hxn Hn.
pose proof frd_stk_consts as (E1 & E2 & E3 & E4).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK HAR Hf)
  as (Hf16 & Hf0 & Hfceil & Hfapp & Hfbytes & Hfdisj & Hfrange).
assert (RQ : req_size SRC_FILE_BLOCK = SRC_FILE_BLOCK) by reflexivity. rewrite RQ in *.
split; [lia|]. split; [lia|]. split.
{ intros a Ha. split.
  - apply (aview_some_of_apresent segs). exact (proj1 (Hfbytes a ltac:(lia))).
  - lia. }
split; [apply (amem_range_of_block segs B LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK); [exact HAR | exact Hf | lia | rewrite RQ; lia]|].
split; [apply (range_addressable_of_block segs B LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK); [exact HAR | exact Hf | lia | rewrite RQ; lia]|].
intros Hn0. apply (shadow_hull_vis_of_block segs B LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK);
  [exact HAR | exact Hf | lia | rewrite RQ; lia | exact Hn0].
Qed.

(* aj_intrin_atS at fread's call, the source given by its facts. The destination (d', n) is a
   sub-range of fread's (d, nm). Besides aj_intrin_atS's post: the shadow band is unchanged. *)
Lemma frd_call_memcpy : forall pcm, aintrin_realizes segs B OCpy pcm ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs regsc : bvmap 5 word)
    (d nm f b nb d' x n : Z),
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regsc = spZ regs - 64 -> spZ regs mod 16 = 0 ->
  sp0 - STK <= spZ regs - RFREAD_STK -> spZ regs <= sp0 ->
  YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 d' -> getr regsc 11 = w64 x -> getr regsc 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  rread_dest segs B STK sp0 FP ly S own lyc Sc W memc RFREAD_STK (spZ regs) d nm f b nb ->
  d <= d' -> d' + n <= d + nm ->
  0 <= x -> x + n <= 2 ^ 63 -> src_ok segs W regsc memc x n -> (d' + n <= x \/ x + n <= d') ->
  amem_range x n -> range_addressable (aview segs (w_H W) memc) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) memc) x n) ->
  SRr segs W (mkCfg (mkst regsc (Z_to_bv 64 pcm) memc (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (getr regsc 1) mem2 (seg_rom segs)) md2 /\
       ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       aregs_preserved regsc regs2 /\ getr regs2 10 = w64 d' /\
       (forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d' + i) = aview segs (w_H W) memc (x + i)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d' <= a < d' + n) -> ~ (spZ regsc - ESTACK <= a < spZ regsc) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memc a) /\
       (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W) mem2 s = aview segs (w_H W) memc s) /\
       (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof.
intros pcm HAI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsc d nm f b nb d' x n
  HJ Hspc Hal Hlo Hhi Hret Hgp Htp G10 G11 G12 Hn Hdest Hdd Hdn Hx0 Hxn Hsrc Hdisj Hxam Hxra Hxhull.
pose proof frd_stk_consts as (E1 & E2 & E3 & E4).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (frd_dest_sub STK sp0 FP ly S own lyc Sc W memc W memc RFREAD_STK (spZ regs) ESTACK (spZ regsc)
  d nm d' n f b nb Hdest ltac:(lia) ltac:(lia) Hdd Hdn ltac:(lia) ltac:(intros; reflexivity))
  as (_ & _ & Hd0 & Ham & _ & Hwr & Hra & Hhull).
assert (Hdhi : d' + n <= 2 ^ 47).
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
eapply SRr_mono.
{ eapply (aj_intrin_atS segs B LAWS segs_low OCpy pcm HAI W regsc memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc
    mdc k d' x n (spZ regsc - sp0) (getr regsc 1) HJ G10 G11 G12 Hn Hd0 ltac:(lia) ltac:(lia) ltac:(rewrite Hspc; lia)
    ltac:(lia) ltac:(lia) Hgp Htp eq_refl Hret).
  - intros a Ha. destruct (Hwr a Ha) as [Hw Hns]. split; [exact Hw | lia].
  - exact Ham.
  - exact Hra.
  - exact Hhull.
  - cbn iota. split; [exact Hx0|]. split; [exact Hxn|]. split; [exact Hsrc|]. split; [exact Hdisj|].
    split; [exact Hxam|]. split; [exact Hxra | exact Hxhull]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & H10 & Hcp & Hkeep & Hpres & Hsame).
replace (sp0 + (spZ regsc - sp0)) with (spZ regsc) in Hkeep by lia.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact H10|]. split; [exact Hcp|].
split; [exact Hkeep|]. split; [|split; [exact Hpres | exact Hsame]].
intros s Hs. apply Hkeep; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighShadowEnd, kHighMemEnd in *; lia.
Qed.

(* The same call with the source inside the live FILE block: its source facts are
   frd_src_block's, and the destination is disjoint from the FILE (rread_dest). *)
Lemma frd_call_memcpy_file : forall pcm, aintrin_realizes segs B OCpy pcm ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs regsc : bvmap 5 word)
    (d nm f b nb d' x n : Z),
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regsc = spZ regs - 64 -> spZ regs mod 16 = 0 ->
  sp0 - STK <= spZ regs - RFREAD_STK -> spZ regs <= sp0 ->
  YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 d' -> getr regsc 11 = w64 x -> getr regsc 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  rread_dest segs B STK sp0 FP ly S own lyc Sc W memc RFREAD_STK (spZ regs) d nm f b nb ->
  d <= d' -> d' + n <= d + nm ->
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) -> f <= x -> x + n <= f + SRC_FILE_BLOCK ->
  SRr segs W (mkCfg (mkst regsc (Z_to_bv 64 pcm) memc (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (getr regsc 1) mem2 (seg_rom segs)) md2 /\
       ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       aregs_preserved regsc regs2 /\ getr regs2 10 = w64 d' /\
       (forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d' + i) = aview segs (w_H W) memc (x + i)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d' <= a < d' + n) -> ~ (spZ regsc - ESTACK <= a < spZ regsc) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memc a) /\
       (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W) mem2 s = aview segs (w_H W) memc s) /\
       (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof.
intros pcm HAI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsc d nm f b nb d' x n
  HJ Hspc Hal Hlo Hhi Hret Hgp Htp G10 G11 G12 Hn Hdest Hdd Hdn Hf Hfx Hxn.
destruct (frd_src_block STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsc f x n
  HJ Hspc Hlo Hf Hfx Hxn ltac:(lia)) as (Hx0 & Hx63 & Hsrc & Hxam & Hxra & Hxhull).
pose proof Hdest as (Hdf & _).
apply (frd_call_memcpy pcm HAI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsc d nm f b nb d' x n
  HJ Hspc Hal Hlo Hhi Hret Hgp Htp G10 G11 G12 Hn Hdest Hdd Hdn Hx0 Hx63 Hsrc ltac:(lia) Hxam Hxra Hxhull).
Qed.

End call.
