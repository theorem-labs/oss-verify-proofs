(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ajournal_closed_fs is cgif_file_fuzzer's lib/A/ACfh.v ajournal_closed_io (origin/ossv/recipes c8557374ad2e), module paths changed; the rest is new kit for libreac/fuzz_pcap's program walks, over cgif's journal (lib/Reusable/YCbq.v) and the rule lifts of lib/A/Prog/YC85.v, with no image constant: a call whose own journal has a sink-closed footprint leaves the descriptors and the file system exactly as it found them, so a walk whose cumulative journal carries the sink token (fuzz_pcap's entry, PcapEntryDefs.pe_from) keeps m_fds / m_fs exact across the harness's own allocator and intrinsic calls. *)
(* What already existed, and is used here unchanged:
   - YCbq.ajournal_sub_init: a fresh journal at the current state, with any footprint FP1;
   - YC85.ajournal_sub_tok (cgif YC85.v): composition of the cumulative journal with a callee's journal whose footprint
     is the caller's or a block allocated since the caller's start;
   - YC85.amalloc04_sub / afree04_sub / afree_null04_sub: the allocator rules applied to such a fresh journal (footprint
     [] for malloc and free(NULL), the freed block for free) and composed, each also returning the callee's journal;
   - YCbq.aos_step_closed: under a sink-closed footprint ajournal's aos_step fixes m_fd and m_fsys.
   What this file adds: that exactness, as m_fds / m_fs equations, for any composed call (ajournal_sub_closed_fs) and
   for the three rule lifts and the intrinsic lift (YC85.aj_intrin_atS, whose post is same_but_materialized). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK15 YK18 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC85G.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable MT : ameter_ops.
Local Notation code := (as_code B).

(* cgif lib/A/ACfh.v ajournal_closed_io. *)
Lemma ajournal_closed_fs : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ~ YI16.sink_open_fp FP ->
  ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
  intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k Hcl HJ. pose proof HJ as (_ & _ & _ & _ & Hos & _).
  destruct (aos_step_closed FP md md' Hcl Hos) as (Efd & Efsys & _ & _).
  unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.

Lemma same_io_fs : forall md md', same_io md md' -> m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros md md' (E1 & _ & E3 & _). unfold m_fds, m_fs. rewrite E1, E3. split; reflexivity. Qed.

Lemma same_but_materialized_fs : forall md md', same_but_materialized md md' ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros md md' H. apply same_io_fs. exact (same_io_materialized md md' H). Qed.

(* The composition, with the exactness: a callee's journal from the current state whose footprint is sink-closed and
   lies in the caller's footprint or in blocks the caller allocated extends the cumulative journal and leaves the
   descriptors and the file system as they were at the call. *)
Lemma ajournal_sub_closed_fs : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1,
  ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  ajournal segs B STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  ~ YI16.sink_open_fp FP1 ->
  ajournal segs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1) /\
  m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc.
Proof.
  intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1 HJ HJ1 Hlo Hhi HF Hcl.
  split; [exact (ajournal_sub_tok segs B LAWS segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf
                   ly2 S2 W2 mem2 md2 k1 HJ HJ1 Hlo Hhi HF)|].
  exact (ajournal_closed_fs STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 Hcl HJ1).
Qed.

(* YC85.amalloc04_sub, with the descriptors and the file system kept. *)
Lemma amalloc04_sub_fs : amalloc04_rule segs B MT ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
  ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev Sc < EV_MAX ->
  chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
  In (call_trace0 (pc_malloc_ra0 code) regsT ch) (as_universe B) ->
  mo_ok MT Sc (mo_malloc MT n) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
     ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
     aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
     4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
     acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
     mo_le MT Sc S2 (mo_malloc MT n) /\
     m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc).
Proof.
  intros AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch HJ Ha0 Hn Hlive Hsp Ho16 Ho Hstk
    Hgp Htp Hra Hraw Hnev Hch HU MOK.
  eapply SRr_mono.
  { exact (amalloc04_sub segs B LAWS segs_low MT AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
             HJ Ha0 Hn Hlive Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch HU MOK). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & Ec & HJ2 & HP & Hres & Hfr & Hr4 & Hbl & HK & MLE & HJ1).
  destruct (ajournal_closed_fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sink_closed_nil HJ1) as [Efd Efs].
  exists ly2, S2, regs2, mem2, md2, res. repeat (split; [assumption|]). assumption.
Qed.

(* YC85.afree04_sub, with the descriptors and the file system kept (the callee's footprint is the freed block,
   which starts at 4096 or above, so it is sink-closed). *)
Lemma afree04_sub_fs : afree04_rule segs B MT ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n (o : Z) raw ch,
  ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  In (pa, n) (ablocks B lyc Sc) ->
  getr regsT 10 = w64 pa ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev Sc < EV_MAX ->
  chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
  In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
  (In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
  mo_ok MT Sc (mo_free MT) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
     ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
     aregs_preserved regsT regs2 /\
     (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
     frames S2 = frames Sc /\
     acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n) /\
     mo_le MT Sc S2 (mo_free MT) /\
     m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc).
Proof.
  intros AF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch HJ Hin Ha0 Hsp Ho16 Ho Hstk Hgp Htp
    Hra Hraw Hnev Hch HU Hcov MOK.
  pose proof HJ as (HAR & _).
  pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & _).
  eapply SRr_mono.
  { exact (afree04_sub segs B LAWS segs_low MT AF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
             HJ Hin Ha0 Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch HU Hcov MOK). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & HP & Hbl & Hfr & HK & MLE & HJ1).
  assert (Hcl : ~ YI16.sink_open_fp (ablocks_fp [(pa, n)])).
  { apply sink_closed_ablocks_fp. constructor; [cbn [fst]; lia | constructor]. }
  destruct (ajournal_closed_fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcl HJ1) as [Efd Efs].
  exists ly2, S2, regs2, mem2, md2. repeat (split; [assumption|]). assumption.
Qed.

(* YC85.afree_null04_sub, with the descriptors and the file system kept. *)
Lemma afree_null04_sub_fs : afree_null04_rule segs B MT ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw ch,
  ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 0 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev Sc < EV_MAX ->
  chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
  In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
  mo_ok MT Sc (mo_free MT) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
     ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
     aregs_preserved regsT regs2 /\
     Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
     frames S2 = frames Sc /\
     acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
     mo_le MT Sc S2 (mo_free MT) /\
     m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc).
Proof.
  intros AF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch HJ Ha0 Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw
    Hnev Hch HU MOK.
  eapply SRr_mono.
  { exact (afree_null04_sub segs B LAWS segs_low MT AF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch
             HJ Ha0 Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch HU MOK). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & HP & Hbl & Hfr & HK & MLE & HJ1).
  destruct (ajournal_closed_fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sink_closed_nil HJ1) as [Efd Efs].
  exists ly2, S2, regs2, mem2, md2. repeat (split; [assumption|]). assumption.
Qed.

(* THE PROGRAM CALLEE LIFT (a Theorem Labs lane decision 22:36Z). A program callee of the harness (libreac_fuzz_fopen,
   pcap_source_open / _next / _close) writes no program global, so its statement stays on the donor's ajournal; its
   journal, started at the call state (the caller's current memory memc), extends the harness's W_journal.v
   ajournal_gx G 0 [] for ANY global ranges G. This is the one citation the harness lanes use at those calls.
   Proof: YC85.ajournal_sub_tok on the inner donor journal, repacked by ajournal_gx_pack with the same start memory.
   W_journal.v's ajournal_gx_sub is not used: its footprint premise asks every callee footprint byte to be in a heap
   block, which the sink token (address 0) of the open / close statements' footprint is not; ajournal_sub_tok asks only
   inFP FP a \/ in_tmp_block, as YC85 does for cgif's callees. *)
Lemma ajournal_gx_callee : forall G STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1,
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  ajournal segs B STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Proof.
  intros G STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1
    (H0 & H1 & (memS & HJi & Hag) & _) HJ1 Hlo Hhi HF.
  rewrite !Z.add_0_r in HJi.
  eapply ajournal_gx_pack; [exact H0 | exact H1 | | exact Hag | intros a Ha _; lia].
  rewrite !Z.add_0_r.
  exact (ajournal_sub_tok segs B LAWS segs_low STK sp0 FP ly S W memS md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf
           ly2 S2 W2 mem2 md2 k1 HJi HJ1 Hlo Hhi HF).
Qed.

(* The same lift with the descriptors and the file system kept, for a callee whose footprint is sink-closed. *)
Lemma ajournal_gx_callee_closed_fs : forall G STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1,
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  ajournal segs B STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  ~ YI16.sink_open_fp FP1 ->
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1) /\
  m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc.
Proof.
  intros G STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1 HJ HJ1 Hlo Hhi HF Hcl.
  split; [exact (ajournal_gx_callee G STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2
                   md2 k1 HJ HJ1 Hlo Hhi HF)|].
  exact (ajournal_closed_fs STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 Hcl HJ1).
Qed.

End e.
End c.
(* The sink head is EXPLICIT on every exported lemma here (a Theorem Labs lane, 21:57Z): the only global sink_head instance in
   fuzz_pcap's closure is the plain build's, so it must never be inferred. *)
Arguments ajournal_closed_fs {rc} SK segs B.
Arguments ajournal_sub_closed_fs {rc} SK segs B LAWS segs_low.
Arguments amalloc04_sub_fs {fx rc} SK segs B LAWS segs_low MT.
Arguments afree04_sub_fs {fx rc} SK segs B LAWS segs_low MT.
Arguments afree_null04_sub_fs {fx rc} SK segs B LAWS segs_low MT.
Arguments ajournal_gx_callee {rc} SK segs B LAWS segs_low.
Arguments ajournal_gx_callee_closed_fs {rc} SK segs B LAWS segs_low.
