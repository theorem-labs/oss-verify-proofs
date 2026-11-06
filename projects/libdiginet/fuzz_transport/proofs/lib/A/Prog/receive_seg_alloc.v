(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the journal of fuzz_reply's ASan program walks.  It is the donor's
   journal (Reusable/YCbq.v:351 ajournal) with two extensions the donor's programs never needed, and the
   run chain of Reusable/YC80.v restated over it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_journal.v, with its module paths and module names changed; 81 of its 127 lines of code are new or changed and 849 lines of the source are left out. *)
(* receive_seg_alloc: the two allocator calls of a G-form caller-journal walk (lib/A/W_journalG.v ajournal_gx with
   XO = 0 and OUT = []), and the facts about the block they add and remove. Nothing here names a program function.
   - gx_malloc_at: YC85.v amalloc04_sub inside the G journal (TransportGCg.v gx_open gives the donor journal at a start
     memory that agrees with the G journal's outside G; gx_pack0 packs it again at that memory), as
     TransportGFrame.v gx_stack_malloc_at does for the stack malloc.
   - gx_free_at: YC85.v afree04_sub inside the G journal, the same way.
   - gx_malloc_fresh: the block the malloc adds is none of the blocks before it (AR_laws' al_sep: the blocks are
     pairwise apart, and a block of at least one byte is not apart from itself).
   - gx_start_fp: a block of the journal's start state that is not a block of the current state lies in the
     footprint (YCbq.v ajournal's clause for a start block the journal no longer holds): afree04_rule's footprint
     premise for a block the walk allocated.
   - gx_trace0: the trace an allocator call rule asks for (YCbq.v call_trace0) is DgnTransportCg.v decode_utrace of
     the return address followed by the chain's return addresses (fuzz_decode's crtA_w_tail.v crtT_trace). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI04 YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportPa DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC85 TransportGCg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.

(* The trace of an allocator call. *)
Lemma gx_trace0 : forall pc0 (regs : bvmap 5 word) (ch : list (Z * Z * Z)),
  call_trace0 pc0 regs ch = decode_utrace pc0 (raZ regs :: spine ch).
Proof.
  intros pc0 regs ch. unfold call_trace0, unwind_of_chain, decode_utrace, spine. cbn [flat_map map].
  f_equal. f_equal. f_equal.
  induction ch as [|[[fp ra] nfp] ch IH]; [reflexivity|]. cbn [flat_map map]. f_equal. exact IH.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable MT : ameter_ops.

(* The malloc in the G journal. *)
Lemma gx_malloc_at : amalloc04_rule segs B MT ->
forall G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B) ->
mo_ok MT Sc (mo_malloc MT n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
mo_le MT Sc S2 (mo_malloc MT n)).
Proof.
intros AM G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
  HJ Ha0 Hn Hlive Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch HU MOK.
destruct (gx_open segs B G STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k HJ) as (memS & HJi & Hag & HSTK).
eapply SRr_mono.
{ exact (amalloc04_sub (SK := SK) segs B LAWS segs_low MT AM W regsT memT STK sp0 FP ly S W0 memS md own lyc Sc mdc
    k n o raw ch HJi Ha0 Hn Hlive Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch HU MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & Hc & HJ2 & Hrest).
exists ly2, S2, regs2, mem2, md2, res. split; [exact Hc|].
split; [exact (gx_pack0 segs B G STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) memS HSTK HJ2 Hag)|].
destruct Hrest as (HP & Hres & Hfr & Hr4 & Hbl & HK & MLE & _).
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hr4|]. split; [exact Hbl|].
split; [exact HK | exact MLE].
Qed.

(* The free in the G journal. *)
Lemma gx_free_at : afree04_rule segs B MT ->
forall G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n (o : Z) raw ch,
ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (pa, n) (ablocks B lyc Sc) ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_free_ra0 (as_code B)) regsT ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n) /\
mo_le MT Sc S2 (mo_free MT)).
Proof.
intros AF G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
  HJ Hin Ha0 Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch HU Hcov MOK.
destruct (gx_open segs B G STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k HJ) as (memS & HJi & Hag & HSTK).
eapply SRr_mono.
{ exact (afree04_sub (SK := SK) segs B LAWS segs_low MT AF W regsT memT STK sp0 FP ly S W0 memS md own lyc Sc mdc
    k pa n o raw ch HJi Hin Ha0 Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch HU Hcov MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & Hrest).
exists ly2, S2, regs2, mem2, md2. split; [exact Hc|].
split; [exact (gx_pack0 segs B G STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) memS HSTK HJ2 Hag)|].
destruct Hrest as (HP & Hbl & Hfr & HK & MLE & _).
split; [exact HP|]. split; [exact Hbl|]. split; [exact Hfr|]. split; [exact HK | exact MLE].
Qed.

(* The malloc's block is none of the blocks before it. *)
Lemma gx_malloc_fresh : forall ly2 S2 (W2 : world segs) mem2 md2 lyc Sc res n,
  AR segs B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] -> 0 <= n ->
  ~ In (res, n) (ablocks B lyc Sc).
Proof.
intros ly2 S2 W2 mem2 md2 lyc Sc res n HAR E Hn Hin.
apply in_split in Hin as (l1 & l2 & El).
rewrite El, <- app_assoc in E. cbn [app] in E.
pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (res, n) (res, n) l1 l2 [] HAR E) as Hd.
pose proof (req_size_pos n Hn) as [Hr _].
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* A block of the journal's start state that the current state no longer holds lies in the footprint. *)
Lemma gx_start_fp : forall G STK sp0 FP ly S (W0 : world segs) mem md own lyc Sc (W : world segs) memc mdc k pa n,
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  ~ In (pa, n) (ablocks B lyc Sc) ->
  In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i).
Proof.
intros G STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k pa n HJ Hnot Hin i Hi.
destruct (gx_open segs B G STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k HJ) as (memS & HJi & _ & _).
destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
exact (Hgone pa n i Hin Hnot Hi).
Qed.
End a.
