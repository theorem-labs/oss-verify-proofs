(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: the allocator calls of its walk that are RAW allocator rules (not an own
   allocating callee's contract), shared by the walk's phases (one file, by ruling).
   The sites: free at 0x82e6c / 0x82e74 (op_decide), 0x83750 / 0x83758 (op_read), 0x838d8 (op_write), 0x83b88 /
   0x83b90 (the exit); calloc at 0x82c74 / 0x82c84 (the set-up).

   1. THE RULES WITH THE IO AND DEPOT CLAUSES (open item W1). The frame's journal-level rules (lib/Reusable/YC5d.v
      afree04_rule / afree_null04_rule, lib/Reusable/YGCalloc.v acalloc04_rule) say nothing of the depot, so a walk
      cannot carry the bound lf_jbk states on the depot's wild part (YG01.v wild_part) across them; nor of the
      model's descriptors and file system, which lf_jbk carries too. `afree04_rule_w`, `afree_null04_rule_w` and
      `acalloc04_rule_w` are the three rules, premises unchanged, with two more LAST post clauses, in the form the
      malloc depot states them (lib/A/Rt/LinkMallocDepot.v afree04_rule_d / afree_null04_rule_d /
      acalloc04_rule_d, agreed 2026-10-30; amalloc04_rule_d there is the malloc twin):
      - `same_io mdc md2` (YG0d.v:37): the realization every rule is proved from gives it (YG0d.v acall_post, which
        malloc_leaf and the free / calloc posts carry; YCbq.v aj_free_at_io keeps it for free), the frame's rules drop
        it;
      - `depot_step (call_trace lyc pc0 regsT ch) (st_depot Sc) (st_depot S2)` (YGwildCount.v): the depot is kept,
        or the call's trace is appended once.
      A walk takes each as a named Section hypothesis (AFREE4W, AFREENULL4W, ACALLOC4W).
   2. THE LIFTS onto the walk's journal `ajournal_gx G XO OUT` (W_journalG.v): aj_gx_free_w, aj_gx_free_null_w,
      aj_gx_calloc_w, by LinkWalkSide.v aj_gx_unpack and W_journalG.v ajournal_gx_pack around the donor rule, with the
      call's window [sp - ASTACK, sp) inside the journal's window and sp at least 16 below the journal's sp0 (so the
      frame record is well formed, YG0d.v frame0_ok, and the depot step is of call_trace0's trace). Their posts give
      the wild-count bound `(length (wild_part (as_universe B) (st_depot S2)) <= length (wild_part (as_universe B)
      (st_depot Sc)))%nat` in place of the depot step: the rule's own trace premise puts the trace in the universe's
      FIXED part (YG00.v:406, the coercion u_fix), so the step adds no wild trace (lf_depot_step_fixed).
   3. THE TRACE PREMISE in universe form. A raw rule asks `In (call_trace0 pc0 regsT ch) (as_universe B)`. At a
      site of LLVMFuzzerTestOneInput the chain is `lf_chain cx` (interface v7), whose spine is [RA_LLVMF] or [], so
      the trace is `lf_unwind pc0 (ra :: lf_ctx_tail b)` (`lf_unwind`: pc0, then the return addresses other than
      pc0, cut at kUnwindMax, YG00.v:375 unwind_of_chain; call_trace0_unwind is the exact equation). The named
      Section hypotheses a walk takes are `lf_trace_free B` (the seven free sites LF_FREE_RAS, pc0 =
      pc_free_ra0 (as_code B)) and `lf_trace_calloc B pc0` (the two calloc sites LF_CALLOC_RAS, pc0 = the calloc
      interceptor's own return address, 0x545a0 on image A, lib/A/DecodeCalloc.v DEC_A_calloc_ra0). Both are, text
      for text, lib/A/ACejSites.v llvmf_site_in at `as_universe B = Tfib_univ` and `pc_free_ra0 (as_code B) =
      0x5420c` (the start-up files; the top discharges them there).
   4. THE CHAIN AT A SITE OF LLVMFuzzerTestOneInput (lf_site_chain, over LLVMFuzzerTestOneInputDefs.v): at every
      cut of the body, a call made with sp = s1 (or lower) and s0 = the entry sp has the frame chain `lf_chain cx`:
      `chain_pre` (the raw rules' premise) and `achain` (the own allocating callees' premise, aleaf_alloc_rd) hold
      of it. It is the entry's chain (afn_pre: achain at the entry sp, ch = []) with LLVMFuzzerTestOneInput's own
      record pushed when it is well formed: [sp0 - 8] = the entry ra and [sp0 - 16] = the entry s0, both of
      lf_saved, and every byte at or above sp0 is the entry's (the journal's window ends at sp0, XO = 0).
      lf_free_trace / lf_calloc_trace give the raw rules' trace premise from the two Section hypotheses.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YGCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC85G.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. The unwound trace of a context (image-free)
   ========================================================================== *)

(* what the unwinder records for a call from pc0 whose return addresses, innermost first, are c *)
Definition lf_unwind (pc0 : Z) (c : list Z) : list Z :=
  firstn kUnwindMax (pc0 :: flat_map (fun ra => if ra =? pc0 then [] else [ra]) c).

Lemma call_trace0_unwind : forall pc0 (regs : bvmap 5 word) ch,
  call_trace0 pc0 regs ch = lf_unwind pc0 (raZ regs :: spine ch).
Proof.
  intros pc0 regs ch. unfold call_trace0, unwind_of_chain, lf_unwind, spine.
  f_equal. f_equal. cbn [flat_map map]. f_equal.
  induction ch as [|[[f r] v] ch IH]; [reflexivity|]. cbn [flat_map map fst snd]. rewrite IH. reflexivity.
Qed.

Lemma ctrace0_unwind : forall pc0 (regs : bvmap 5 word) ch,
  ctrace0 pc0 regs ch = lf_unwind pc0 (raZ regs :: spine ch).
Proof. intros pc0 regs ch. exact (call_trace0_unwind pc0 regs ch). Qed.

(* the tail of a context of LLVMFuzzerTestOneInput's sites: its own return address into target_run when its frame
   record is well formed (lf_chain), else nothing *)
Definition lf_ctx_tail (b : bool) : list Z := if b then [RA_LLVMF] else [].

(* the return addresses of the call's free and calloc sites (LLVMFuzzerTestOneInputDefs.v LF_FREE_SITES and
   LF_CALLOC_SITES at link_text + AF_LLVMFuzzerTestOneInput = 0x827d4) *)
Definition LF_FREE_RAS : list Z := [0x82e70; 0x82e78; 0x83758; 0x83760; 0x838dc; 0x83b8c; 0x83b94].
Definition LF_CALLOC_RAS : list Z := [0x82c78; 0x82c88].
Lemma LF_FREE_RAS_sites : map (fun o => link_text + AF_LLVMFuzzerTestOneInput + o)
  [0x69c; 0x6a4; 0xf84; 0xf8c; 0x1108; 0x13b8; 0x13c0] = LF_FREE_RAS.
Proof. reflexivity. Qed.

(* the named Section hypotheses of the raw rules' trace premise (ACejSites.v llvmf_site_in at the instance) *)
Definition lf_trace_free (B : asyms) : Prop :=
  forall ra (b : bool), In ra LF_FREE_RAS ->
    In (lf_unwind (pc_free_ra0 (as_code B)) (ra :: lf_ctx_tail b)) (as_universe B).
Definition lf_trace_calloc (B : asyms) (pc0 : Z) : Prop :=
  forall ra (b : bool), In ra LF_CALLOC_RAS -> In (lf_unwind pc0 (ra :: lf_ctx_tail b)) (as_universe B).

(* same_io keeps the descriptors and the file system (the two conjuncts lf_jbk and apost carry) *)
Lemma same_io_fds_fs : forall md md', same_io md md' -> m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
  intros [fd vm io fs proc lim tm] [fd' vm' io' fs' proc' lim' tm'] (E1 & E2 & E3 & E4).
  cbn in E1, E2, E3, E4. subst. split; reflexivity.
Qed.

(* the depot step of a FIXED trace adds no wild trace (the printf lane's LinkMallocDepot.v depot_step_fixed_wild) *)
Lemma lf_depot_step_fixed : forall U tr d d', depot_step tr d d' -> In tr (u_fix U) ->
  (length (wild_part U d') <= length (wild_part U d))%nat.
Proof.
  intros U tr d d' H Hf. pose proof (wild_part_step U tr d d' H) as W.
  unfold wild_cost in W. apply mem_trace_In in Hf. rewrite Hf in W. cbn [orb] in W. lia.
Qed.

(* at a call whose frame record is well formed the trace is call_trace0's *)
Lemma lf_call_trace_ok : forall ly pc0 (regs : bvmap 5 word) ch, spZ regs + 16 < ly_top ly ->
  call_trace ly pc0 regs ch = call_trace0 pc0 regs ch.
Proof.
  intros ly pc0 regs ch H. unfold call_trace, frame0_ok.
  replace (spZ regs + 16 <? ly_top ly) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

(* ==========================================================================
   2. The three rules with the io and depot clauses (open item W1): the malloc depot forms
      (lib/A/Rt/LinkMallocDepot.v afree04_rule_d / afree_null04_rule_d / acalloc04_rule_d), text for text
   ========================================================================== *)
Section r.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Abbreviation code := (as_code B).
#[local] Abbreviation ctr lyc pc0 regsT ch := (call_trace lyc pc0 regsT ch).

(* YC5d.v:75 afree04_rule, and the two clauses: io kept, one depot step of the call's trace *)
Definition afree04_rule_w : Prop :=
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
same_io mdc md2 /\ depot_step (ctr lyc (pc_free_ra0 code) regsT ch) (st_depot Sc) (st_depot S2)).

(* YC5d.v:97 afree_null04_rule, and the two clauses *)
Definition afree_null04_rule_w : Prop :=
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
same_io mdc md2 /\ depot_step (ctr lyc (pc_free_ra0 code) regsT ch) (st_depot Sc) (st_depot S2)).

(* YGCalloc.v:257 acalloc04_rule at the walk's journal (YCbq.v ajournal, acall_kept) and meter, and the two
   clauses *)
Definition acalloc04_rule_w (pc pc0 cmax cdepth : Z) : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k nm sz (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
ly_bot lyc + cdepth < spZ regsT ->
getr regsT 10 = w64 nm -> getr regsT 11 = w64 sz ->
0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> nm * sz <= cmax -> blocks_bytes Sc + nm * sz <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (ctrace0 pc0 regsT ch) (as_universe B) ->
mo_ok MT Sc (mo_malloc MT (nm * sz)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, nm * sz)] /\
(forall i, 0 <= i < nm * sz -> aview segs (w_H W2) mem2 (res + i) = Some 0) /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size (nm * sz)) /\
mo_le MT Sc S2 (mo_malloc MT (nm * sz)) /\
same_io mdc md2 /\ depot_step (ctr lyc pc0 regsT ch) (st_depot Sc) (st_depot S2)).

(* each _w rule gives the frame's rule *)
Lemma afree04_rule_of_w : afree04_rule_w -> afree04_rule segs B MT.
Proof.
  intros R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
    HJ Hin Ha0 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr Hcov Hmo.
  eapply SRr_mono; [exact (R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
    HJ Hin Ha0 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr Hcov Hmo)|].
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
  exists ly2, S2, regs2, mem2, md2. repeat (split; [assumption|]). exact H7.
Qed.

Lemma afree_null04_rule_of_w : afree_null04_rule_w -> afree_null04_rule segs B MT.
Proof.
  intros R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch
    HJ Ha0 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr Hmo.
  eapply SRr_mono; [exact (R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch
    HJ Ha0 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr Hmo)|].
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
  exists ly2, S2, regs2, mem2, md2. repeat (split; [assumption|]). exact H7.
Qed.

End r.

(* ==========================================================================
   3. The lifts onto ajournal_gx
   ========================================================================== *)
Section l.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
#[local] Abbreviation code := (as_code B).
#[local] Abbreviation wildc S := (length (wild_part (as_universe B) (st_depot S))).

(* a call made at least 16 bytes below the journal's sp0 has a well-formed frame record (YG0d.v frame0_ok), so its
   allocator trace is call_trace0's *)
Lemma aj_gx_frame0 : forall G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k (regsT : bvmap 5 word),
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT + 16 < sp0 -> spZ regsT + 16 < ly_top lyc.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT (_ & HXO & (memS & HJ & _) & _) Hs.
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  destruct Hstk as (_ & _ & _ & _ & _ & _ & _ & Htop & _). rewrite Etop. lia.
Qed.

Lemma aj_gx_free_w : afree04_rule_w segs B MT ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n raw ch,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  In (pa, n) (ablocks B lyc Sc) ->
  getr regsT 10 = w64 pa ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ASTACK -> spZ regsT <= sp0 -> spZ regsT + 16 < sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev S + k + 1 <= EV_MAX ->
  chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
  In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
  (In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
  mo_ok MT Sc (mo_free MT) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
       aregs_preserved regsT regs2 /\
       (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
       frames S2 = frames Sc /\
       acall_kept segs B lyc Sc W memT W2 mem2 (spZ regsT - ASTACK) (spZ regsT) (fun a => pa <= a < pa + req_size n) /\
       mo_le MT Sc S2 (mo_free MT) /\
       (wildc S2 <= wildc Sc)%nat /\ same_io mdc md2).
Proof.
  intros AF G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n raw ch
    HJX Hin Ha0 H16 Hlo Hhi Hfr0 Hgp Htp Hra Hraw Hev Hch Htr Hcov Hmo.
  pose proof (aj_gx_frame0 G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT HJX Hfr0) as Htop.
  assert (Has : ASTACK = 16384) by reflexivity.
  destruct (aj_gx_unpack SK segs B LAWS segs_low G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT ASTACK
    HJX ltac:(lia) H16 Hlo Hhi) as (memS & HJ & Hag & Hout & HSTK & HXO & Esp & Ho16 & Ho & Hb & Hceil & H47).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
  eapply SRr_mono.
  { exact (AF W regsT memT (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc mdc k pa n (spZ regsT - (sp0 + XO)) raw ch
      HJ Hin Ha0 Esp Ho16 Ho Hb Hgp Htp Hra Hraw ltac:(lia) Hch Htr Hcov Hmo). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & Hbl & Hfr & HK & MLE & HW & Hio).
  replace (sp0 + XO + (spZ regsT - (sp0 + XO))) with (spZ regsT) in HK by lia.
  exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
  split.
  { apply (ajournal_gx_pack segs B G XO OUT STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) memS HSTK HXO HJ2 Hag).
    intros a Ha Hno. destruct HK as (K1 & _). rewrite K1 by lia. exact (Hout a Ha Hno). }
  split; [exact HP|]. split; [exact Hbl|]. split; [exact Hfr|]. split; [exact HK|].
  split; [exact MLE|]. split; [|exact HW].
  rewrite (lf_call_trace_ok lyc _ regsT ch Htop) in Hio. exact (lf_depot_step_fixed _ _ _ _ Hio Htr).
Qed.

Lemma aj_gx_free_null_w : afree_null04_rule_w segs B MT ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw ch,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 0 ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ASTACK -> spZ regsT <= sp0 -> spZ regsT + 16 < sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev S + k + 1 <= EV_MAX ->
  chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
  In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
  mo_ok MT Sc (mo_free MT) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
       aregs_preserved regsT regs2 /\
       Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
       frames S2 = frames Sc /\
       acall_kept segs B lyc Sc W memT W2 mem2 (spZ regsT - ASTACK) (spZ regsT) (fun _ => False) /\
       mo_le MT Sc S2 (mo_free MT) /\
       (wildc S2 <= wildc Sc)%nat /\ same_io mdc md2).
Proof.
  intros AF G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw ch
    HJX Ha0 H16 Hlo Hhi Hfr0 Hgp Htp Hra Hraw Hev Hch Htr Hmo.
  pose proof (aj_gx_frame0 G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT HJX Hfr0) as Htop.
  assert (Has : ASTACK = 16384) by reflexivity.
  destruct (aj_gx_unpack SK segs B LAWS segs_low G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT ASTACK
    HJX ltac:(lia) H16 Hlo Hhi) as (memS & HJ & Hag & Hout & HSTK & HXO & Esp & Ho16 & Ho & Hb & Hceil & H47).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
  eapply SRr_mono.
  { exact (AF W regsT memT (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc mdc k (spZ regsT - (sp0 + XO)) raw ch
      HJ Ha0 Esp Ho16 Ho Hb Hgp Htp Hra Hraw ltac:(lia) Hch Htr Hmo). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & Hbl & Hfr & HK & MLE & HW & Hio).
  replace (sp0 + XO + (spZ regsT - (sp0 + XO))) with (spZ regsT) in HK by lia.
  exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
  split.
  { apply (ajournal_gx_pack segs B G XO OUT STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) memS HSTK HXO HJ2 Hag).
    intros a Ha Hno. destruct HK as (K1 & _). rewrite K1 by lia. exact (Hout a Ha Hno). }
  split; [exact HP|]. split; [exact Hbl|]. split; [exact Hfr|]. split; [exact HK|].
  split; [exact MLE|]. split; [|exact HW].
  rewrite (lf_call_trace_ok lyc _ regsT ch Htop) in Hio. exact (lf_depot_step_fixed _ _ _ _ Hio Htr).
Qed.

Lemma aj_gx_calloc_w : forall pc pc0 cmax cdepth, acalloc04_rule_w segs B MT pc pc0 cmax cdepth ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k nm sz raw ch,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  ly_bot lyc + cdepth < spZ regsT ->
  getr regsT 10 = w64 nm -> getr regsT 11 = w64 sz ->
  0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> nm * sz <= cmax -> blocks_bytes Sc + nm * sz <= LIVE_MAX ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ASTACK -> spZ regsT <= sp0 -> spZ regsT + 16 < sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev S + k + 1 <= EV_MAX ->
  chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
  In (ctrace0 pc0 regsT ch) (as_universe B) ->
  mo_ok MT Sc (mo_malloc MT (nm * sz)) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
       4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, nm * sz)] /\
       (forall i, 0 <= i < nm * sz -> aview segs (w_H W2) mem2 (res + i) = Some 0) /\
       acall_kept segs B lyc Sc W memT W2 mem2 (spZ regsT - ASTACK) (spZ regsT)
         (fun a => res <= a < res + req_size (nm * sz)) /\
       mo_le MT Sc S2 (mo_malloc MT (nm * sz)) /\
       (wildc S2 <= wildc Sc)%nat /\ same_io mdc md2).
Proof.
  intros pc pc0 cmax cdepth AC G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k nm sz raw ch
    HJX Hdep Ha0 Ha1 Hnm Hsz Hn Hcmax Hlive H16 Hlo Hhi Hfr0 Hgp Htp Hra Hraw Hev Hch Htr Hmo.
  pose proof (aj_gx_frame0 G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT HJX Hfr0) as Htop.
  assert (Has : ASTACK = 16384) by reflexivity.
  destruct (aj_gx_unpack SK segs B LAWS segs_low G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT ASTACK
    HJX ltac:(lia) H16 Hlo Hhi) as (memS & HJ & Hag & Hout & HSTK & HXO & Esp & Ho16 & Ho & Hb & Hceil & H47).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
  eapply SRr_mono.
  { exact (AC W regsT memT (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc mdc k nm sz (spZ regsT - (sp0 + XO)) raw ch
      HJ Hdep Ha0 Ha1 Hnm Hsz Hn Hcmax Hlive Esp Ho16 Ho Hb Hgp Htp Hra Hraw ltac:(lia) Hch Htr Hmo). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP & Hres & Hfr & H4096 & Hbl & Hz & HK & MLE
    & HW & Hio).
  replace (sp0 + XO + (spZ regsT - (sp0 + XO))) with (spZ regsT) in HK by lia.
  exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|].
  split.
  { apply (ajournal_gx_pack segs B G XO OUT STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) memS HSTK HXO HJ2 Hag).
    intros a Ha Hno. destruct HK as (K1 & _). rewrite K1 by lia. exact (Hout a Ha Hno). }
  split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact H4096|]. split; [exact Hbl|].
  split; [exact Hz|]. split; [exact HK|]. split; [exact MLE|]. split; [|exact HW].
  rewrite (lf_call_trace_ok lyc _ regsT ch Htop) in Hio. exact (lf_depot_step_fixed _ _ _ _ Hio Htr).
Qed.

End l.

(* ==========================================================================
   4. The chain at a site of LLVMFuzzerTestOneInput
   ========================================================================== *)
Section c.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LAWS : AR_laws SEGS B.

#[local] Notation LFB := (lf_base SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* At a cut of the body (the journal of lf_from, the two words of the machine frame's record from lf_saved), a call
   with sp at most s1 and s0 = the entry sp has the frame chain `lf_chain cx`: the raw rules' chain_pre and the own
   allocating callees' achain hold of it. *)
Lemma lf_site_chain : forall cx own ly3 S3 W3 mem3 md3 k2 (regsT : bvmap 5 word),
  LFB cx ->
  ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k2 ->
  rdword (aview SEGS (w_H W3) mem3) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) mem3) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  alloc_ceiling <= spZ regsT <= lf_sp1 cx -> s0Z regsT = spZ (c_regs cx) -> 4096 <= raZ regsT ->
  chain_pre ly3 (aview SEGS (w_H W3) mem3) regsT (lf_chain cx) /\
  achain ly3 (aview SEGS (w_H W3) mem3) (spZ regsT) (s0Z regsT) (lf_chain cx).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k2 regsT HB HJX H8 H16 Hsp Hs0 Hra.
  destruct HB as ((HPRE & _) & _).
  pose proof HPRE as (_ & _ & Hra0 & _ & _ & Hstk & _ & Hch0 & _).
  pose proof Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HSTKv : LLVMF_STK = 32768) by reflexivity.
  assert (Hsp1 : spZ (c_regs cx) - LF_MFRAME - 16 <= lf_sp1 cx <= spZ (c_regs cx) - LF_MFRAME).
  { unfold lf_sp1.
    destruct (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME; lia) Hal) as (R & _). exact R. }
  unfold LF_MFRAME in Hsp1.
  destruct HJX as (_ & _ & (memS & HJ & Hag) & _).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  (* every byte at or above sp0 is the entry's *)
  assert (Hab : forall a, spZ (c_regs cx) <= a < 2 ^ 64 ->
            aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (c_W cx)) (c_mem cx) a).
  { intros a Ha. rewrite !Z.add_0_r in F1. rewrite (F1 a ltac:(lia) ltac:(lia)).
    apply (aview_gagree SEGS G_HARNESS); [exact Hag|].
    destruct (inGb G_HARNESS (bv_unsigned (Z_to_bv 64 a))) eqn:Eg; [|reflexivity]. exfalso.
    apply inGb_spec in Eg. rewrite unsigned_lit_small in Eg by lia.
    unfold G_HARNESS, inG in Eg. rewrite !Exists_cons, Exists_nil in Eg. unfold in_zr in Eg. cbn [fst snd] in Eg.
    unfold LA_G_NL, LA_G_NAMES, LA_LONG_ALIAS, LA_G_SINK, LA_G_SAID, LA_G_SAY, LA_OFL_HEAD in Eg.
    unfold kLowMemEnd in *. lia. }
  assert (Hach : achain ly3 (aview SEGS (w_H W3) mem3) (spZ regsT) (s0Z regsT) (lf_chain cx)).
  { rewrite Hs0. unfold lf_chain.
    destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hlt | Hge].
    - apply (achain_ly_top (c_ly cx)); [exact Etop|].
      apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) (aview SEGS (w_H W3) mem3)
               (spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] (spZ regsT) Hch0);
        [lia | exact Hab | exact H8 | exact H16 | exact Hra0 | lia | | lia | lia].
      apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. destruct Hal as (q & Hq).
      exists (2 * q). lia.
    - left. split; [right; left; rewrite Etop; lia | reflexivity]. }
  split; [|exact Hach].
  apply (achain_chain_pre ly3 _ (spZ regsT) (s0Z regsT) (lf_chain cx) regsT Hach); [lia | reflexivity | exact Hra].
Qed.

(* the spine of the closed chain is RA_LLVMF or nothing *)
Lemma lf_chain_tail : forall cx, LFB cx -> exists b, spine (lf_chain cx) = lf_ctx_tail b.
Proof.
  intros cx ((_ & Hra & _) & _). unfold lf_chain.
  destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)); [exists true | exists false]; cbn [spine map fst snd];
    [rewrite Hra; reflexivity | reflexivity].
Qed.

(* the context lf_base gives at an allocating site *)
Lemma lf_site_ctx : forall cx (regsT : bvmap 5 word), LFB cx -> In (raZ regsT - BASE) LF_ALLOC_SITES ->
  In (raZ regsT :: spine (lf_chain cx)) LF_CTX.
Proof. intros cx regsT (_ & _ & _ & _ & _ & _ & _ & HCTX & _) Hs. exact (HCTX regsT Hs). Qed.

(* the raw rules' trace premise at a free / calloc site *)
Lemma lf_free_trace : forall cx (regsT : bvmap 5 word), LFB cx -> lf_trace_free B -> In (raZ regsT) LF_FREE_RAS ->
  In (call_trace0 (pc_free_ra0 (as_code B)) regsT (lf_chain cx)) (as_universe B).
Proof.
  intros cx regsT HB HT Hs. destruct (lf_chain_tail cx HB) as (b & Eb).
  rewrite call_trace0_unwind, Eb. exact (HT _ b Hs).
Qed.

Lemma lf_calloc_trace : forall pc0 cx (regsT : bvmap 5 word), LFB cx -> lf_trace_calloc B pc0 ->
  In (raZ regsT) LF_CALLOC_RAS -> In (ctrace0 pc0 regsT (lf_chain cx)) (as_universe B).
Proof.
  intros pc0 cx regsT HB HT Hs. destruct (lf_chain_tail cx HB) as (b & Eb).
  rewrite ctrace0_unwind, Eb. exact (HT _ b Hs).
Qed.

(* the two words lf_saved gives, in the form lf_site_chain takes *)
Lemma lf_saved_ra_s0 : forall cx (W3 : world SEGS) ms3,
  lf_saved cx W3 ms3 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)).
Proof.
  intros cx W3 ms3 (H8 & Hj). split; [exact H8|].
  pose proof (Hj 0 ltac:(lia)) as H0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
  exact H0.
Qed.

End c.
End a.
