(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepAppRcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 3f969b478d6c) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair), and 4 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, slice F4 of a Theorem Labs lane's class-full report walk, for AppendWalk):
   the call of __sanitizer::InternalMmapVectorNoCtor<char, true>::Realloc (0x59e3c) from
   __asan::AppendToErrorMessageBuffer (0x56418, the jal at 0x56548 and at 0x5657c) as an st_ok-to-st_ok stretch.
   rule 24: proves no function (kind: segment lemma of __asan::AppendToErrorMessageBuffer's walk, a call wrapper
   around Realloc's contract; reuse search: `proof-index VSNPrintf Printf SharedPrintfCode AppendNumber
   AppendToErrorMessageBuffer MmapOrDie` 2026-10-30T02:25:54Z exit 0 and `proof-index UnmapOrDie
   internal_memset internal_memcpy internal_strlen GetNamedMappingFd IncreaseTotalMmap` 2026-10-30T02:55Z exit 3,
   0 released lemma(s) for every name; rule-24 check RepLookupCheck CONFIRM, nothing reusable).

   Realloc's contract is RepReallocD's realloc_pre / realloc_post.  [realloc_stretch] (the deliverable) uses it in
   the model's form, RepReallocf.realloc_node (the KMmapSec ask of Realloc's MmapOrDie is the node of the call);
   [realloc_stretch_t] takes the plain SRr form as a Section hypothesis and serves any tree.  The caller's regions
   survive the call when no byte of theirs is in Realloc's write set (its stack window REALLOC_STK, the vector's
   data / capacity words, the old buffer, any grant of the new one). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFeq YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YE08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB15 YFff.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0v YK13 YK02 YG0b YFfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Z Require Import Placement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RepReallocD.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RepMmapcf RepReallocf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. A call kept every region whose bytes keep their visibility and their value.                                   *)
Lemma st_ok_after_call_W : forall (W W' : world tfibsegs) (k : nat) (E : env) (ss : sstate) (ms : machine_state)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (rs : smem) (retpc : Z),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
regions_wf rs = true -> no_cdata rs = true -> mem_atoms_lt k rs = true -> submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1%bv = SLit retpc ->
regs_preserved (ms_regs ms) regs' ->
(forall r a, In r rs -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
   w_H W' (Z_to_bv 64 a) = w_H W (Z_to_bv 64 a) /\ mem' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
st_ok tfibsegs (havoc E k (map (getr regs') CLOB)) (ss_after_call ss rs k retpc)
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))).
Proof.
intros W W' k E ss ms regs' mem' rs retpc HS Hrv Hat Hwf Hnc Hmat Hsub Hra HP HK.
rewrite restrict_mkst_fx.
apply (st_ok_after_call tfibsegs k E ss (restrict (w_H W) ms) regs' (mrestrict (w_H W') mem') rs retpc HS Hrv Hat Hwf Hnc Hmat Hsub Hra HP).
apply Forall_forall. intros r Hr.
assert (Hwfr : YP09.region_wf r = true) by (eapply regions_wf_In; eauto).
apply region_wf_facts in Hwfr as (W1 & W2 & _).
split.
- intros a Ha. destruct (HK r a Hr Ha) as [E1 E2]. unfold mbyte. cbn [ms_mem restrict]. unfold mrestrict. rewrite E1, E2. reflexivity.
- intros a Ha Hw. destruct W2 as [W2|W2]; [lia|]. destruct (HK r a Hr ltac:(lia)) as [E1 E2].
  unfold writable_at, wview in *. cbn [ms_mem restrict] in Hw. unfold mrestrict in *. rewrite E1, E2. exact Hw.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. Realloc's post at a call site: the configuration at the return and the caller's symbolic state there.        *)
Lemma realloc_post_after_call : forall (W W' : world tfibsegs) (k : nat) (E : env) (ss : sstate) (rs : smem)
  (ms : machine_state) (md : Model) (v nb d cap sz retpc : Z) (c' : config),
let sp := bv_unsigned (getr (ms_regs ms) 2) in let ncap := page_round_up_Z nb in
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
regions_wf rs = true -> no_cdata rs = true -> mem_atoms_lt k rs = true -> submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1%bv = SLit retpc -> 0 < nb ->
(forall r x, In r rs -> base_val E (YP09.r_base r) + YP09.r_lo r <= x < base_val E (YP09.r_base r) + YP09.r_hi r ->
   ~ (sp - REALLOC_STK <= x < sp) /\ ~ (v <= x < v + 16) /\ ~ (d <= x < d + cap)) ->
(forall r x, In r rs -> base_val E (YP09.r_base r) + YP09.r_lo r <= x < base_val E (YP09.r_base r) + YP09.r_hi r ->
   forall a : word, grant_ok_na_pin md a ncap = true -> ~ (bv_unsigned a <= x < bv_unsigned a + ncap)) ->
realloc_post W (ms_regs ms) (ms_mem ms) md v nb d cap sz W' c' ->
exists (regs' : bvmap 5 word) (mem' : word -> option byte) (mdx : Model),
  c' = mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) mdx /\
  st_ok tfibsegs (havoc E k (map (getr regs') CLOB)) (ss_after_call ss rs k retpc)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))).
Proof.
intros W W' k E ss rs ms md v nb d cap sz retpc c'. cbv zeta.
intros HS Hrv Hat Hwf Hnc Hmat Hsub Hra Hnb R1 R2 HP.
unfold realloc_post in HP. cbv zeta in HP.
destruct HP as (a & regs' & mem' & mat & mat2 & _ & _ & _ & HHout & Hg & Ha0 & Ha1 & Hc & HPres & _ & _ & _ & _ & _ & _ & FR & _).
assert (NC0 : nb <= page_round_up_Z nb)
  by (pose proof (YK02.page_round_up_Z_bounds nb ltac:(lia)) as X; unfold page_size in X; lia).
assert (RA : getr (ms_regs ms) 1 = Z_to_bv 64 retpc).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms 1%bv HS), Hra. reflexivity. }
pose proof (mem_ok_sub tfibsegs E _ (ss_mem ss) rs Hsub Hwf (st_ok_mem_ok tfibsegs E ss _ HS)) as (_ & MOK & _).
assert (Ua : bv_unsigned (w64 a) = a) by (unfold w64; apply unsigned_lit_small; clear - Hnb Ha0 Ha1 NC0; lia).
exists regs', mem'. eexists.
split; [rewrite Hc, RA; reflexivity|].
apply (st_ok_after_call_W W W' k E ss ms regs' mem' rs retpc HS Hrv Hat Hwf Hnc Hmat Hsub Hra HPres).
intros r x Hr Hx.
pose proof (proj1 (Forall_forall _ _) MOK r Hr) as (B1 & B2 & _).
assert (Ux : bv_unsigned (Z_to_bv 64 x) = x) by (apply unsigned_lit_small; clear - B1 B2 Hx; lia).
destruct (R1 r x Hr Hx) as (N1 & N2 & N3).
pose proof (R2 r x Hr Hx (w64 a) Hg) as N4. rewrite Ua in N4.
split.
- apply HHout. rewrite Ux. exact N4.
- apply FR; rewrite Ux; assumption.
Qed.
Lemma realloc_pre_nb : forall W regs mem md v nb d cap sz, realloc_pre W regs mem md v nb d cap sz -> 0 < nb.
Proof. intros W regs mem md v nb d cap sz P. unfold realloc_pre in P. cbv zeta in P. destruct P as (_ & _ & _ & _ & X & _). exact X. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The stretch, with Realloc's contract in the model's form, RepReallocf.realloc_node (the deliverable).          *)
Lemma realloc_stretch : forall {R : Type} (K : Z -> itree astate R) (Q : R -> world tfibsegs -> config -> Prop)
  (snap : astate) (rq : Z) (W : world tfibsegs) (k : nat) (E : env) (ss : sstate) (rs : smem) (ms : machine_state) (md : Model)
  (v nb d cap sz retpc : Z),
let sp := bv_unsigned (getr (ms_regs ms) 2) in let ncap := page_round_up_Z nb in
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = A_REALLOC ->
ss_atoms_lt k ss = true -> regions_wf rs = true -> no_cdata rs = true -> mem_atoms_lt k rs = true -> submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1%bv = SLit retpc ->
realloc_pre W (ms_regs ms) (ms_mem ms) md v nb d cap sz ->
(forall r x, In r rs -> base_val E (YP09.r_base r) + YP09.r_lo r <= x < base_val E (YP09.r_base r) + YP09.r_hi r ->
   ~ (sp - REALLOC_STK <= x < sp) /\ ~ (v <= x < v + 16) /\ ~ (d <= x < d + cap)) ->
(forall r x, In r rs -> base_val E (YP09.r_base r) + YP09.r_lo r <= x < base_val E (YP09.r_base r) + YP09.r_hi r ->
   forall a : word, grant_ok_na_pin md a ncap = true -> ~ (bv_unsigned a <= x < bv_unsigned a + ncap)) ->
(forall (W' : world tfibsegs) (regs' : bvmap 5 word) (mem' : word -> option byte) (mdx : Model),
   realloc_post W (ms_regs ms) (ms_mem ms) md v nb d cap sz W' (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) mdx) ->
   st_ok tfibsegs (havoc E k (map (getr regs') CLOB)) (ss_after_call ss rs k retpc)
     (restrict (w_H W') (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))) ->
   amreal tfibsegs (K 1) W' (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) mdx) Q) ->
amreal tfibsegs (IAsk (KMmapSec rq) snap K) W (mkCfg ms md) Q.
Proof.
intros R K Q snap rq W k E ss rs ms md v nb d cap sz retpc. cbv zeta.
intros HS Hrv Hpc Hat Hwf Hnc Hmat Hsub Hra Hpre R1 R2 HK.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Hrv) as Hshape. rewrite Hpc in Hshape.
rewrite Hshape.
apply (RepReallocf.realloc_node K Q snap rq W (ms_regs ms) (ms_mem ms) md v nb d cap sz Hpre).
intros W' c' HP.
destruct (realloc_post_after_call W W' k E ss rs ms md v nb d cap sz retpc c' HS Hrv Hat Hwf Hnc Hmat Hsub Hra
  (realloc_pre_nb _ _ _ _ _ _ _ _ _ Hpre) R1 R2 HP) as (regs' & mem' & mdx & -> & HS').
exact (HK W' regs' mem' mdx HP HS').
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The stretch, with Realloc's contract as a plain SRr spec, for any tree.                                       *)
Section p.
Hypothesis Hrealloc : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (v nb d cap sz : Z),
realloc_pre W regs mem md v nb d cap sz ->
SRr tfibsegs W (mkCfg (mkst regs (w64 A_REALLOC) mem (seg_rom tfibsegs)) md) (realloc_post W regs mem md v nb d cap sz).
Lemma realloc_stretch_t : forall {R : Type} (t : itree astate R) (Q : R -> world tfibsegs -> config -> Prop)
  (W : world tfibsegs) (k : nat) (E : env) (ss : sstate) (rs : smem) (ms : machine_state) (md : Model)
  (v nb d cap sz retpc : Z),
let sp := bv_unsigned (getr (ms_regs ms) 2) in let ncap := page_round_up_Z nb in
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = A_REALLOC ->
ss_atoms_lt k ss = true -> regions_wf rs = true -> no_cdata rs = true -> mem_atoms_lt k rs = true -> submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1%bv = SLit retpc ->
realloc_pre W (ms_regs ms) (ms_mem ms) md v nb d cap sz ->
(forall r x, In r rs -> base_val E (YP09.r_base r) + YP09.r_lo r <= x < base_val E (YP09.r_base r) + YP09.r_hi r ->
   ~ (sp - REALLOC_STK <= x < sp) /\ ~ (v <= x < v + 16) /\ ~ (d <= x < d + cap)) ->
(forall r x, In r rs -> base_val E (YP09.r_base r) + YP09.r_lo r <= x < base_val E (YP09.r_base r) + YP09.r_hi r ->
   forall a : word, grant_ok_na_pin md a ncap = true -> ~ (bv_unsigned a <= x < bv_unsigned a + ncap)) ->
(forall (W' : world tfibsegs) (regs' : bvmap 5 word) (mem' : word -> option byte) (mdx : Model),
   realloc_post W (ms_regs ms) (ms_mem ms) md v nb d cap sz W' (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) mdx) ->
   st_ok tfibsegs (havoc E k (map (getr regs') CLOB)) (ss_after_call ss rs k retpc)
     (restrict (w_H W') (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))) ->
   amreal tfibsegs t W' (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) mdx) Q) ->
amreal tfibsegs t W (mkCfg ms md) Q.
Proof.
intros R t Q W k E ss rs ms md v nb d cap sz retpc. cbv zeta.
intros HS Hrv Hpc Hat Hwf Hnc Hmat Hsub Hra Hpre R1 R2 HK.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Hrv) as Hshape. rewrite Hpc in Hshape.
rewrite Hshape.
apply (amreal_SRr_pre tfibsegs t W _ Q (realloc_post W (ms_regs ms) (ms_mem ms) md v nb d cap sz)).
- exact (Hrealloc W (ms_regs ms) (ms_mem ms) md v nb d cap sz Hpre).
- intros W' c' _ HP.
  destruct (realloc_post_after_call W W' k E ss rs ms md v nb d cap sz retpc c' HS Hrv Hat Hwf Hnc Hmat Hsub Hra
    (realloc_pre_nb _ _ _ _ _ _ _ _ _ Hpre) R1 R2 HP) as (regs' & mem' & mdx & -> & HS').
  exact (HK W' regs' mem' mdx HP HS').
Qed.
End p.
End s.
