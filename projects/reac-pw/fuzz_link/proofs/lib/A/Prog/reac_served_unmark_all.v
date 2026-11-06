(* reac_served_unmark_all (fuzz_link.asan 0x89ed4, listing offset AF_reac_served_unmark_all = 0x7d08) on image A:
   the top of its walk. `um_shape` says that the interface of lib/A/Prog/reac_served_unmark_allDefs.v is the
   contract: a proof that from every context `cx` whose `um_pre` holds the run of the entry reaches `um_post cx`
   gives `reac_served_unmark_all_acontract`. The walk is cut at five places of the code (HEAD +0x1d8, MID +0x288,
   JOIN +0x294, TAIL +0x340, REL +0x350; and the entry's BRANCH cut +0x18c of reac_served_unmark_allEntryDefs.v):
     reac_served_unmark_allEntryA.v : um_br_obl -> the run from the entry reaches um_post
     reac_served_unmark_allEntryB.v : um_rel_obl -> um_tail_obl -> um_head_obl 0 -> um_br_obl
     reac_served_unmark_allReadB.v  : forall c, um_mid_obl c -> um_join_obl c -> um_head_obl c (um_read)
     reac_served_unmark_allWrite.v  : forall c, um_join_obl c -> um_mid_obl c
     reac_served_unmark_allJoin.v   : um_tail_obl -> forall c, um_head_obl (S c) -> um_join_obl c
     reac_served_unmark_allTail.v   : um_rel_obl -> um_tail_obl
     reac_served_unmark_allRel.v    : um_rel_obl
   and this file closes the loop (a loop head of round c >= MARKS_MAX is never reached: `um_head_far`) and composes
   them into `reac_served_unmark_all_aproof`.

   Proves function reac_served_unmark_all (image A, the asan build). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_unmark_all_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_unmark_allDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk PcapRelroA reac_link_alias_read_c
reac_link_alias_write_c reac_served_unmark_allEntryDefs reac_served_unmark_allEntryA reac_served_unmark_allEntryB
reac_served_unmark_allReadB reac_served_unmark_allWrite reac_served_unmark_allJoin reac_served_unmark_allTail
reac_served_unmark_allRel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.

(* The entry configuration of the contract, at a context. *)
Definition um_cfg (cx : umcx) : config :=
  cfg_at SEGS REAC_SERVED_UNMARK_ALL_A (um_regs cx) (um_memc cx) (um_mdc cx).

(* THE INTERFACE IS THE CONTRACT: `aleaf_rd`'s body at a context whose Pre witnesses the walk names. *)
Theorem um_shape :
  (forall cx : umcx, um_pre SK B cx -> SRr SEGS (um_W cx) (um_cfg cx) (um_post SK B cx)) ->
  reac_served_unmark_all_acontract SK SEGS PCAP_RLO PCAP_RHI B.
Proof.
intros H G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE HRD HP.
destruct HP as (kbs & tab & HNL & HER & HTB & HBK & HS1 & HS2 & HE1 & HE2).
assert (HG : exists gbs, aarg regs 0 <> 0 ->
  amarks_at SEGS (mrestrict (w_H W) memc) (aarg regs 0) gbs /\ marks_wf gbs).
{ destruct (Z.eq_dec (aarg regs 0) 0) as [E0 | N0].
  - exists []. intros N. exfalso. exact (N E0).
  - destruct (HBK N0) as (_ & _ & _ & _ & gbs & Hg & Hw). exists gbs. intros _. split; [exact Hg | exact Hw]. }
destruct HG as (gbs & HGB).
exact (H (mkUMCX G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kbs tab gbs)
  (conj HPRE (conj HRD (conj HNL (conj HER (conj HTB (conj HBK (conj HS1 (conj HS2 (conj HE1 (conj HE2 HGB))))))))))).
Qed.

(* A loop head of round c >= MARKS_MAX is never reached: um_pre gives marks_wf, so m->n <= MARKS_MAX. *)
Lemma um_head_far : forall c, (Z.to_nat MARKS_MAX <= c)%nat -> um_head_obl SK B c.
Proof.
intros c Hc cx fpos ly3 S3 W3 ms3 md3 HPRE (_ & (Hm & Hcn & _) & _).
exfalso. destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGB).
destruct (HGB Hm) as (_ & ((Hn0 & Hn1) & _)). unfold um_n in Hcn.
change (Z.to_nat MARKS_MAX) with 32%nat in Hc. unfold MARKS_MAX in *. lia.
Qed.

(* The loop closes: from the three body pieces, every loop head reaches the post. *)
Lemma um_loop_closed :
  um_tail_obl SK B ->
  (forall c, um_mid_obl SK B c -> um_join_obl SK B c -> um_head_obl SK B c) ->
  (forall c, um_join_obl SK B c -> um_mid_obl SK B c) ->
  (forall c, um_head_obl SK B (S c) -> um_join_obl SK B c) ->
  forall c, um_head_obl SK B c.
Proof.
intros HT HRD HWR HJN.
assert (K : forall d c, (Z.to_nat MARKS_MAX <= c + d)%nat -> um_head_obl SK B c).
{ induction d as [|d IH]; intros c Hc.
  - apply um_head_far. lia.
  - assert (HS : um_head_obl SK B (S c)) by (apply IH; lia).
    pose proof (HJN c HS) as HJ.
    exact (HRD c (HWR c HJ) HJ). }
intros c. apply (K (Z.to_nat MARKS_MAX) c). lia.
Qed.

End b.
End a.

(* ==========================================================================
   The top lemma
   ========================================================================== *)
Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
(* the allocator's laws (the lib/A frame) *)
Hypothesis LAWS : AR_laws SEGS B.
(* link's listing values and runtime facts: the link instance (LinkWalk.v LinkVals, LinkPaLib.v PALib) *)
Hypothesis LV : LinkVals.
Hypothesis TL : PALib B.
(* the start-up symbols of image A: lib/A/AD2l.v PcapB_syms *)
Hypothesis TB : PcapSyms B.
(* the segments the listing is certified against: lib/A/Prog/LinkImgInst.v pi_link_segs (reflexivity) *)
Hypothesis HSEGS : SEGS = tfibsegs.
(* the callees *)
Hypothesis HRD : reac_link_alias_read_acontract SK SEGS PCAP_RLO PCAP_RHI B.     (* reac_link_alias_read.v *)
Hypothesis HWR : reac_link_alias_write_acontract SK SEGS PCAP_RLO PCAP_RHI B.    (* reac_link_alias_write.v *)
Hypothesis HBC : abcmp_realizes SEGS B (pa_sigma LS___interceptor_trampoline_bcmp). (* AE2s.v bcmp_icpt_contract *)
Hypothesis HSM : astack_malloc_realizes SEGS B 3.                (* Rt/StackSideInst.v link_stack_malloc_3 *)
Hypothesis HF5 : aset_shadow_realizes SEGS B (pa_sigma LS___asan_set_shadow_f5) 0xf5. (* Rt/SetShadow.v link_set_shadow_f5 *)
Hypothesis HMS : aintrin_realizes SEGS B OSet (pa_sigma LS___asan_memset). (* AE2r.v asan_memset_realizes *)

(* PcapRelro.v's read-only window lies in one segment of image A (PcapRelroA.v pcap_relro_in_image) *)
Lemma um_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Proof.
intros a Ha. rewrite HSEGS. destruct pcap_relro_in_image as (s & Hin & H1 & H2 & H3).
exists s. split; [exact Hin | lia].
Qed.

Theorem reac_served_unmark_all_aproof : reac_served_unmark_all_acontract SK SEGS PCAP_RLO PCAP_RHI B.
Proof.
pose proof um_relro_img as RELRO_IMG.
assert (HREL : um_rel_obl SK B) by (eapply um_rel; eassumption).
assert (HTAIL : um_tail_obl SK B) by (eapply um_tail; eassumption).
assert (HHEAD : forall c, um_head_obl SK B c).
{ apply (um_loop_closed SK B HTAIL).
  - intros c. eapply um_read; eassumption.
  - intros c. eapply um_write; eassumption.
  - intros c. eapply um_join; eassumption. }
pose proof (HHEAD 0%nat) as HH0.
assert (HBR : um_br_obl SK B) by (eapply um_entryB; eassumption).
apply um_shape. intros cx HP. unfold um_cfg.
eapply um_entryA; eassumption.
Qed.

End top.

About reac_served_unmark_all_aproof.
Print Assumptions reac_served_unmark_all_aproof.

(* No global sink_head instance is in scope here. *)
Fail Definition sink_head_probe_um_top : YI16.sink_head := _.
