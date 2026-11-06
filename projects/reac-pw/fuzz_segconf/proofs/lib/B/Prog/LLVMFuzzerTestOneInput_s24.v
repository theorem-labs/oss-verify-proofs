(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment F of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86a3c .. 0x86a60): the three frees of the words blocks (pointers reloaded from sp + 120 .. 136) and the latch s1 + 1 <> 32 back to the loop head or out to the second rec_clear, the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s71.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (pb_wcb: run, branch, exit) and A/ACh6.v (a segment statement proved from the statements of the points it leaves to). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_s71.v, with its module paths, module names and numbers changed; 1941 of its 2010 lines of code are new or changed and 315 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): segments S16 .. S20
   of the walk of the test harness's entry function LLVMFuzzerTestOneInput (0x85e50 .. 0x85ec4): the two declared
   calls, the four frees of mt, tab, m and c, and the store that puts n out of scope.

   THE FORM: the frees (S17, S18, S19 and S16's free(mt)) follow the image-B harness walk of plugin-hostd/fuzz_command
   (lib/B/Prog/LLVMFuzzerTestOneInput_s70.v and _s71.v at origin/ossv/recipes 3abc3740de97: the free step as a lemma
   of its own, s24_free_at, and each segment an application of it). S16's two program calls and S20's shadow store
   are the image-A twin's (image A's S16 .. S20 commit 68d839b8d799, lib/A/Prog/LLVMFuzzerTestOneInput_s24.v and its
   kit _s24k.v, ported here as the k24_* lemmas), over image B's own runs (s16_run1, s16_runC, s16_free3) and image
   B's cut statements (lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, image B's cut-statement lane). The image facts
   lt_img needs after a call come from the image-B listing owner's per-image record SegRecBase.seg_img_facts, and the
   stack-protector cells from SegRecCells.seg_rec_cells at each AR state.

   rule 24: proves function LLVMFuzzerTestOneInput (segments S16 .. S20 of its image-B walk). Reuse search, rule
   24: released units, the earlier proof delivery and working heads; the result is recorded with the commissioning
   brief; none: written new, adapted. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI00 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0p YC5d YG0q YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaNoChain SegObj SegGlob SegPgBase SegABase
SegRo SegRecBase SegRecCells PaDenot PaSB PaLibF PaLibG.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_c SegInstB LLVMFuzzerTestOneInput_defs
reac_declared_vlan_add_c reac_segconf_declared_c check_declared_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== pure facts of the model ===================================== *)
(* every byte of the driver's payload is a byte *)
Lemma s24_in_ok : forall (pl : list byte), Forall SegModel.byte_ok (seg_spec.seg_in pl).
Proof.
intros pl. unfold seg_spec.seg_in, seg_spec.zs. apply Forall_forall.
intros z Hz. apply in_map_iff in Hz as (b & <- & _).
pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H.
unfold SegModel.byte_ok. lia.
Qed.
(* the agreement theorem at this walk's payload *)
Lemma s24_harness_ok : forall (pl : list byte), SegModel.harness_ok (seg_spec.seg_pay pl) = true.
Proof. intros pl. unfold seg_spec.seg_pay. apply SegModel.segconf_agrees. apply s24_in_ok. Qed.
(* its last conjunct: the reader's declared table and the model's agree, which check_declared asks *)
Lemma s24_vlans : forall (pl : list byte),
  SegModel.vlans_are
    (SegModel.r_declared (seg_spec.seg_rc (SegModel.run (seg_spec.seg_pay pl)))
       (seg_spec.seg_tab0 pl) (seg_spec.seg_cap pl))
    (SegModel.m_declared (seg_spec.seg_mc (SegModel.run (seg_spec.seg_pay pl)))
       (seg_spec.seg_tab0 pl) (seg_spec.seg_cap pl))
    (seg_spec.seg_cap pl) = true.
Proof.
intros pl. pose proof (s24_harness_ok pl) as H.
unfold SegModel.harness_ok in H. unfold seg_spec.seg_tab0, seg_spec.seg_cap, seg_spec.seg_rc, seg_spec.seg_mc.
destruct (SegModel.run (seg_spec.seg_pay pl)) as [[c m] ret].
cbn [fst snd] in *.
repeat (apply andb_true_iff in H as [H ?H]).
assumption.
Qed.

(* two list steps (own copies, so no list lemma whose name or implicit arguments vary is needed) *)
Lemma s24m_nth_firstn : forall {A} (l : list A) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
intros A l n; revert l; induction n as [|n IH]; intros l k d Hk; [lia|].
destruct l as [|x l]; [destruct k; reflexivity|].
destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma s24m_nth_skipn : forall {A} (l : list A) j k d, nth k (skipn j l) d = nth (j + k) l d.
Proof.
intros A l j; revert l; induction j as [|j IH]; intros l k d; [reflexivity|].
destruct l as [|x l]; [destruct k; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the allocator record's laws are the kit's theorem (as image A's twin takes them); the walk hypotheses: the
   listing's runtime entries, the meter's laws (with set_fs, as the S00 walk and the image-A twin take them), the call
   target of every program function, image B's runtime symbols and the image-B listing owner's per-image record *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : seg_sig_prog.
Hypothesis HB : SegBSyms B.
Hypothesis IMGF : seg_img_facts SEGS B.
(* the runtime entry and the two callees these segments reach, each at every FP state. Their entries are listing
   terms (BASE + AF_<F>, which SIGP matches to the call target pa_sigma SS_<F>); the stacks, the read-only window
   and the stack-protector cells are SegInstB's pure parameters. *)
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis HDECLARED : forall fx0 : YK11.FPState,
  @reac_segconf_declared_c.reac_segconf_declared_contract fx0 rc SK SEGS B
    (BASE + AF_reac_segconf_declared) STK_reac_segconf_declared RLO_A RHI_A gotwA guardA.
Hypothesis HCHECK_DECLARED : forall fx0 : YK11.FPState,
  @check_declared_c.check_declared_contract fx0 rc SK SEGS B
    (BASE + AF_check_declared) STK_check_declared RLO_A RHI_A.

(* ===================================== the image facts, from the record ===================================== *)
Lemma s24_relro : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof. intros a Ha. exact (cif_relro_img _ _ IMGF a Ha). Qed.
(* the stack-protector cells at every AR state: the guard's .got word gotwA = 0xa3e98 is a runtime-owned const cell
   holding guardA = 0x5ff838, the guard an image byte (SegRecCells.seg_rec_cells, from the image-B listing owner) *)
Lemma s24_ssp : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Proof.
intros ly S W mem md HAR. destruct (seg_rec_cells SEGS B LAWS HB IMGF ly S W mem md HAR) as (_ & HG & _).
exact HG.
Qed.

(* ===================================== blocks ===================================== *)
(* in_app gives the kit's amem_range *)
Lemma s24_amem_of_app : forall p n, in_app p n -> amem_range p n.
Proof.
intros p n [H0 [HL | [HH1 HH2]]]; pose proof (proj1 alloc_ceiling_value) as HC;
unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
- left. lia.
- right. lia.
Qed.
(* a live block is a harness block: the whole of lt_hblk follows from AR and membership *)
Lemma s24_hblk_of_AR : forall ly S (W : world SEGS) mem md p n,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) p n.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (H16 & H4096 & Hceil & Happ & _ & _ & Hn).
destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [Hbs Hhull].
pose proof (req_size_pos n ltac:(lia)) as [Q1 Q2].
pose proof (proj1 alloc_ceiling_value) as HC.
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
unfold sa_addr.
split; [lia|]. split; [lia|].
split; [exact (s24_amem_of_app p n ltac:(eapply in_app_sub; [exact Happ | lia | lia | lia]))|].
split.
- exact (block_shadow_range _ _ p (req_size n) p n Hbs ltac:(lia) ltac:(lia)).
- intros Hn0 s Hs. apply Hhull.
  assert (Hdiv : shadow_addr (p + n - 1) / 8 <= shadow_addr (p + req_size n - 1) / 8)
    by (apply Z.div_le_mono; [lia | apply shadow_mono; lia]).
  lia.
Qed.

(* ===================================== the image facts across a call ===================================== *)
(* lt_img reads image bytes the runtime does not own, and the stack-protector cells: a reader that keeps those
   bytes, at an AR state (which gives the cells, s24_ssp), keeps lt_img (image A's S00 walk, s10_lt_img_kept) *)
Lemma s24_img_kept : forall cx ly' S' (W' : world SEGS) mem' md' (rd : reader),
  AR SEGS B ly' S' W' mem' md' ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   rdW W' mem' a = rd a) ->
  lt_img B cx rd -> lt_img B cx (rdW W' mem').
Proof.
intros cx ly' S' W' mem' md' rd HAR' K (HRO & HIM & HGI).
assert (KI : forall q n, sa_img SEGS B q n -> forall a, q <= a < q + n -> rdW W' mem' a = rd a).
{ intros q n0 Hq a Ha. destruct (Hq a Ha) as (H1 & H2 & H3). exact (K a H1 H2 H3). }
assert (KW : forall q n a, sa_img SEGS B q n -> q <= a -> a + 8 <= q + n -> rdword (rdW W' mem') a = rdword rd a).
{ intros q n0 a Hq H1 H2. apply rdword_ext. intros k Hk. apply (KI q n0 Hq). lia. }
assert (KL : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s (Ha & ((Hz & Hn0) & _) & Hp & Hr & Hi). split; [exact Ha|]. split; [split; [split|]|].
  - intros i Hix. rewrite length_app in Hix. cbn [length] in Hix.
    rewrite (KI _ _ Hi); [exact (Hz i ltac:(rewrite length_app; cbn [length]; lia)) | lia].
  - exact Hn0.
  - exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hr).
  - split; [exact Hp|]. split; [exact Hr | exact Hi]. }
destruct HIM as (Hm40 & Hm40i & HLF & HLR & (Hcp & Hci & Hcr) & HCa & (Hwp & Hwi & Hwr) & (Hrp & Hri & Hrr) & (Hg1 & Hg2)
  & HLP & HLT & HLI & HD1 & HD2 & HD3).
split; [|split].
- intros a Hro Ho He. rewrite <- (HRO a Hro Ho He). apply K; [|exact Ho | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
  exact (s24_relro a Hr).
- split; [|split; [exact Hm40i|]].
  { intros k Hk. rewrite (KI _ _ Hm40i); [exact (Hm40 k Hk) | cbn [Z.of_nat] in Hk |- *; lia]. }
  split; [intros s Hs; destruct (HLF s Hs) as [Hl Ha]; exact (conj (KL _ _ Hl) Ha)|].
  split; [intros s Hs; destruct (HLR s Hs) as [Hl Ha]; exact (conj (KL _ _ Hl) Ha)|].
  split.
  { split; [exact Hcp|]. split; [exact Hci|]. intros i Hi. destruct (Hcr i Hi) as (tp & Htp & Hl).
    exists tp. split; [|exact (KL _ _ Hl)]. rewrite (KW _ _ _ Hci); [exact Htp | |];
    unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *; lia. }
  split; [exact HCa|].
  split.
  { split; [exact Hwp|]. split; [exact Hwi|]. intros i Hi. destruct (Hwr i Hi) as (wp & Hwp' & Hl).
    exists wp. split; [|exact (KL _ _ Hl)]. rewrite (KW _ _ _ Hwi); [exact Hwp' | lia | lia]. }
  split.
  { split; [exact Hrp|]. split; [exact Hri|]. intros i Hi k Hk. rewrite (KI _ _ Hri);
    [exact (Hrr i Hi k Hk) | cbn [Z.of_nat] in Hk |- *; lia]. }
  split; [exact (s24_ssp ly' S' W' mem' md' HAR')|].
  split; [exact HLP|]. split; [exact HLT|]. split; [exact HLI|]. split; [exact HD1|]. split; [exact HD2 | exact HD3].
- intros i Hi. rewrite (KI _ _ HLI).
  + exact (HGI i Hi).
  + unfold LLVMFuzzerTestOneInput_c.LONGL_W, LLVMFuzzerTestOneInput_c.LONGL_N. lia.
Qed.

(* ===================================== the budget of a free ===================================== *)
Lemma s24_free_le_U : mo_free MT <= LT_U MT.
Proof. unfold LT_U. pose proof (mo_malloc_nonneg MT MTL 65536 ltac:(lia)). lia. Qed.
Lemma s24_U_nonneg : 0 <= LT_U MT.
Proof.
unfold LT_U. pose proof (mo_malloc_nonneg MT MTL 65536 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia.
Qed.
Lemma s24_bud_pre : forall cx ly S (W : world SEGS) mem md own k acc rem,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) own ly S W mem md k ->
  lt_bud MT cx S k acc rem -> 1 <= rem ->
  st_nev S < EV_MAX /\ mo_ok MT S (mo_free MT).
Proof.
intros cx ly S W mem md own k acc rem HBASE HJ HBUD Hrem.
pose proof HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _ & MOK0).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & Hk & _).
pose proof HBUD as (Hk0 & Hrem0 & Hkr & Hmle & Hacc & Hax).
pose proof s24_free_le_U as HU. pose proof s24_U_nonneg as HU0.
assert (Hrle : acc + mo_free MT <= XM_LTOI MT (x_pl cx)).
{ assert (Hm : 1 * LT_U MT <= rem * LT_U MT) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
split; [lia|].
apply (mo_ok_step MT MTL (x_S cx) S acc (mo_free MT)); [|exact Hmle].
apply (mo_ok_le MT MTL (x_S cx) (acc + mo_free MT) (XM_LTOI MT (x_pl cx)) MOK0). lia.
Qed.
Lemma s24_bud_step : forall cx S S2 k acc rem,
  lt_bud MT cx S k acc rem -> mo_le MT S S2 (mo_free MT) -> 1 <= rem ->
  lt_bud MT cx S2 (k + 1) (acc + mo_free MT) (rem - 1).
Proof.
intros cx S S2 k acc rem HBUD HLE Hrem.
pose proof HBUD as (Hk0 & Hrem0 & Hkr & Hmle & Hacc & Hax).
pose proof s24_free_le_U as HU. pose proof s24_U_nonneg as HU0.
pose proof (mo_free_nonneg MT MTL) as HF0.
assert (Hmul : (rem - 1) * LT_U MT = rem * LT_U MT - LT_U MT) by ring.
split; [lia|]. split; [lia|]. split; [lia|].
split; [exact (mo_le_trans MT MTL (x_S cx) S S2 acc (mo_free MT) Hmle HLE)|].
split; [lia | lia].
Qed.

(* ===================================== the stack, the chain and separation ===================================== *)
(* s1 = (sp0 - 352) rounded down to 32: where it lies and that it is 16-aligned *)
Lemma s24_s1_arith : forall cx ly,
  astk_ok STK_LLVMFuzzerTestOneInput ly (x_sp0 cx) ->
  x_s1 cx mod 16 = 0 /\ x_sp0 cx - 384 < x_s1 cx <= x_sp0 cx - 352 /\
  alloc_ceiling <= x_s1 cx /\ (x_s1 cx - x_sp0 cx) mod 16 = 0 /\
  0 <= x_s1 cx < 2 ^ 64 /\ 0 <= x_sp0 cx < 2 ^ 64 /\ x_sp0 cx <= ly_top ly.
Proof.
intros cx ly HS.
pose proof HS as (Hal & _ & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (proj1 alloc_ceiling_value) as HC.
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HR : 0 <= (x_sp0 cx - LT_FRAME) mod 32 < 32) by (apply Z.mod_pos_bound; lia).
assert (E16 : x_s1 cx mod 16 = 0).
{ unfold x_s1.
  assert (E : x_sp0 cx - LT_FRAME - (x_sp0 cx - LT_FRAME) mod 32 = (2 * ((x_sp0 cx - LT_FRAME) / 32)) * 16)
    by (pose proof (Z.div_mod (x_sp0 cx - LT_FRAME) 32 ltac:(lia)); lia).
  rewrite E. apply Z.mod_mul. lia. }
assert (EB : x_sp0 cx - 384 < x_s1 cx <= x_sp0 cx - 352).
{ unfold x_s1, LT_FRAME in *. lia. }
split; [exact E16|]. split; [exact EB|]. split; [lia|].
split; [rewrite Zminus_mod, E16, Hal; reflexivity|].
split; [lia|]. split; [lia | lia].
Qed.
(* the walk's stack is readable from s1 up: the entry's astack_pres carried over the journal *)
Lemma s24_stack_rd : forall cx ly S (W : world SEGS) mem md own k,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) own ly S W mem md k ->
  astack_rd ly (rdW W mem) (x_s1 cx).
Proof.
intros cx ly S W mem md own k HBASE HJ.
pose proof HBASE as (HPRE0 & HSP & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKOK & _).
destruct (s24_s1_arith cx (x_ly cx) HSTKOK) as (E16 & EB & Hc1 & Emod & Hr1 & Hr0 & Htop).
pose proof (proj1 alloc_ceiling_value) as HC.
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
eapply astack_rd_mono; [| eapply astack_rd_journal; [exact HJ | |]].
- lia.
- apply astack_rd_of_pres. exact HSP.
- intros a (r & Hr & Har) Hb. exfalso. cbn [In ltoi_PG] in Hr. destruct Hr as [<- | []].
  cbn [fst snd] in Har. unfold longlA, A_LONGL, LLVMFuzzerTestOneInput_c.LONGL_N in Har. lia.
Qed.
(* the frame chain at a call of this walk: s1 is the sp, SP0 the frame pointer *)
Lemma s24_chain : forall cx ly S (W : world SEGS) mem md own k (regsT : bvmap 5 word),
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) own ly S W mem md k ->
  getr regsT 2 = w64 (x_s1 cx) -> getr regsT 8 = w64 (x_sp0 cx) -> 4096 <= raZ regsT ->
  exists ch, chain_pre ly (rdW W mem) regsT ch.
Proof.
intros cx ly S W mem md own k regsT HBASE HJ H2 H8 Hra.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKOK & _).
destruct (s24_s1_arith cx (x_ly cx) HSTKOK) as (E16 & EB & Hc1 & Emod & Hr1 & Hr0 & Htop).
pose proof (s24_stack_rd cx ly S W mem md own k HBASE HJ) as HRD.
assert (Hsp : spZ regsT = x_s1 cx).
{ unfold spZ. rewrite H2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hs0 : s0Z regsT = x_sp0 cx).
{ unfold s0Z. rewrite H8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
destruct (achain_any ly (rdW W mem) (x_s1 cx) (x_sp0 cx) HRD ltac:(right; right; right; lia)) as [ch Hch].
exists ch. eapply achain_chain_pre; [exact Hch | rewrite Hsp; lia | exact Hs0 | exact Hra].
Qed.
(* an element of one half of a pairwise list and one of the other are related *)
Lemma s24_pairwise_cross : forall {X} (R : X -> X -> Prop) l1 l2 x y,
  pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z l1 IH]; intros l2 x y Hp Hx Hy; [destruct Hx|].
cbn [app pairwise] in Hp. destruct Hp as [Hf Hp]. destruct Hx as [<- | Hx].
- rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right. exact Hy.
- exact (IH l2 x y Hp Hx Hy).
Qed.
(* a live block and a live side-stack frame do not meet (AR_sep_law's one pairwise list) *)
Lemma s24_sep_frame_blk : forall ly S (W : world SEGS) mem md cid pos p n,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> In (p, n) (ablocks B ly S) ->
  zdisjoint (p, req_size n) (frame_addr ly cid pos, fs_frame_bytes cid).
Proof.
intros ly S W mem md cid pos p n HAR Hf Hb.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _].
apply (s24_pairwise_cross zdisjoint _ _ _ _ Hp).
- exact (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ Hb).
- exact (in_map (fun f : Z * Z => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hf).
Qed.
(* a client byte is not a shadow byte *)
Lemma s24_app_not_band : forall a, app_addr a -> ~ in_band_rw a.
Proof.
intros a [H0 H] Hb. pose proof (proj1 alloc_ceiling_value) as HC.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *.
destruct H as [H|H]; destruct Hb as [Hb|Hb]; lia.
Qed.
(* the shadow bytes of this walk's class-3 frame are shadow bytes *)
Lemma s24_frame_shadow_band : forall ly S (W : world SEGS) mem md pos i,
  AR SEGS B ly S W mem md -> In (LT_FCLS, pos) (frames S) -> 0 <= i < 64 ->
  in_band_rw (shadow_addr (frame_addr ly LT_FCLS pos) + i).
Proof.
intros ly S W mem md pos i HAR Hf Hi.
destruct (al_frames _ _ LAWS ly S W mem md LT_FCLS pos HAR Hf) as (Hal32 & Happ & _ & _).
assert (EFB : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
assert (E : shadow_addr (frame_addr ly LT_FCLS pos) + i = shadow_addr (frame_addr ly LT_FCLS pos + 8 * i)).
{ unfold shadow_addr. rewrite <- Z.add_assoc. f_equal.
  replace (frame_addr ly LT_FCLS pos + 8 * i) with (frame_addr ly LT_FCLS pos + i * 8) by ring.
  rewrite Z.div_add by lia. lia. }
rewrite E. apply (shadow_addr_in_band (frame_addr ly LT_FCLS pos) (fs_frame_bytes LT_FCLS) (8 * i) Happ).
rewrite EFB. lia.
Qed.

(* ===================================== one free ===================================== *)
(* pairwise of a symmetric relation survives a permutation *)
Lemma s24_pairwise_perm : forall {X} (R : X -> X -> Prop),
  (forall x y, R x y -> R y x) -> forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros X R Hsym l l' HP. induction HP as [|x l l' HP IH|x y l|l1 l2 l3 HP1 IH1 HP2 IH2]; intros H.
- exact H.
- cbn [pairwise] in H |- *. destruct H as [Hf Hp]. split; [|exact (IH Hp)].
  rewrite Forall_forall in Hf |- *. intros z Hz. apply Hf. exact (Permutation_in z (Permutation_sym HP) Hz).
- cbn [pairwise] in H |- *. destruct H as [Hf [Hg Hp]].
  assert (Hyx : R y x) by (inversion Hf; assumption).
  assert (Hfl : Forall (R y) l) by (inversion Hf; assumption).
  split; [apply Forall_cons; [exact (Hsym _ _ Hyx) | exact Hg] | split; [exact Hfl | exact Hp]].
- exact (IH2 (IH1 H)).
Qed.
(* the head of the live-block list is not in its tail: a block does not meet itself *)
Lemma s24_blk_fresh : forall ly S (W : world SEGS) mem md p n l,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((p, n) :: l) -> ~ In (p, n) l.
Proof.
intros ly S W mem md p n l HAR HP Hin.
assert (H1 : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR H1) as (_ & _ & _ & _ & _ & Hpw & Hn).
pose proof (req_size_pos n ltac:(lia)) as [Q1 _].
assert (Hsym : forall x y : Z * Z, zdisjoint x y -> zdisjoint y x).
{ intros [a b] [c d] [Hd|Hd]; unfold zdisjoint in *; cbn [fst snd] in *; [right | left]; lia. }
assert (HPm : Permutation (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B ly S))
                          ((p, req_size n) :: map (fun b : Z * Z => (fst b, req_size (snd b))) l))
  by (apply (Permutation_map (fun b : Z * Z => (fst b, req_size (snd b)))) in HP; exact HP).
pose proof (s24_pairwise_perm zdisjoint Hsym _ _ HPm Hpw) as Hpw2.
cbn [pairwise] in Hpw2. destruct Hpw2 as [Hf _]. rewrite Forall_forall in Hf.
pose proof (Hf (p, req_size n)
  (in_map (fun b : Z * Z => (fst b, req_size (snd b))) l (p, n) Hin)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* reading a callee-saved register out of aregs_preserved *)
Lemma s24_pres_get : forall (regs regs' : bvmap 5 word) (r : Z) (rr : bv 5),
  aregs_preserved regs regs' -> acallee_saved r -> Z_to_bv 5 r = rr -> getr regs' rr = getr regs rr.
Proof. intros regs regs' r rr HP Hr <-. exact (HP r Hr). Qed.
(* what a free of this walk keeps for the rest of the segment: every byte from s1 up, which holds this walk's
   stack slots and the registers the entry saved *)
Definition s24_kept (cx : lcx) (W : world SEGS) mem (W2 : world SEGS) mem2 : Prop :=
  forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W mem a.
Lemma s24_kept_word : forall cx (W : world SEGS) mem (W2 : world SEGS) mem2 a v,
  s24_kept cx W mem W2 mem2 -> x_s1 cx <= a -> a + 8 <= 2 ^ 64 ->
  rdword (rdW W mem) a = Some v -> rdword (rdW W2 mem2) a = Some v.
Proof.
intros cx W mem W2 mem2 a v HK H1 H2 H. rewrite (rdword_ext (rdW W mem) (rdW W2 mem2) a); [exact H|].
intros kk Hkk. apply HK; lia.
Qed.
(* THE FREE STEP. At the free wrapper's entry, with the pointer in a0 and the return address in ra: the block at
   the head of the walk's own block list is released, one event is spent, and every other part of lt_core is
   carried over (image bytes by acall_kept's image clause, the frame and its shadow by its frame clause, the
   walk's stack by its first clause). The image-B twin of fuzz_command's lib/B/Prog/LLVMFuzzerTestOneInput_s70.v
   ltf_free, with this walk's class-3 side-stack frame added. *)
Lemma s24_free_at : forall cx O ly S (W : world SEGS) (regs regsT : bvmap 5 word) mem md k acc rem o pa n retk Q,
  lt_base B MT cx ->
  lt_core B MT cx ly S W regs mem md k acc rem o ((pa, n) :: O) ->
  aregs_preserved regs regsT ->
  getr regsT 10 = w64 pa -> getr regsT 1 = w64 (BASE + retk) ->
  0 <= retk < 2 ^ 40 -> retk mod 2 = 0 -> 1 <= rem ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
     lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) (rem - 1) o O ->
     aregs_preserved regs regs2 -> s24_kept cx W mem W2 mem2 ->
     SRr SEGS W2 (cfg_at SEGS (BASE + retk) regs2 mem2 md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx O ly S W regs regsT mem md k acc rem o pa n retk Q
  HBASE HCORE HPRES Ha0 Hra Hretk Hretk2 Hrem HC.
pose proof HCORE as (HFRAME & HIMG & HBLK & HBUD).
pose proof HFRAME as (HJ & H2 & H3 & H4 & H8 & H9 & HSAV & HW0 & HW8 & HW16 & HWF & HSHB & HZS & HSH).
pose proof HBASE as (HPRE0 & HSP & _).
pose proof HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HFR0 & _).
pose proof HPRE0 as (HAR0 & Hrok0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & HSTKOK & F5 & HQT).
destruct (s24_s1_arith cx (x_ly cx) HSTKOK) as (E16 & EB & Hc1 & Emod & Hr1 & Hr0 & Htop0).
pose proof (proj1 alloc_ceiling_value) as HAC.
pose proof pa_base_lo as HBLO. pose proof (pa_B_ok (L := seg_listing)) as (HB0 & HB1 & HB4).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
pose proof HSTKOK as (Hal16' & _ & Hceil2 & Hslo2 & Hshi2 & H47' & _ & _ & _).
assert (HASTK : ASTACK = 16384) by reflexivity.
(* the frames at this point: this walk's own class-3 frame alone *)
assert (Hframes : frames S = [(LT_FCLS, x_fpos cx)]) by (rewrite Hfrs, HFR0; reflexivity).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hframes; left; reflexivity).
destruct (al_layout _ _ LAWS (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) ly HAR0 Hly) as (Eab & Efa & Eown).
assert (EFR : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by (unfold x_fr; apply Efa).
assert (EFB : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
(* the registers at the call *)
assert (R2 : getr regsT 2 = w64 (x_s1 cx)).
{ etransitivity; [exact (s24_pres_get regs regsT 2 2%bv HPRES ltac:(unfold acallee_saved; lia)
    ltac:(vm_compute; reflexivity)) | exact H2]. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ etransitivity; [exact (s24_pres_get regs regsT 3 3%bv HPRES ltac:(unfold acallee_saved; lia)
    ltac:(vm_compute; reflexivity)) |]. etransitivity; [exact H3 | exact Hgp0]. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ etransitivity; [exact (s24_pres_get regs regsT 4 4%bv HPRES ltac:(unfold acallee_saved; lia)
    ltac:(vm_compute; reflexivity)) |]. etransitivity; [exact H4 | exact Htp0]. }
assert (R8 : getr regsT 8 = w64 (x_sp0 cx)).
{ etransitivity; [exact (s24_pres_get regs regsT 8 8%bv HPRES ltac:(unfold acallee_saved; lia)
    ltac:(vm_compute; reflexivity)) | exact H8]. }
assert (Hsp : spZ regsT = x_s1 cx).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hraok : YK0s.ret_ok (getr regsT 1)) by (rewrite Hra; apply ret_ok_codeptr_v; [lia | exact Hretk2]).
assert (Hra4 : 4096 <= raZ regsT).
{ unfold raZ. rewrite Hra. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* the block to free is live, and it is not one of the entry's *)
assert (Hin : In (pa, n) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HBLK)). left. reflexivity. }
assert (Hfresh : ~ In (pa, n) (O ++ x_bl0 B cx))
  by exact (s24_blk_fresh ly S W mem md pa n (O ++ x_bl0 B cx) HAR HBLK).
destruct (al_blocks _ _ LAWS ly S W mem md pa n HAR Hin) as (B16 & B4096 & Bceil & Bapp & _ & _ & Bn).
pose proof (req_size_pos n ltac:(lia)) as [Q1 Q2].
(* the chain and the budget *)
destruct (s24_chain cx ly S W mem md [(LT_FCLS, x_fpos cx)] k regsT HBASE HJ R2 R8 Hra4) as [ch Hch].
destruct (s24_bud_pre cx ly S W mem md [(LT_FCLS, x_fpos cx)] k acc rem HBASE HJ HBUD Hrem) as [Hnev1 MOK1].
(* the call of the free wrapper *)
eapply SRr_bind.
{ exact (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE4 fx) W regsT mem
    STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
    [(LT_FCLS, x_fpos cx)] ly S md k pa n (x_s1 cx - x_sp0 cx) (getr regsT 1) ch
    HJ Hin Ha0 ltac:(rewrite Hsp; lia) Emod ltac:(lia) ltac:(lia) R3 R4 eq_refl Hraok Hnev1 Hch
    ltac:(intros Hb; exfalso; apply Hfresh; apply in_or_app; right; exact Hb) MOK1). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl & Ebl2) & Hfr2 & HK2 & MLE & HJin).
pose proof HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx) - ASTACK) with (x_s1 cx - ASTACK) in K1, K4, K5, K6 by ring.
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in K1, K4, K5, K6 by ring.
(* what the free kept of this walk's stack *)
assert (KEEP : s24_kept cx W mem W2 mem2) by (intros a Ha; apply K1; lia).
(* what it kept of this walk's frame and of that frame's shadow *)
assert (KEEPF : forall a, in_zr a (x_fr cx, 512) -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. apply (K4 LT_FCLS (x_fpos cx) a HinF).
  - left. unfold frame_rng. cbn [fst snd]. rewrite EFR, EFB. exact Ha.
  - intros Hb. cbv beta in Hb.
    pose proof (s24_sep_frame_blk ly S W mem md LT_FCLS (x_fpos cx) pa n HAR HinF Hin) as Hd.
    rewrite EFR, EFB in Hd. unfold zdisjoint, in_zr in *. cbn [fst snd] in *. lia. }
assert (KEEPS : forall i, 0 <= i < 64 -> rdW W2 mem2 (x_sh cx + i) = rdW W mem (x_sh cx + i)).
{ intros i Hi. apply (K4 LT_FCLS (x_fpos cx) (x_sh cx + i) HinF).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFR, EFB. change (512 / 8) with 64. unfold x_sh. lia.
  - intros Hb. cbv beta in Hb.
    apply (s24_app_not_band (x_sh cx + i)).
    + apply (in_app_addr pa (req_size n)); [exact Bapp | lia].
    + unfold x_sh. rewrite <- EFR. exact (s24_frame_shadow_band ly S W mem md (x_fpos cx) i HAR HinF Hi). }
(* the three sizes the walk re-uses *)
assert (HWORD : forall a v, x_s1 cx <= a -> a + 8 <= 2 ^ 64 ->
  rdword (rdW W mem) a = Some v -> rdword (rdW W2 mem2) a = Some v)
  by (intros a v H1 Hb Hv; exact (s24_kept_word cx W mem W2 mem2 a v KEEP H1 Hb Hv)).
assert (HWORDF : forall a v, in_zr a (x_fr cx, 505) ->
  rdword (rdW W mem) a = Some v -> rdword (rdW W2 mem2) a = Some v).
{ intros a v Ha Hv. rewrite (rdword_ext (rdW W mem) (rdW W2 mem2) a); [exact Hv|].
  intros kk Hkk. apply KEEPF. unfold in_zr in *. cbn [fst snd] in *. lia. }
(* lt_core at the new state *)
rewrite Hra.
apply (HC ly2 S2 W2 regs2 mem2 md2); [| exact (aregs_preserved_trans _ _ _ HPRES HP2) | exact KEEP].
split.
{ (* lt_frame *)
  split; [exact HJ2|].
  pose proof (aregs_preserved_trans _ _ _ HPRES HP2) as HPA.
  split; [etransitivity; [exact (s24_pres_get regs regs2 2 2%bv HPA ltac:(unfold acallee_saved; lia)
    ltac:(vm_compute; reflexivity)) | exact H2]|].
  split; [etransitivity; [exact (s24_pres_get regs regs2 3 3%bv HPA ltac:(unfold acallee_saved; lia)
    ltac:(vm_compute; reflexivity)) | exact H3]|].
  split; [etransitivity; [exact (s24_pres_get regs regs2 4 4%bv HPA ltac:(unfold acallee_saved; lia)
    ltac:(vm_compute; reflexivity)) | exact H4]|].
  split; [etransitivity; [exact (s24_pres_get regs regs2 8 8%bv HPA ltac:(unfold acallee_saved; lia)
    ltac:(vm_compute; reflexivity)) | exact H8]|].
  split; [etransitivity; [exact (s24_pres_get regs regs2 9 9%bv HPA ltac:(unfold acallee_saved; lia)
    ltac:(vm_compute; reflexivity)) | exact H9]|].
  split.
  { intros i r Hi. apply HWORD; [| |exact (HSAV i r Hi)].
    - assert (Hi13 : (i < length LT_SAVED)%nat)
        by (apply (proj1 (nth_error_Some LT_SAVED i)); rewrite Hi; discriminate).
      change (length LT_SAVED) with 13%nat in Hi13.
      assert (Hiz : 1 <= Z.of_nat (Datatypes.S i) <= 13) by (rewrite Nat2Z.inj_succ; lia). lia.
    - lia. }
  split; [apply (HWORDF (x_fr cx) LT_HDR0); [unfold in_zr; cbn [fst snd]; lia | exact HW0]|].
  split; [apply (HWORDF (x_fr cx + 8) _); [unfold in_zr; cbn [fst snd]; lia | exact HW8]|].
  split; [apply (HWORDF (x_fr cx + 16) _); [unfold in_zr; cbn [fst snd]; lia | exact HW16]|].
  split; [apply (HWORDF (x_fr cx + LT_FLAGW) _); [unfold in_zr, LT_FLAGW; cbn [fst snd]; lia | exact HWF]|].
  split; [apply HWORD; [lia | lia | exact HSHB]|].
  split.
  { intros i Hi. rewrite KEEPS; [exact (HZS i Hi)|].
    rewrite (lt_fsh_len o) in Hi. lia. }
  apply HWORD; [lia | lia | exact HSH]. }
split.
{ (* lt_img *)
  apply (s24_img_kept cx ly2 S2 W2 mem2 md2 (rdW W mem) (proj1 HJ2)); [| exact HIMG].
  intros a Hi Ho He. exact (K3 a Hi Ho He). }
split.
{ (* the blocks left *)
  unfold lt_blocks. rewrite Ebl2. apply (Permutation_cons_inv (a := (pa, n))).
  eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- Ebl. exact HBLK. }
exact (s24_bud_step cx S S2 k acc rem HBUD MLE Hrem).
Qed.

(* a word read at or above lo survives a reader that keeps everything from lo up *)
Lemma s24_word_of_kept : forall (W2 : world SEGS) mem2 (W : world SEGS) mem a v lo,
  (forall x, lo <= x < 2 ^ 64 -> rdW W2 mem2 x = rdW W mem x) -> lo <= a -> a + 8 <= 2 ^ 64 ->
  rdword (rdW W mem) a = Some v -> rdword (rdW W2 mem2) a = Some v.
Proof.
intros W2 mem2 W mem a v lo HK H1 H2 H.
rewrite (rdword_ext (rdW W mem) (rdW W2 mem2) a); [exact H|]. intros kk Hkk. apply HK; lia.
Qed.
(* the core at the same allocator state, read through a reader that shows the same bytes: what a plain run of
   instructions that make no memory access leaves (frame_of over an empty region list) *)
Lemma s24_core_rd_eq : forall cx ly S (W : world SEGS) regs mem mem' md md' k acc rem o O,
  (forall a, rdW W mem' a = rdW W mem a) ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  lt_core B MT cx ly S W regs mem md k acc rem o O ->
  lt_core B MT cx ly S W regs mem' md' k acc rem o O.
Proof.
intros cx ly S W regs mem mem' md md' k acc rem o O Heq HJ2 HCORE.
pose proof HCORE as (HFRAME & HIMG & HBLK & HBUD).
pose proof HFRAME as (HJ & H2 & H3 & H4 & H8 & H9 & HSAV & HW0 & HW8 & HW16 & HWF & HSHB & HZS & HSH).
assert (RW : forall a v, rdword (rdW W mem) a = Some v -> rdword (rdW W mem') a = Some v).
{ intros a v Hv. rewrite (rdword_ext (rdW W mem) (rdW W mem') a); [exact Hv|]. intros kk _. apply Heq. }
split; [|split; [|split]].
- split; [exact HJ2|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact H8|]. split; [exact H9|].
  split; [intros i r Hi; exact (RW _ _ (HSAV i r Hi))|].
  split; [exact (RW _ _ HW0)|]. split; [exact (RW _ _ HW8)|]. split; [exact (RW _ _ HW16)|].
  split; [exact (RW _ _ HWF)|]. split; [exact (RW _ _ HSHB)|].
  split; [intros i Hi; rewrite Heq; exact (HZS i Hi)|].
  exact (RW _ _ HSH).
- apply (s24_img_kept cx ly S W mem' md' (rdW W mem) (proj1 HJ2)); [intros a _ _ _; apply Heq | exact HIMG].
- exact HBLK.
- exact HBUD.
Qed.

(* ================== the symbolic seed of a point whose run makes no memory access ================== *)
Definition s24_facts : facts := mkFacts [] [] [].
Definition s24_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None s24_facts.
Definition s24_Bx : sv := SLit SHADOW_OFF.
Definition s24_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition s24_E (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Lemma s24_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi SEGS (@pa_val _ seg_listing PI) (s24_E regs) (s24_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS s24_Bx [] (s24_E regs) (mrestrict (w_H W) mem)
  /\ img_env (@pa_val _ seg_listing PI) A_LIM (s24_E regs)
  /\ env_agree 32 (Ereg regs []) (s24_E regs)
  /\ (forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s24_E regs) n = getr regs rr).
Proof.
intros W regs mem pc.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (s24_E regs) n = ew (Ereg regs []) n)
  by (intros n Hn; unfold s24_E; apply Eimg_low; exact Hn).
split.
- unfold s24_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold s24_E. apply regs_ok_Eimg_Ereg.
  + reflexivity.
  + apply Forall_nil.
  + first [ exact I | constructor
          | apply pairwise_disjoint_of_extents; cbn; first [exact I | constructor | repeat split] ].
  + unfold facts_ok, s24_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto.
- split; [apply Forall_nil|].
  split; [unfold s24_E; apply Eimg_env|].
  split; [split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | reflexivity]|].
  intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

(* ========================= S17: 0x85e9c `mv a0,s5`, 0x85ea0 `jal free`: free(tab) ========================= *)
Theorem lt_seg_S17 : lt_seg_S17_stmt B MT.
Proof.
unfold lt_seg_S17_stmt. intros HA.
unfold LT_K85e9c_stmt. intros cx ly S W regs mem md k acc c m tab HBASE HFRM HCORE Hc Hm Htab R18 R21 R24 HSL.
pose proof (paj_run B LAWS) as RUN.
pose proof HCORE as (HFRAMEc & HIMGc & HBLKc & HBUDc).
pose proof HFRAMEc as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKOK & _).
destruct (s24_s1_arith cx (x_ly cx) HSTKOK) as (E16 & EB & Hc1 & Emod & Hr1 & Hr0 & Htop0).
pose proof HSTKOK as (Hal16 & _ & Hceil2 & Hslo2 & Hshi2 & H47 & _ & _ & _).
pose proof (proj1 alloc_ceiling_value) as HAC.
destruct (s24_seed W regs mem LO_K85e9c) as (HS & SHOK & HEI & HAE & EEo).
paj_run_tok RUN HS HJ SHOK s24_Bspan; try solve [apply awr_ok_nil].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
(* the two instructions write no byte *)
assert (Emem : forall x : word, ms_mem ms x = mem x) by (intros x; apply HF; intros (r & [] & _)).
assert (Heq : forall a, rdW W (ms_mem ms) a = rdW W mem a).
{ intros a. unfold aview, mbyte, mrestrict. rewrite Emem. reflexivity. }
pose proof (s24_core_rd_eq cx ly S W regs mem (ms_mem ms) md mdv k acc 3 LFO_N
  [(tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] Heq HJ HCORE) as HCORE'.
(* the free wrapper's entry, with tab in a0 and 0x85ea4 in ra *)
pmkst HS. rewrite (pal_free B TL).
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
assert (HPRES : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs []); [exact HS | exact HAE | vm_compute; reflexivity]. }
assert (Ea0 : getr (ms_regs ms) 10 = w64 tab).
{ rewrite P10. rewrite (EEo 21%nat (21%bv : bv 5) ltac:(reflexivity)). exact R21. }
assert (Era : getr (ms_regs ms) 1 = w64 (BASE + LO_K85ea4)).
{ rewrite P1. unfold w64, LO_K85ea4. reflexivity. }
apply (s24_free_at cx [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ly S W regs (ms_regs ms)
  (ms_mem ms) mdv k acc 3 LFO_N tab (x_tabn cx) LO_K85ea4 (lt_post B MT cx)
  HBASE HCORE' HPRES Ea0 Era ltac:(unfold LO_K85ea4; lia) ltac:(unfold LO_K85ea4; reflexivity) ltac:(lia)).
intros ly2 S2 W2 regs2 mem2 md2 HCORE2 HPRES2 KEEP2.
assert (KEEPa : forall x, x_s1 cx <= x < 2 ^ 64 -> rdW W2 mem2 x = rdW W mem x)
  by (intros x Hx; rewrite (KEEP2 x Hx); apply Heq).
pose proof HCORE2 as (HFRAME2 & _ & HBLK2 & _).
pose proof HFRAME2 as (HJ2 & _).
pose proof (proj1 HJ2) as HAR2.
apply (HA fx cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) c m HBASE HFRM HCORE2).
- apply (s24_hblk_of_AR ly2 S2 W2 mem2 md2); [exact HAR2|].
  apply (Permutation_in _ (Permutation_sym HBLK2)). right. left. reflexivity.
- apply (s24_hblk_of_AR ly2 S2 W2 mem2 md2); [exact HAR2|].
  apply (Permutation_in _ (Permutation_sym HBLK2)). left. reflexivity.
- etransitivity; [exact (s24_pres_get regs regs2 18 18%bv HPRES2 ltac:(unfold acallee_saved; lia)
    ltac:(vm_compute; reflexivity)) | exact R18].
- etransitivity; [exact (s24_pres_get regs regs2 24 24%bv HPRES2 ltac:(unfold acallee_saved; lia)
    ltac:(vm_compute; reflexivity)) | exact R24].
- intros off v Hoff.
  assert (Hoff2 : off = 16 \/ off = 24)
    by (unfold LT_LF in Hoff; cbn [In] in Hoff; destruct Hoff as [Hq|[Hq|[]]]; injection Hq as <- _; auto).
  apply (s24_word_of_kept W2 mem2 W mem (x_s1 cx + off) v (x_s1 cx) KEEPa);
    [lia | lia | exact (HSL off v Hoff)].
Qed.

(* ========================= S18: 0x85ea4 `mv a0,s8`, 0x85ea8 `jal free`: free(m) ========================= *)
Theorem lt_seg_S18 : lt_seg_S18_stmt B MT.
Proof.
unfold lt_seg_S18_stmt. intros HA.
unfold LT_K85ea4_stmt. intros cx ly S W regs mem md k acc c m HBASE HFRM HCORE Hc Hm R18 R24 HSL.
pose proof (paj_run B LAWS) as RUN.
pose proof HCORE as (HFRAMEc & HIMGc & HBLKc & HBUDc).
pose proof HFRAMEc as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKOK & _).
destruct (s24_s1_arith cx (x_ly cx) HSTKOK) as (E16 & EB & Hc1 & Emod & Hr1 & Hr0 & Htop0).
pose proof HSTKOK as (Hal16 & _ & Hceil2 & Hslo2 & Hshi2 & H47 & _ & _ & _).
pose proof (proj1 alloc_ceiling_value) as HAC.
destruct (s24_seed W regs mem LO_K85ea4) as (HS & SHOK & HEI & HAE & EEo).
paj_run_tok RUN HS HJ SHOK s24_Bspan; try solve [apply awr_ok_nil].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (Emem : forall x : word, ms_mem ms x = mem x) by (intros x; apply HF; intros (r & [] & _)).
assert (Heq : forall a, rdW W (ms_mem ms) a = rdW W mem a).
{ intros a. unfold aview, mbyte, mrestrict. rewrite Emem. reflexivity. }
pose proof (s24_core_rd_eq cx ly S W regs mem (ms_mem ms) md mdv k acc 2 LFO_N
  [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] Heq HJ HCORE) as HCORE'.
pmkst HS. rewrite (pal_free B TL).
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
assert (HPRES : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs []); [exact HS | exact HAE | vm_compute; reflexivity]. }
assert (Ea0 : getr (ms_regs ms) 10 = w64 m).
{ rewrite P10. rewrite (EEo 24%nat (24%bv : bv 5) ltac:(reflexivity)). exact R24. }
assert (Era : getr (ms_regs ms) 1 = w64 (BASE + LO_K85eac)).
{ rewrite P1. unfold w64, LO_K85eac. reflexivity. }
apply (s24_free_at cx [(c, seg_spec.SEG_C_SIZE)] ly S W regs (ms_regs ms)
  (ms_mem ms) mdv k acc 2 LFO_N m seg_spec.SEG_M_SIZE LO_K85eac (lt_post B MT cx)
  HBASE HCORE' HPRES Ea0 Era ltac:(unfold LO_K85eac; lia) ltac:(unfold LO_K85eac; reflexivity) ltac:(lia)).
intros ly2 S2 W2 regs2 mem2 md2 HCORE2 HPRES2 KEEP2.
assert (KEEPa : forall x, x_s1 cx <= x < 2 ^ 64 -> rdW W2 mem2 x = rdW W mem x)
  by (intros x Hx; rewrite (KEEP2 x Hx); apply Heq).
pose proof HCORE2 as (HFRAME2 & _ & HBLK2 & _).
pose proof HFRAME2 as (HJ2 & _).
pose proof (proj1 HJ2) as HAR2.
apply (HA fx cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) c HBASE HFRM HCORE2).
- apply (s24_hblk_of_AR ly2 S2 W2 mem2 md2); [exact HAR2|].
  apply (Permutation_in _ (Permutation_sym HBLK2)). left. reflexivity.
- etransitivity; [exact (s24_pres_get regs regs2 18 18%bv HPRES2 ltac:(unfold acallee_saved; lia)
    ltac:(vm_compute; reflexivity)) | exact R18].
- intros off v Hoff.
  assert (Hoff2 : off = 16 \/ off = 24)
    by (unfold LT_LF in Hoff; cbn [In] in Hoff; destruct Hoff as [Hq|[Hq|[]]]; injection Hq as <- _; auto).
  apply (s24_word_of_kept W2 mem2 W mem (x_s1 cx + off) v (x_s1 cx) KEEPa);
    [lia | lia | exact (HSL off v Hoff)].
Qed.

(* ========================= S19: 0x85eac `mv a0,s2`, 0x85eb0 `jal free`: free(c) ========================= *)
Theorem lt_seg_S19 : lt_seg_S19_stmt B MT.
Proof.
unfold lt_seg_S19_stmt. intros HA.
unfold LT_K85eac_stmt. intros cx ly S W regs mem md k acc c HBASE HFRM HCORE Hc R18 HSL.
pose proof (paj_run B LAWS) as RUN.
pose proof HCORE as (HFRAMEc & HIMGc & HBLKc & HBUDc).
pose proof HFRAMEc as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKOK & _).
destruct (s24_s1_arith cx (x_ly cx) HSTKOK) as (E16 & EB & Hc1 & Emod & Hr1 & Hr0 & Htop0).
pose proof HSTKOK as (Hal16 & _ & Hceil2 & Hslo2 & Hshi2 & H47 & _ & _ & _).
pose proof (proj1 alloc_ceiling_value) as HAC.
destruct (s24_seed W regs mem LO_K85eac) as (HS & SHOK & HEI & HAE & EEo).
paj_run_tok RUN HS HJ SHOK s24_Bspan; try solve [apply awr_ok_nil].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (Emem : forall x : word, ms_mem ms x = mem x) by (intros x; apply HF; intros (r & [] & _)).
assert (Heq : forall a, rdW W (ms_mem ms) a = rdW W mem a).
{ intros a. unfold aview, mbyte, mrestrict. rewrite Emem. reflexivity. }
pose proof (s24_core_rd_eq cx ly S W regs mem (ms_mem ms) md mdv k acc 1 LFO_N
  [(c, seg_spec.SEG_C_SIZE)] Heq HJ HCORE) as HCORE'.
pmkst HS. rewrite (pal_free B TL).
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
assert (HPRES : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs []); [exact HS | exact HAE | vm_compute; reflexivity]. }
assert (Ea0 : getr (ms_regs ms) 10 = w64 c).
{ rewrite P10. rewrite (EEo 18%nat (18%bv : bv 5) ltac:(reflexivity)). exact R18. }
assert (Era : getr (ms_regs ms) 1 = w64 (BASE + LO_K85eb4)).
{ rewrite P1. unfold w64, LO_K85eb4. reflexivity. }
apply (s24_free_at cx [] ly S W regs (ms_regs ms)
  (ms_mem ms) mdv k acc 1 LFO_N c seg_spec.SEG_C_SIZE LO_K85eb4 (lt_post B MT cx)
  HBASE HCORE' HPRES Ea0 Era ltac:(unfold LO_K85eb4; lia) ltac:(unfold LO_K85eb4; reflexivity) ltac:(lia)).
intros ly2 S2 W2 regs2 mem2 md2 HCORE2 HPRES2 KEEP2.
assert (KEEPa : forall x, x_s1 cx <= x < 2 ^ 64 -> rdW W2 mem2 x = rdW W mem x)
  by (intros x Hx; rewrite (KEEP2 x Hx); apply Heq).
apply (HA fx cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) HBASE HFRM HCORE2).
intros off v Hoff.
assert (Hoff2 : off = 16 \/ off = 24)
  by (unfold LT_LF in Hoff; cbn [In] in Hoff; destruct Hoff as [Hq|[Hq|[]]]; injection Hq as <- _; auto).
apply (s24_word_of_kept W2 mem2 W mem (x_s1 cx + off) v (x_s1 cx) KEEPa);
  [lia | lia | exact (HSL off v Hoff)].
Qed.

(* ===================== what segment S16's two program calls need of the walk ===================== *)
(* the frame chain at a call, in the form cl_callS_wide asks for *)
Lemma s24_achain : forall cx ly S (W : world SEGS) mem md own k,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) own ly S W mem md k ->
  exists ch, achain ly (rdW W mem) (x_s1 cx) (x_sp0 cx) ch.
Proof.
intros cx ly S W mem md own k HBASE HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKOK & _).
destruct (s24_s1_arith cx (x_ly cx) HSTKOK) as (E16 & EB & Hc1 & Emod & Hr1 & Hr0 & Htop0).
pose proof (s24_stack_rd cx ly S W mem md own k HBASE HJ) as HRD.
exact (achain_any ly (rdW W mem) (x_s1 cx) (x_sp0 cx) HRD ltac:(right; right; right; lia)).
Qed.

(* ===================== segment S16's first run: 0x85e50 .. 0x85e70, the four slot loads ===================== *)
(* a word a reader shows is a 64-bit value *)
Lemma s24_rdword_rng : forall (W : world SEGS) mem a v, rdword (rdW W mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros W mem a v E. unfold rdword in E.
destruct (rdW W mem a) as [b0|] eqn:E0; [|discriminate].
destruct (rdW W mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (rdW W mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (rdW W mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (rdW W mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (rdW W mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (rdW W mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (rdW W mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection E as <-.
pose proof (sa_aview_rng SEGS (w_H W) mem _ _ E0). pose proof (sa_aview_rng SEGS (w_H W) mem _ _ E1).
pose proof (sa_aview_rng SEGS (w_H W) mem _ _ E2). pose proof (sa_aview_rng SEGS (w_H W) mem _ _ E3).
pose proof (sa_aview_rng SEGS (w_H W) mem _ _ E4). pose proof (sa_aview_rng SEGS (w_H W) mem _ _ E5).
pose proof (sa_aview_rng SEGS (w_H W) mem _ _ E6). pose proof (sa_aview_rng SEGS (w_H W) mem _ _ E7).
lia.
Qed.
(* the symbolic seed of 0x85e50: the four words the four `ld`s take from the s1 slots 40, 48, 104 and 168, in a
   read-only region of the s1 atom; s1 itself is 16-aligned and on the stack (the donor's ltf_wseed shape) *)
Definition s16_rs1 : smem :=
  [YP09.mkRegion (Some 9%nat) 40 176 40 40
     [YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 8 (SOff 35 0));
      YP09.mkChunk 104 (CVal 8 (SOff 33 0)); YP09.mkChunk 168 (CVal 8 (SOff 32 0))]].
Definition s16_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition s16_ss1 (pc : Z) : sstate := mkSS pc sr_atoms s16_rs1 None s16_facts.
Definition s16_E1 (regs : bvmap 5 word) (c tab cap np : Z) : env :=
  Eimg (Ereg regs [Z_to_bv 64 c; Z_to_bv 64 tab; Z_to_bv 64 cap; Z_to_bv 64 np]).
Lemma s16_seed1 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc c tab cap np,
  2 ^ 46 <= bv_unsigned (getr regs 9) <= 2 ^ 47 -> bv_unsigned (getr regs 9) mod 16 = 0 ->
  rdword (rdW W mem) (bv_unsigned (getr regs 9) + 40) = Some cap ->
  rdword (rdW W mem) (bv_unsigned (getr regs 9) + 48) = Some np ->
  rdword (rdW W mem) (bv_unsigned (getr regs 9) + 104) = Some tab ->
  rdword (rdW W mem) (bv_unsigned (getr regs 9) + 168) = Some c ->
  st_ok_pi SEGS VAL (s16_E1 regs c tab cap np) (s16_ss1 pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS s24_Bx [] (s16_E1 regs c tab cap np) (mrestrict (w_H W) mem)
  /\ img_env VAL A_LIM (s16_E1 regs c tab cap np)
  /\ env_agree 32 (Ereg regs [Z_to_bv 64 c; Z_to_bv 64 tab; Z_to_bv 64 cap; Z_to_bv 64 np])
       (s16_E1 regs c tab cap np)
  /\ (forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s16_E1 regs c tab cap np) n = getr regs rr).
Proof.
intros W regs mem pc c tab cap np Hsp Hal Hcap Hnp Htab Hc.
pose proof (s24_rdword_rng W mem _ _ Hcap) as Rcap. pose proof (s24_rdword_rng W mem _ _ Hnp) as Rnp.
pose proof (s24_rdword_rng W mem _ _ Htab) as Rtab. pose proof (s24_rdword_rng W mem _ _ Hc) as Rc.
set (E := s16_E1 regs c tab cap np).
assert (EL : forall n, (n < A_TEXT)%nat ->
  ew E n = ew (Ereg regs [Z_to_bv 64 c; Z_to_bv 64 tab; Z_to_bv 64 cap; Z_to_bv 64 np]) n)
  by (intros n Hn; subst E; unfold s16_E1; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = getr regs 9)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 tab) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 cap) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 np) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 9) = bv_unsigned (getr regs 9)) by (rewrite E9; reflexivity).
split.
- unfold s16_ss1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold s16_E1. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold s16_rs1. constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    * apply (chunk_ok_val SEGS E _ (bv_unsigned (getr regs 9)) 40 8 (SOff 34 0) cap);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia
        | exact (val_mem_of_rdword SEGS _ _ _ _ Hcap)].
    * apply (chunk_ok_val SEGS E _ (bv_unsigned (getr regs 9)) 48 8 (SOff 35 0) np);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia
        | exact (val_mem_of_rdword SEGS _ _ _ _ Hnp)].
    * apply (chunk_ok_val SEGS E _ (bv_unsigned (getr regs 9)) 104 8 (SOff 33 0) tab);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia
        | exact (val_mem_of_rdword SEGS _ _ _ _ Htab)].
    * apply (chunk_ok_val SEGS E _ (bv_unsigned (getr regs 9)) 168 8 (SOff 32 0) c);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia
        | exact (val_mem_of_rdword SEGS _ _ _ _ Hc)].
  + unfold s16_rs1. cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; [exact I | exact I]].
    cbn [s16_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
    split; [|exact I]. split; [lia|]. split; [exact Hal | lia].
- split; [apply Forall_nil|].
  split; [subst E; unfold s16_E1; apply Eimg_env|].
  split; [split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | reflexivity]|].
  intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
(* the run 0x85e50 .. 0x85e70: four `ld` of the s1 slots, four `mv`, and the jal of reac_segconf_declared *)
Lemma s16_run1 : forall cx ly S (W : world SEGS) regs mem md k c tab (Q : world SEGS -> config -> Prop),
  lt_base B MT cx ->
  lt_frame B cx ly S W regs mem md k LFO_N ->
  rdword (rdW W mem) (x_s1 cx + 40) = Some (x_cap cx) ->
  rdword (rdW W mem) (x_s1 cx + 48) = Some (x_fr cx + FO_N) ->
  rdword (rdW W mem) (x_s1 cx + 104) = Some tab ->
  rdword (rdW W mem) (x_s1 cx + 168) = Some c ->
  (forall (regsT : bvmap 5 word) memT mdT,
     getr regsT 2 = getr regs 2 -> getr regsT 3 = getr regs 3 -> getr regsT 4 = getr regs 4 ->
     getr regsT 8 = getr regs 8 -> getr regsT 9 = getr regs 9 -> getr regsT 24 = getr regs 24 ->
     getr regsT 10 = w64 c -> getr regsT 11 = w64 tab -> getr regsT 12 = w64 (x_cap cx) ->
     getr regsT 13 = w64 (x_fr cx + FO_N) -> getr regsT 1 = w64 (BASE + 0x10b4) ->
     getr regsT 18 = w64 c -> getr regsT 19 = w64 (x_cap cx) ->
     getr regsT 20 = w64 (x_fr cx + FO_N) -> getr regsT 21 = w64 tab ->
     (forall a, rdW W memT a = rdW W mem a) ->
     ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx)
       (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W memT mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_reac_segconf_declared)) memT (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85e50) regs mem md) Q.
Proof.
intros cx ly S W regs mem md k c tab Q HBASE HFRAME Hcap Hnp Htab Hc HK.
pose proof (paj_run B LAWS) as RUN.
pose proof HFRAME as (HJ & H2 & H3 & H4 & H8 & H9 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKOK & _).
destruct (s24_s1_arith cx (x_ly cx) HSTKOK) as (E16 & EB & Hc1 & Emod & Hr1 & Hr0 & Htop0).
pose proof HSTKOK as (Hal16 & _ & Hceil2 & Hslo2 & Hshi2 & H47 & _ & _ & _).
pose proof (proj1 alloc_ceiling_value) as HAC.
assert (U9 : bv_unsigned (getr regs 9) = x_s1 cx)
  by (rewrite H9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
destruct (s16_seed1 W regs mem LO_K85e50 c tab (x_cap cx) (x_fr cx + FO_N)
  ltac:(rewrite U9; lia) ltac:(rewrite U9; exact E16)
  ltac:(rewrite U9; exact Hcap) ltac:(rewrite U9; exact Hnp)
  ltac:(rewrite U9; exact Htab) ltac:(rewrite U9; exact Hc)) as (HS & SHOK & HEI & HAE & EEo).
paj_run_tok RUN HS HJ SHOK s24_Bspan;
  try solve [ apply awr_ok_nil
            | unfold s16_ss1, s16_rs1; cbn [ss_mem]; apply awr_ok_cons_ro;
              [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil] ].
(* the model the run leaves is whatever with_vm_backing gives; the continuation takes it as it is *)
assert (Emem : forall x : word, ms_mem ms x = mem x).
{ intros x; apply HF; intros (r & Hr & Hw).
  unfold s16_ss1, s16_rs1 in Hr; cbn [ss_mem In] in Hr; destruct Hr as [<- | []].
  cbn [YP09.r_wlo YP09.r_whi] in Hw; lia. }
assert (Heq : forall a, rdW W (ms_mem ms) a = rdW W mem a).
{ intros a. unfold aview, mbyte, mrestrict. rewrite Emem. reflexivity. }
pmkst HS.
rewrite (SIGP SS_reac_segconf_declared
  ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_declared) with AF_reac_segconf_declared by (vm_compute; reflexivity).
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (24%bv : bv 5) P24.
prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13. prreg HS (18%bv : bv 5) P18.
prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
assert (EL' : forall n, (n < A_TEXT)%nat ->
  ew (s16_E1 regs c tab (x_cap cx) (x_fr cx + FO_N)) n =
  ew (Ereg regs [Z_to_bv 64 c; Z_to_bv 64 tab; Z_to_bv 64 (x_cap cx); Z_to_bv 64 (x_fr cx + FO_N)]) n)
  by (intros n Hn; unfold s16_E1; apply Eimg_low; exact Hn).
assert (A32 : ew (s16_E1 regs c tab (x_cap cx) (x_fr cx + FO_N)) 32 = w64 c)
  by (rewrite EL' by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (A33 : ew (s16_E1 regs c tab (x_cap cx) (x_fr cx + FO_N)) 33 = w64 tab)
  by (rewrite EL' by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (A34 : ew (s16_E1 regs c tab (x_cap cx) (x_fr cx + FO_N)) 34 = w64 (x_cap cx))
  by (rewrite EL' by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (A35 : ew (s16_E1 regs c tab (x_cap cx) (x_fr cx + FO_N)) 35 = w64 (x_fr cx + FO_N))
  by (rewrite EL' by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
apply (HK (ms_regs ms) (ms_mem ms)).
- rewrite P2. exact (EEo 2%nat 2%bv eq_refl).
- rewrite P3. exact (EEo 3%nat 3%bv eq_refl).
- rewrite P4. exact (EEo 4%nat 4%bv eq_refl).
- rewrite P8. exact (EEo 8%nat 8%bv eq_refl).
- rewrite P9. exact (EEo 9%nat 9%bv eq_refl).
- rewrite P24. exact (EEo 24%nat 24%bv eq_refl).
- rewrite P10. exact A32.
- rewrite P11. exact A33.
- rewrite P12. exact A34.
- rewrite P13. exact A35.
- rewrite P1. reflexivity.
- rewrite P18. exact A32.
- rewrite P19. exact A34.
- rewrite P20. exact A35.
- rewrite P21. exact A33.
- exact Heq.
- exact HJ.
Qed.

(* a reader at a machine address only depends on the address mod 2 ^ 64 (the image-A twin's s24_aview_wrap,
   s24_keep_all) *)
Lemma k24_aview_wrap : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zmod_mod. reflexivity.
Qed.
Lemma k24_keep_all : forall H (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' HK a. rewrite (k24_aview_wrap H m' a), (k24_aview_wrap H m a). apply HK.
apply Z.mod_pos_bound. lia.
Qed.

(* ===================== segment S16's second run: 0x85e74 .. 0x85e90, to check_declared ===================== *)
(* the seed of 0x85e74: the count cell n (4 bytes at s4, atom 32 = its value, 0 .. 39) and the s1 slots 112 (want,
   atom 33), 120 (mt, atom 34) and 128 (mn, atom 35), all read only (the image-A twin's s24_ssC, B's slots) *)
Definition s16_rC1 : YP09.region := YP09.mkRegion (Some 20%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition s16_rC2 : YP09.region := YP09.mkRegion (Some 9%nat) 112 136 0 0
  [YP09.mkChunk 112 (CVal 8 (SOff 33 0)); YP09.mkChunk 120 (CVal 8 (SOff 34 0));
   YP09.mkChunk 128 (CVal 8 (SOff 35 0))].
Definition s16_ssC (pc : Z) : sstate :=
  mkSS pc sr_atoms [s16_rC1; s16_rC2] None (mkFacts [(32%nat, mkAF 0 39 0)] [] []).
Lemma s16_runC : forall cx ly S (W : world SEGS) regs mem md k len1 want mt mn (Q : world SEGS -> config -> Prop),
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  getr regs 9 = w64 (x_s1 cx) -> getr regs 20 = w64 (x_fr cx + FO_N) ->
  4096 <= x_fr cx -> x_fr cx + 512 <= x_s1 cx -> x_s1 cx + 136 <= 2 ^ 47 ->
  0 <= len1 <= 39 -> sa_val (rdW W mem) (x_fr cx + FO_N) 4 len1 ->
  rdword (rdW W mem) (x_s1 cx + 112) = Some want -> rdword (rdW W mem) (x_s1 cx + 120) = Some mt ->
  rdword (rdW W mem) (x_s1 cx + 128) = Some mn ->
  (forall (regsT : bvmap 5 word) memT mdT,
     (forall r, In r ([2; 3; 4; 8; 9; 10; 18; 19; 21; 24]%bv : list (bv 5)) -> getr regsT r = getr regs r) ->
     getr regsT 11 = w64 want -> getr regsT 12 = getr regs 21 -> getr regsT 13 = w64 len1 ->
     getr regsT 14 = w64 mt -> getr regsT 15 = w64 mn -> getr regsT 16 = getr regs 19 ->
     getr regsT 20 = w64 mt -> getr regsT 1 = w64 (BASE + 0x10d4) ->
     (forall a, rdW W memT a = rdW W mem a) ->
     ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx)
       (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W memT mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_check_declared)) memT (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x10b4) regs mem md) Q.
Proof.
intros cx ly S W regs mem md k len1 want mt mn Q HJ R9 R20 Hfr4 Hfrs Hs1 Hlen HNV Swant Smt Smn HK.
pose proof (paj_run B LAWS) as RUN.
pose proof (s24_rdword_rng W mem _ _ Swant) as Rw. pose proof (s24_rdword_rng W mem _ _ Smt) as Rm.
pose proof (s24_rdword_rng W mem _ _ Smn) as Rn.
set (EC := Eimg (Ereg regs [w64 len1; w64 want; w64 mt; w64 mn])).
assert (ECr : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew EC n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst EC. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (ECx : forall j, (j < 4)%nat ->
  ew EC (32 + j) = nth j [w64 len1; w64 want; w64 mt; w64 mn] (Z_to_bv 64 0)).
{ intros j Hj. subst EC. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
pose proof (ECx 0%nat ltac:(lia)) as EC32. pose proof (ECx 1%nat ltac:(lia)) as EC33.
pose proof (ECx 2%nat ltac:(lia)) as EC34. pose proof (ECx 3%nat ltac:(lia)) as EC35.
cbn [Nat.add nth] in EC32, EC33, EC34, EC35. clear ECx.
assert (EC9u : bv_unsigned (ew EC 9) = x_s1 cx)
  by (rewrite (ECr 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (EC20u : bv_unsigned (ew EC 20) = x_fr cx + FO_N)
  by (rewrite (ECr 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; unfold FO_N; lia).
assert (HEIC : img_env VAL A_LIM EC) by (subst EC; apply Eimg_env).
assert (HAEC : env_agree 32 (Ereg regs [w64 len1; w64 want; w64 mt; w64 mn]) EC)
  by (subst EC; split; [intros i Hi; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (SHC : sh_ok SEGS s24_Bx [] EC (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HSC : st_ok_pi SEGS VAL EC (s16_ssC 0x10b4)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x10b4)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s16_ssC. apply pa_entry_st_ok_full.
  - subst EC. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold s16_rC1, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite EC20u. split; [unfold FO_N; lia|]. split; [unfold FO_N; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS EC _ (x_fr cx + FO_N) 0 4 (SOff 32 0) len1);
        [cbn [sv_denot]; rewrite EC32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ HNV).
    + unfold s16_rC2, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite EC9u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val SEGS EC _ (x_s1 cx) 112 8 (SOff 33 0) want);
          [cbn [sv_denot]; rewrite EC33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Swant).
      * apply (chunk_ok_val SEGS EC _ (x_s1 cx) 120 8 (SOff 34 0) mt);
          [cbn [sv_denot]; rewrite EC34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Smt).
      * apply (chunk_ok_val SEGS EC _ (x_s1 cx) 128 8 (SOff 35 0) mn);
          [cbn [sv_denot]; rewrite EC35, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Smn).
  - unfold s16_rC1, s16_rC2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite EC20u, EC9u.
    split; [split; [left; unfold FO_N; lia | exact I] | split; exact I].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite EC32. unfold w64. rewrite unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
assert (EC21 : ew EC 21 = getr regs 21) by (apply ECr; reflexivity).
assert (EC19 : ew EC 19 = getr regs 19) by (apply ECr; reflexivity).
clearbody EC. clear ECr.
unfold cfg_at. change (w64 (BASE + 0x10b4)) with (Z_to_bv 64 (BASE + 0x10b4)).
paj_run_tok RUN HSC HJ SHC s24_Bspan.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdC := d) in *; clearbody mdC end.
lazymatch goal with
| HFr : frame_of ?E0 _ (mrestrict _ _) (mrestrict _ ?m1) |- _ =>
  assert (KEEPC0 : forall a, 0 <= a < 2 ^ 64 -> rdW W m1 a = rdW W mem a)
    by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
        [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin'; destruct Hin' as [Heq | [Heq | []]];
          inversion Heq; subst; lia
        | exact Ha | intros Hff; destruct Hff ])
end.
pmkst HSC.
rewrite (SIGP SS_check_declared ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_check_declared) with AF_check_declared by (vm_compute; reflexivity).
prreg HSC (1%bv : bv 5) PC1. prreg HSC (11%bv : bv 5) PC11. prreg HSC (12%bv : bv 5) PC12.
prreg HSC (13%bv : bv 5) PC13. prreg HSC (14%bv : bv 5) PC14. prreg HSC (15%bv : bv 5) PC15.
prreg HSC (16%bv : bv 5) PC16. prreg HSC (20%bv : bv 5) PC20.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ ([2; 3; 4; 8; 9; 10; 18; 19; 21; 24]%bv : list (bv 5)) HSC HAEC
  ltac:(vm_compute; reflexivity)) as HKC.
cbn [ms_regs restrict] in HKC.
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rr _ ?mm _ |} _ => set (regsC := rr) in *; set (memC := mm) in * end.
apply (HK regsC memC mdC).
- exact HKC.
- exact (eq_trans PC11 EC33).
- exact (eq_trans PC12 EC21).
- exact (eq_trans PC13 EC32).
- exact (eq_trans PC14 EC34).
- exact (eq_trans PC15 EC35).
- exact (eq_trans PC16 EC19).
- exact (eq_trans PC20 EC34).
- rewrite PC1. reflexivity.
- intros a. apply (k24_keep_all (w_H W) mem memC KEEPC0).
- exact HJ.
Qed.

(* ===================== segment S16's third run: 0x85e94 `mv a0,s4`, 0x85e98 `jal free`: free(mt) ===================== *)
Lemma s16_free3 : forall cx ly S (W : world SEGS) regs mem md k acc O pa n (Q : world SEGS -> config -> Prop),
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc 4 LFO_N ((pa, n) :: O) ->
  getr regs 20 = w64 pa ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
     lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) 3 LFO_N O ->
     aregs_preserved regs regs2 -> s24_kept cx W mem W2 mem2 ->
     SRr SEGS W2 (cfg_at SEGS (BASE + LO_K85e9c) regs2 mem2 md2) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x10d4) regs mem md) Q.
Proof.
intros cx ly S W regs mem md k acc O pa n Q HBASE HCORE R20 HK.
pose proof (paj_run B LAWS) as RUN.
pose proof HCORE as (HFRAMEc & _).
pose proof HFRAMEc as (HJ & _).
destruct (s24_seed W regs mem 0x10d4) as (HS & SHOK & HEI & HAE & EEo).
paj_run_tok RUN HS HJ SHOK s24_Bspan; try solve [apply awr_ok_nil].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (Emem : forall x : word, ms_mem ms x = mem x) by (intros x; apply HF; intros (r & [] & _)).
assert (Heq : forall a, rdW W (ms_mem ms) a = rdW W mem a).
{ intros a. unfold aview, mbyte, mrestrict. rewrite Emem. reflexivity. }
pose proof (s24_core_rd_eq cx ly S W regs mem (ms_mem ms) md mdv k acc 4 LFO_N ((pa, n) :: O) Heq HJ HCORE)
  as HCORE'.
pmkst HS. rewrite (pal_free B TL).
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
assert (HPRES : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs []); [exact HS | exact HAE | vm_compute; reflexivity]. }
assert (Ea0 : getr (ms_regs ms) 10 = w64 pa).
{ rewrite P10. rewrite (EEo 20%nat (20%bv : bv 5) ltac:(reflexivity)). exact R20. }
assert (Era : getr (ms_regs ms) 1 = w64 (BASE + LO_K85e9c)).
{ rewrite P1. unfold w64, LO_K85e9c. reflexivity. }
apply (s24_free_at cx O ly S W regs (ms_regs ms) (ms_mem ms) mdv k acc 4 LFO_N pa n LO_K85e9c Q
  HBASE HCORE' HPRES Ea0 Era ltac:(unfold LO_K85e9c; lia) ltac:(unfold LO_K85e9c; reflexivity) ltac:(lia)).
intros ly2 S2 W2 regs2 mem2 md2 HCORE2 HPRES2 KEEP2.
apply (HK ly2 S2 W2 regs2 mem2 md2).
- replace (4 - 1) with 3 in HCORE2 by lia. exact HCORE2.
- exact HPRES2.
- intros x Hx. rewrite (KEEP2 x Hx). apply Heq.
Qed.


(* ============================ the S16 kit (image B port of the image-A twin's kit) ============================ *)
(* The image-A twin's kit for segments S16 .. S20 (image A's S16 .. S20 commit 68d839b8d799,
   lib/A/Prog/LLVMFuzzerTestOneInput_s24k.v lines 1-892, everything before its free part), ported to image B with
   every s24_ / s24m_ / s24n_ name renamed k24_ / k24m_ / k24n_. Not ported, because this file has them with the
   same statement: s24_vlans, s24m_nth_firstn, s24m_nth_skipn, s24_hblk (here s24_hblk_of_AR), s24_aview_wrap and
   s24_keep_all (here k24_aview_wrap and k24_keep_all). What image B changes: S1 = (SP0 - 352) rounded down to 32,
   so SP0 - 384 < S1 <= SP0 - 352 (k24_nums, k24_low); lt_frame's shadow-base slot is S1 + 200 and it adds the
   SH(FR) slot S1 + 184 (k24_frame_kept); the image facts across a step are s24_img_kept's (no s10_img); the
   stack-protector cells are s24_ssp's (k24_decl_pre); the call sites are 0x85e70 and 0x85e90. *)
(* ================================== the model facts check_declared asks ================================== *)
(* m_declared's answer: -1 (the table filled up) or the entries added, at most one per segment *)
Lemma k24_mdecl_rng : forall ms tab cap a, 0 <= a ->
  fst (SegModel.m_decl_go ms tab cap a) = -1 \/
  a <= fst (SegModel.m_decl_go ms tab cap a) <= a + Z.of_nat (length ms).
Proof.
  induction ms as [|g r IH]; intros tab cap a Ha; cbn [SegModel.m_decl_go length].
  - right. cbn [fst]. lia.
  - destruct (SegModel.ms_ignore g).
    + destruct (IH tab cap a Ha) as [E | E]; [left; exact E | right; lia].
    + destruct (SegModel.m_split (SegModel.ms_name g)) as [[p v]|].
      * match goal with |- context [existsb ?f tab] => destruct (existsb f tab) end.
        -- destruct (IH tab cap a Ha) as [E | E]; [left; exact E | right; lia].
        -- destruct (cap <=? Z.of_nat (length tab)).
           ++ left. reflexivity.
           ++ destruct (IH (tab ++ [(p, v)]) cap (a + 1) ltac:(lia)) as [E | E]; [left; exact E | right; lia].
      * destruct (IH tab cap a Ha) as [E | E]; [left; exact E | right; lia].
Qed.

Lemma k24_mdecl_bnd : forall mc tab cap, (length (SegModel.mc_seg mc) <= 32)%nat ->
  - 2 ^ 31 <= fst (SegModel.m_declared mc tab cap) < 2 ^ 31.
Proof.
  intros mc tab cap Hl. unfold SegModel.m_declared.
  change (2 ^ 31) with 2147483648.
  destruct (k24_mdecl_rng (SegModel.mc_seg mc) tab cap 0 ltac:(lia)) as [E | E]; lia.
Qed.

(* the bytes of a field of a table entry, and a char[16] field read as a C string *)
Lemma k24m_nth_fld : forall (bs : list byte) off n j d, (j < n)%nat ->
  nth j (seg_spec.fld off n bs) d = nth (off + j) bs d.
Proof.
  intros bs off n j d Hj. unfold seg_spec.fld. rewrite s24m_nth_firstn by exact Hj. apply s24m_nth_skipn.
Qed.
Lemma k24m_nth_zs : forall (g : list byte) j, (j < length g)%nat ->
  nth j (seg_spec.zs g) 0 = bv_unsigned (nth j g ZB0).
Proof.
  unfold seg_spec.zs. induction g as [|b g IH]; intros j Hj; cbn [length] in Hj; [lia|].
  destruct j as [|j]; cbn [nth map]; [reflexivity|]. apply IH. lia.
Qed.
Lemma k24m_bytes_fld : forall rd a (bs : list byte) off n, sa_bytes rd a bs ->
  sa_bytes rd (a + Z.of_nat off) (seg_spec.fld off n bs).
Proof.
  intros rd a bs off n H. unfold sa_bytes in *. intros j Hj.
  assert (Hl : length (seg_spec.fld off n bs) = Nat.min n (length bs - off)).
  { unfold seg_spec.fld. rewrite length_firstn, length_skipn. reflexivity. }
  rewrite Hl in Hj.
  rewrite k24m_nth_fld by lia.
  replace (a + Z.of_nat off + Z.of_nat j) with (a + Z.of_nat (off + j)) by lia.
  apply H. lia.
Qed.
Lemma k24m_strz_cstr : forall rd p (g : list byte) cap s, sa_bytes rd p g -> seg_spec.cstr_enc cap s g ->
  sa_strz rd p s.
Proof.
  intros rd p g cap s Hb (Hlg & Hls & Hn0 & Hf). unfold sa_bytes in Hb.
  unfold sa_strz, sa_zs. split; [|exact Hn0].
  intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  rewrite <- Hf.
  rewrite s24m_nth_firstn by lia.
  rewrite k24m_nth_zs by lia.
  apply Hb. lia.
Qed.
(* each entry's parent of the reader's table (18-byte entries) and of the model's (20-byte entries) is a C string
   with its tail, the tail inside the block *)
Lemma k24_rtab_str : forall (rd : reader) (tab : Z) (t : list (list Z * Z)),
  sa_rtab rd tab t ->
  (forall x, tab <= x < tab + 18 * Z.of_nat (length t) + 5 -> rd x <> None) ->
  forall i, (i < length t)%nat -> sa_str rd (tab + seg_spec.RVLAN_SIZE * Z.of_nat i) (fst (nth i t ([], 0))).
Proof.
  intros rd tab t (bs & Hb & _ & Hent) Hm i Hi.
  destruct (Hent i Hi) as (_ & Hc & _).
  pose proof (k24m_bytes_fld rd tab bs (18 * i) 18 Hb) as Hb1.
  pose proof (k24m_bytes_fld rd _ _ 0 16 Hb1) as Hb2.
  assert (Ep : tab + Z.of_nat (18 * i) + Z.of_nat 0 = tab + seg_spec.RVLAN_SIZE * Z.of_nat i)
    by (unfold seg_spec.RVLAN_SIZE; lia).
  rewrite Ep in Hb2.
  pose proof (k24m_strz_cstr _ _ _ _ _ Hb2 Hc) as Hz.
  unfold sa_str. split; [exact Hz|].
  destruct Hc as (_ & Hls & _).
  unfold sa_tail. intros x Hx. apply Hm.
  assert (HL : 0 <= Z.of_nat (length (fst (nth i t ([], 0)))) < 16) by lia.
  unfold seg_spec.RVLAN_SIZE in Hx.
  revert HL Hx. generalize (Z.of_nat (length (fst (nth i t ([], 0))))) as L. intros L HL Hx.
  pose proof (Z.mod_pos_bound (tab + 18 * Z.of_nat i + L) 8 ltac:(lia)) as HM.
  revert HM Hx. generalize ((tab + 18 * Z.of_nat i + L) mod 8) as M. intros M HM Hx.
  lia.
Qed.
Lemma k24_mtab_str : forall (rd : reader) (mt : Z) (t : list (list Z * Z)),
  sa_mtab rd mt t ->
  (forall x, mt <= x < mt + 20 * Z.of_nat (length t) + 3 -> rd x <> None) ->
  forall i, (i < length t)%nat -> sa_str rd (mt + seg_spec.MVLAN_SIZE * Z.of_nat i) (fst (nth i t ([], 0))).
Proof.
  intros rd mt t (bs & Hb & _ & Hent) Hm i Hi.
  destruct (Hent i Hi) as (_ & Hc & _).
  pose proof (k24m_bytes_fld rd mt bs (20 * i) 20 Hb) as Hb1.
  pose proof (k24m_bytes_fld rd _ _ 0 16 Hb1) as Hb2.
  assert (Ep : mt + Z.of_nat (20 * i) + Z.of_nat 0 = mt + seg_spec.MVLAN_SIZE * Z.of_nat i)
    by (unfold seg_spec.MVLAN_SIZE; lia).
  rewrite Ep in Hb2.
  pose proof (k24m_strz_cstr _ _ _ _ _ Hb2 Hc) as Hz.
  unfold sa_str. split; [exact Hz|].
  destruct Hc as (_ & Hls & _).
  unfold sa_tail. intros x Hx. apply Hm.
  assert (HL : 0 <= Z.of_nat (length (fst (nth i t ([], 0)))) < 16) by lia.
  unfold seg_spec.MVLAN_SIZE in Hx.
  revert HL Hx. generalize (Z.of_nat (length (fst (nth i t ([], 0))))) as L. intros L HL Hx.
  pose proof (Z.mod_pos_bound (mt + 20 * Z.of_nat i + L) 8 ltac:(lia)) as HM.
  revert HM Hx. generalize ((mt + 20 * Z.of_nat i + L) mod 8) as M. intros M HM Hx.
  lia.
Qed.

(* ============================== readers that agree everywhere, and lists ============================== *)
Lemma k24_pzd_nodup : forall l, (forall x, In x l -> 0 < snd x) -> pairwise zdisjoint l -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hp Hd; [constructor|]. destruct Hd as [Hx Hl]. constructor.
- intros Hin. rewrite Forall_forall in Hx. specialize (Hx x Hin). pose proof (Hp x (or_introl eq_refl)).
  unfold zdisjoint in Hx. lia.
- apply IH; [intros y Hy; exact (Hp y (or_intror Hy)) | exact Hl].
Qed.
Lemma k24_sa_bytes_ext : forall (rd rd' : reader) a l, (forall x, rd' x = rd x) -> sa_bytes rd a l -> sa_bytes rd' a l.
Proof. intros rd rd' a l HE H i Hi. rewrite HE. exact (H i Hi). Qed.
Lemma k24_sa_val_ext : forall (rd rd' : reader) a n v, (forall x, rd' x = rd x) -> sa_val rd a n v -> sa_val rd' a n v.
Proof. intros rd rd' a n v HE H k Hk. rewrite HE. exact (H k Hk). Qed.

(* ---------------- a block's size is its req_size ---------------- *)
Lemma k24n_req : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. Qed.

(* the five registers the frame part of a cut reads (sp, gp, tp, s0, s1), kept from one state to a later one *)
Definition k24_fregs (regs regs2 : bvmap 5 word) : Prop :=
  forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9) -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Lemma k24_fregs_of_pres : forall regs regs2, aregs_preserved regs regs2 -> k24_fregs regs regs2.
Proof. intros regs regs2 HP r Hr. apply HP. unfold acallee_saved. lia. Qed.
Lemma k24_fregs_trans : forall r1 r2 r3, k24_fregs r1 r2 -> k24_fregs r2 r3 -> k24_fregs r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma k24_w64_mod : forall z, w64 (z mod 2 ^ 64) = w64 z.
Proof.
intros z. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Zmod_mod.
Qed.
Lemma k24_bytes_range : forall (rd rd' : reader) a (bs : list byte),
  sa_bytes rd a bs -> (forall i, 0 <= i < Z.of_nat (length bs) -> rd' (a + i) = rd (a + i)) -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs H HK i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma k24_mtab_range : forall (rd rd' : reader) mt t,
  sa_mtab rd mt t -> (forall i, 0 <= i < 20 * Z.of_nat (length t) -> rd' (mt + i) = rd (mt + i)) -> sa_mtab rd' mt t.
Proof.
intros rd rd' mt t (bs & Hb & Hl & He) HK. exists bs. split; [|exact (conj Hl He)].
apply (k24_bytes_range rd rd' mt bs Hb). intros i Hi. apply HK. rewrite Hl in Hi. lia.
Qed.
Lemma k24_cm_ext : forall (rd rd' : reader) c m st, (forall x, rd' x = rd x) -> lt_cm rd c m st -> lt_cm rd' c m st.
Proof.
intros rd rd' c m st HE. unfold lt_cm, sa_rconf, sa_mconf, sa_mconfp.
intros [(bs1 & H1 & E1) (bs2 & H2 & E2)].
split; [exists bs1 | exists bs2]; (split; [eapply k24_sa_bytes_ext; eassumption | assumption]).
Qed.
(* the bytes reac_segconf_declared may write: entries of the table and, if it grew, the count cell *)
Lemma k24_vtab_in : forall tab n (t0 t1 : list (list Z * Z)) cap a,
  Z.of_nat (length t1) <= cap -> inFP (vtab_W tab n t0 t1) a ->
  (tab <= a < tab + 18 * (cap + 1)) \/ (n <= a < n + 4).
Proof.
intros tab n t0 t1 cap a Hl (r & Hr & Ha). unfold vtab_W in Hr. apply in_app_or in Hr as [Hr | Hr].
- left. destruct Hr as [<- | []]. cbn [fst snd] in Ha. unfold seg_spec.RVLAN_SIZE in Ha. lia.
- right. destruct (length t0 <? length t1)%nat; [|destruct Hr]. destruct Hr as [<- | []]. cbn [fst snd] in Ha. lia.
Qed.

(* vlans_are's parts the walk uses: the answers agree, the reader's table is not longer than cap *)
Lemma k24_vlans_parts : forall got want cap, SegModel.vlans_are got want cap = true ->
  fst got = fst want /\ Z.of_nat (length (snd got)) <= cap.
Proof.
intros got want cap H. unfold SegModel.vlans_are in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 _].
apply Z.eqb_eq in H1. apply Z.leb_le in H4. split; assumption.
Qed.
Lemma k24_rtab_ext : forall (rd rd' : reader) a t, (forall x, rd' x = rd x) -> sa_rtab rd a t -> sa_rtab rd' a t.
Proof. intros rd rd' a t HE (bs & Hb & He). exists bs. split; [eapply k24_sa_bytes_ext; eassumption | exact He]. Qed.
Lemma k24_mtab_ext : forall (rd rd' : reader) a t, (forall x, rd' x = rd x) -> sa_mtab rd a t -> sa_mtab rd' a t.
Proof. intros rd rd' a t HE (bs & Hb & He). exists bs. split; [eapply k24_sa_bytes_ext; eassumption | exact He]. Qed.
Lemma k24_guard_ext : forall (rd rd' : reader) tab cap, (forall x, rd' x = rd x) -> sa_guardtab rd tab cap ->
  sa_guardtab rd' tab cap.
Proof. intros rd rd' tab cap HE H. unfold sa_guardtab in *. eapply k24_sa_bytes_ext; eassumption. Qed.

Lemma k24_tabs_ext : forall cx (rd rd' : reader) tab mt t, (forall x, rd' x = rd x) ->
  lt_tabs cx rd tab mt t -> lt_tabs cx rd' tab mt t.
Proof.
intros cx rd rd' tab mt t HE. unfold lt_tabs, sa_rtab, sa_mtab, sa_guardtab.
intros (H1 & (bs & Hb & Hr) & Hg & Hv & (bs2 & Hb2 & Hm) & H6).
split; [exact H1|]. split; [exists bs; split; [eapply k24_sa_bytes_ext; eassumption | exact Hr]|].
split; [eapply k24_sa_bytes_ext; eassumption|].
split; [eapply k24_sa_val_ext; eassumption|].
split; [exists bs2; split; [eapply k24_sa_bytes_ext; eassumption | exact Hm] | exact H6].
Qed.

(* the journal from the entry every cut from K84eb8 on holds (lt_frame's first conjunct) *)
Definition k24_J (cx : lcx) ly S (W : world SEGS) mem md (k : Z) : Prop :=
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k.

(* the entry's numbers: sp0 16-aligned, S1 = (sp0 - 352) & ~31 at most 383 below sp0, the stack window above the
   allocator's ceiling, below 2 ^ 47 *)
Lemma k24_nums : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ x_s1 cx mod 16 = 0 /\ x_sp0 cx - 384 < x_s1 cx <= x_sp0 cx - 352 /\
  alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_sp0 cx <= ly_top (x_ly cx) /\ ly_top (x_ly cx) <= 2 ^ 47.
Proof.
intros cx HBS. destruct HBS as (HPRE & _).
destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. rewrite HSTK in Hslo.
unfold x_s1, x_sp0, LT_FRAME.
set (sp := spZ (x_regs cx)) in *.
pose proof (Z.mod_pos_bound (sp - 352) 32 ltac:(lia)) as Hm.
assert (E : sp - 352 - (sp - 352) mod 32 = 32 * ((sp - 352) / 32))
  by (pose proof (Z.div_mod (sp - 352) 32 ltac:(lia)); lia).
rewrite E.
split; [exact Hal16|].
split; [replace (32 * ((sp - 352) / 32)) with (2 * ((sp - 352) / 32) * 16) by ring; apply Z.mod_mul; lia|].
split; [rewrite <- E; lia|]. lia.
Qed.

(* the live blocks of a state are distinct *)
Lemma k24_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
destruct (ablocks B ly S) as [|[p0 n0] bl] eqn:Eb; [constructor|].
assert (Hin0 : In (p0, n0) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin0) as (_ & _ & _ & _ & _ & Hpw & _).
rewrite <- Eb. apply (NoDup_map_inv (fun b : Z * Z => (fst b, req_size (snd b)))).
apply k24_pzd_nodup; [|exact Hpw].
intros [a q] Hx. apply in_map_iff in Hx as ([pb nb] & Hq & Hpb). cbn in Hq. injection Hq as <- <-.
destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR Hpb) as (_ & _ & _ & _ & _ & _ & Hn).
cbn [snd]. pose proof (req_size_pos nb ltac:(lia)). lia.
Qed.

Lemma k24_blk_in : forall cx ly S b O, lt_blocks B cx ly S O -> In b O -> In b (ablocks B ly S).
Proof. intros cx ly S b O HP Hb. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hb. Qed.
(* the first two blocks of a cut's list are two different blocks *)
Lemma k24_blk_two : forall cx ly S (W : world SEGS) mem md x y O,
  AR SEGS B ly S W mem md -> lt_blocks B cx ly S (x :: y :: O) -> x <> y /\ ~ In x (x_bl0 B cx) /\ ~ In y (x_bl0 B cx).
Proof.
intros cx ly S W mem md x y O HAR HP.
assert (HND : List.NoDup (ablocks B ly S)) by exact (k24_nodup ly S W mem md HAR).
pose proof (Permutation_NoDup HP HND) as HND2. cbn [app] in HND2.
apply NoDup_cons_iff in HND2 as [Hx HND3]. apply NoDup_cons_iff in HND3 as [Hy _].
split; [intros E; subst y; apply Hx; left; reflexivity|].
split; [intros Hb; apply Hx; right; apply in_or_app; right; exact Hb|].
intros Hb; apply Hy; apply in_or_app; right; exact Hb.
Qed.

(* the frame chain at a call from sp = S1 with s0 = SP0 (the twin's statement; image B has it as s24_achain, from the
   stack the entry's astack_pres keeps readable, so lt_saved is not used) *)
Lemma k24_chain : forall cx ly S (W : world SEGS) mem md k,
  lt_base B MT cx -> k24_J cx ly S W mem md k -> lt_saved cx (rdW W mem) ->
  exists ch, achain ly (rdW W mem) (x_s1 cx) (x_sp0 cx) ch.
Proof.
intros cx ly S W mem md k HBS HJ _.
exact (s24_achain cx ly S W mem md [(LT_FCLS, x_fpos cx)] k HBS HJ).
Qed.

(* what a step keeps that a cut reads: the stack [S1, SP0) (saved registers, slots), the frame's header words and
   flag word, its 36 shadow bytes, and every image byte the runtime does not own *)
Definition k24_kept (cx : lcx) (W : world SEGS) mem (W2 : world SEGS) mem2 : Prop :=
  (forall a, x_s1 cx <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W mem a) /\
  (forall a, x_fr cx <= a < x_fr cx + 24 \/ x_fr cx + 504 <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W mem a) /\
  (forall i, 0 <= i < 36 -> rdW W2 mem2 (x_sh cx + i) = rdW W mem (x_sh cx + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW W mem a).
Lemma k24_kept_all : forall cx (W W2 : world SEGS) mem mem2,
  (forall a, rdW W2 mem2 a = rdW W mem a) -> k24_kept cx W mem W2 mem2.
Proof. intros cx W W2 mem mem2 H. repeat split; intros; apply H. Qed.
Lemma k24_kept_trans : forall cx (W W1 W2 : world SEGS) mem mem1 mem2,
  k24_kept cx W mem W1 mem1 -> k24_kept cx W1 mem1 W2 mem2 -> k24_kept cx W mem W2 mem2.
Proof.
intros cx W W1 W2 mem mem1 mem2 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4).
split; [intros a Ha; rewrite (B1 a Ha); exact (A1 a Ha)|].
split; [intros a Ha; rewrite (B2 a Ha); exact (A2 a Ha)|].
split; [intros i Hi; rewrite (B3 i Hi); exact (A3 i Hi)|].
intros a H1 H2 H3. rewrite (B4 a H1 H2 H3). exact (A4 a H1 H2 H3).
Qed.

(* the frame part of a cut at a later state of the journal *)
Lemma k24_frame_kept : forall cx ly S (W : world SEGS) regs mem md k o ly2 S2 (W2 : world SEGS) regs2 mem2 md2 k2 o2,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o ->
  k24_J cx ly2 S2 W2 mem2 md2 k2 -> k24_fregs regs regs2 ->
  (forall a, x_s1 cx <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W mem a) ->
  (forall a, x_fr cx <= a < x_fr cx + 24 \/ x_fr cx + 504 <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W mem a) ->
  sa_zs (rdW W2 mem2) (x_sh cx) (lt_fsh o2) ->
  lt_frame B cx ly2 S2 W2 regs2 mem2 md2 k2 o2.
Proof.
intros cx ly S W regs mem md k o ly2 S2 W2 regs2 mem2 md2 k2 o2 HBS HF HJ2 HP KS KF HSH2.
pose proof (k24_nums cx HBS) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct HF as (_ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & HSB & _ & HSP).
assert (P : forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9) -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
  by exact HP.
split; [exact HJ2|].
split; [exact (eq_trans (P 2 ltac:(lia)) R2)|].
split; [exact (eq_trans (P 3 ltac:(lia)) R3)|].
split; [exact (eq_trans (P 4 ltac:(lia)) R4)|].
split; [exact (eq_trans (P 8 ltac:(lia)) R8)|].
split; [exact (eq_trans (P 9 ltac:(lia)) R9)|].
split.
{ intros i r Hi. rewrite <- (HSV i r Hi). apply rdword_ext. intros q Hq.
  assert (Hil : (i < 13)%nat) by (apply (proj1 (nth_error_Some LT_SAVED i)); rewrite Hi; discriminate).
  apply KS. lia. }
split; [rewrite <- HH0; apply rdword_ext; intros q Hq; apply KF; lia|].
split; [rewrite <- HH8; apply rdword_ext; intros q Hq; apply KF; lia|].
split; [rewrite <- HH16; apply rdword_ext; intros q Hq; apply KF; lia|].
split; [rewrite <- HFL; apply rdword_ext; intros q Hq; apply KF; unfold LT_FLAGW; lia|].
split; [rewrite <- HSB; apply rdword_ext; intros q Hq; apply KS; lia|].
split; [exact HSH2|].
rewrite <- HSP; apply rdword_ext; intros q Hq; apply KS; lia.
Qed.
Lemma k24_fsh_kept : forall cx (W W2 : world SEGS) mem mem2 o,
  k24_kept cx W mem W2 mem2 -> sa_zs (rdW W mem) (x_sh cx) (lt_fsh o) -> sa_zs (rdW W2 mem2) (x_sh cx) (lt_fsh o).
Proof.
intros cx W W2 mem mem2 o (_ & _ & KH & _) H i Hi. rewrite lt_fsh_len in Hi.
rewrite (KH (Z.of_nat i)) by lia. exact (H i ltac:(rewrite lt_fsh_len; exact Hi)).
Qed.


(* across a call of no allocator event that changes only the frames (sa_noalloc): the same budget *)
Lemma k24_bud_noalloc : forall cx S k acc rem f, lt_bud MT cx S k acc rem -> lt_bud MT cx (set_fs f S) k acc rem.
Proof.
intros cx S k acc rem f (Hk & Hrem & Hkr & Hle & Hacc & Hxm).
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact (mo_le_set_fs_r MT MTFL _ _ f _ Hle)|]. split; lia.
Qed.

(* ---- the cut after a step: frame, image, blocks and budget ---- *)
Lemma k24_core_step_f : forall cx ly S (W : world SEGS) regs mem md k acc rem o O ly2 S2 (W2 : world SEGS) regs2 mem2 md2
  k2 acc2 rem2 O2,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  k24_J cx ly2 S2 W2 mem2 md2 k2 -> k24_fregs regs regs2 -> k24_kept cx W mem W2 mem2 ->
  Permutation (ablocks B ly2 S2) (O2 ++ x_bl0 B cx) -> lt_bud MT cx S2 k2 acc2 rem2 ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 o O2.
Proof.
intros cx ly S W regs mem md k acc rem o O ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 O2 HBS (HF & HI & _ & _) HJ2 HP HK HP2 HBUD.
pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSH & _).
split; [exact (k24_frame_kept cx ly S W regs mem md k o ly2 S2 W2 regs2 mem2 md2 k2 o HBS HF HJ2 HP
  (proj1 HK) (proj1 (proj2 HK)) (k24_fsh_kept cx W W2 mem mem2 o HK HSH))|].
split; [|split; [exact HP2 | exact HBUD]].
destruct HK as (_ & _ & _ & KI).
exact (s24_img_kept cx ly2 S2 W2 mem2 md2 (rdW W mem) (proj1 HJ2) KI HI).
Qed.
Lemma k24_core_step : forall cx ly S (W : world SEGS) regs mem md k acc rem o O ly2 S2 (W2 : world SEGS) regs2 mem2 md2
  k2 acc2 rem2 O2,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  k24_J cx ly2 S2 W2 mem2 md2 k2 -> aregs_preserved regs regs2 -> k24_kept cx W mem W2 mem2 ->
  Permutation (ablocks B ly2 S2) (O2 ++ x_bl0 B cx) -> lt_bud MT cx S2 k2 acc2 rem2 ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 o O2.
Proof.
intros cx ly S W regs mem md k acc rem o O ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 O2 HBS HC HJ2 HP.
exact (k24_core_step_f cx ly S W regs mem md k acc rem o O ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 O2 HBS HC HJ2
  (k24_fregs_of_pres regs regs2 HP)).
Qed.

(* the frame (3, x_fpos cx) at a state of the journal: live, at x_fr cx *)
Lemma k24_frame_at : forall cx ly S (W : world SEGS) mem md k, k24_J cx ly S W mem md k ->
  In (3, x_fpos cx) (frames S) /\ frame_addr ly 3 (x_fpos cx) = x_fr cx /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512 /\ x_fr cx mod 32 = 0 /\
  (forall a, x_fr cx <= a < x_fr cx + 512 -> apresent (w_H W) mem a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H W) mem (x_sh cx + i)).
Proof.
intros cx ly S W mem md k HJ.
destruct HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _).
assert (Hin : In (3, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly 3 (x_fpos cx) = x_fr cx) by (unfold x_fr, frame_addr, LT_FCLS; rewrite EF; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md 3 (x_fpos cx) HAR Hin) as (H4 & Hc & Ha).
destruct (al_frames _ _ LAWS ly S W mem md 3 (x_fpos cx) HAR Hin) as (H32 & _ & Hp & Hsp).
rewrite EFA in H4, Hc, Ha, H32, Hp, Hsp. change (fs_frame_bytes 3) with 512 in H4, Hc, Ha, Hp, Hsp.
change (512 / 8) with 64 in Hsp.
split; [exact Hin|]. split; [exact EFA|]. split; [exact H4|]. split; [exact Hc|]. split; [exact Ha|].
split; [exact H32|]. split; [intros a Hr; exact (proj1 (Hp a Hr))|].
intros i Hi. exact (proj1 (Hsp i Hi)).
Qed.


(* a live block misses the frame and the frame's shadow *)
Lemma k24_blk_apart : forall cx ly S (W : world SEGS) mem md k pa n,
  k24_J cx ly S W mem md k -> In (pa, n) (ablocks B ly S) ->
  (forall a, x_fr cx <= a < x_fr cx + 512 -> ~ (pa <= a < pa + req_size n)) /\
  (forall i, 0 <= i < 36 -> ~ (pa <= x_sh cx + i < pa + req_size n)).
Proof.
intros cx ly S W mem md k pa n HJ Hb.
pose proof (proj1 HJ) as HAR.
destruct (k24_frame_at cx ly S W mem md k HJ) as (Hin & EFA & H4 & Hc & Happ & _).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md pa n 3 (x_fpos cx) HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes 3) with 512 in Hd.
destruct (al_blocks _ _ LAWS ly S W mem md pa n HAR Hb) as (_ & Hp4 & Hpc & Hpapp & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as Hrq.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (shadow_addr_bounds (x_fr cx) ltac:(lia)) as Hsh.
split; [intros a Ha Hab; lia|].
intros i Hi Hab. unfold x_sh, shadow_addr, SHADOW_OFF in Hab. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
clear Hsh. lia.
Qed.

(* the frame and its shadow sit below the stack window of any call from S1 (all below the allocator's ceiling);
   image B: S1 > SP0 - 384 *)
Lemma k24_low : forall cx ly S (W : world SEGS) mem md k, lt_base B MT cx -> k24_J cx ly S W mem md k ->
  x_fr cx + 512 + ASTACK + 352 <= x_s1 cx /\ x_sh cx + 64 + ASTACK + 352 <= x_s1 cx /\
  alloc_ceiling + 32768 - 384 <= x_s1 cx.
Proof.
intros cx ly S W mem md k HBS HJ.
pose proof (k24_nums cx HBS) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct (k24_frame_at cx ly S W mem md k HJ) as (_ & _ & H4 & Hc & _).
pose proof asan_consts as (C1 & _).
unfold x_sh, shadow_addr, SHADOW_OFF, ASTACK. lia.
Qed.

(* check_declared's sa_kept (every byte outside its window [S1 - STK1, S1)) gives what a cut keeps *)
Lemma k24_kept_of_sa_kept : forall cx ly S (W : world SEGS) mem md k (W2 : world SEGS) mem2 (regs : bvmap 5 word) STK1,
  lt_base B MT cx -> k24_J cx ly S W mem md k -> spZ regs = x_s1 cx -> 0 <= STK1 <= ASTACK ->
  sa_kept SEGS W mem W2 mem2 regs STK1 (fun _ => False) -> k24_kept cx W mem W2 mem2.
Proof.
intros cx ly S W mem md k W2 mem2 regs STK1 HBS HJ Hsp HS1 HK.
pose proof (k24_nums cx HBS) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct (k24_low cx ly S W mem md k HBS HJ) as (L1 & L2 & L3).
destruct (k24_frame_at cx ly S W mem md k HJ) as (_ & _ & H4 & Hc & _).
pose proof (pa_img_range (L := seg_listing) (PAImg := PI)) as HIR.
assert (Hsh0 : 0 <= x_sh cx) by (unfold x_sh, shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia)); lia).
pose proof asan_consts as (C1 & _).
unfold ASTACK in *.
split; [intros a Ha; apply HK; [lia | rewrite Hsp; lia | intros []]|].
split; [intros a Ha; apply HK; [lia | rewrite Hsp; lia | intros []]|].
split; [intros i Hi; apply HK; [lia | rewrite Hsp; lia | intros []]|].
intros a Hi _ _. pose proof (HIR a Hi) as Ha. unfold kImgEnd in Ha. apply HK; [lia | rewrite Hsp; lia | intros []].
Qed.

(* a call's inner journal from S1 whose footprint is in live blocks and the count cell n = FR + 256 gives what a
   cut keeps (the image bytes by the journal's image clause: a block or the frame holds no image byte) *)
Lemma k24_kept_of_journal : forall cx ly S (W : world SEGS) mem md k STK1 FP1 ly2 S2 (W2 : world SEGS) mem2 md2 k1,
  lt_base B MT cx -> k24_J cx ly S W mem md k ->
  ajournal SEGS B STK1 (x_s1 cx) FP1 ly S W mem md [] ly2 S2 W2 mem2 md2 k1 -> 0 <= STK1 <= ASTACK ->
  (forall a, inFP FP1 a -> (exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
     (x_fr cx + FO_N <= a < x_fr cx + FO_N + 4)) ->
  k24_kept cx W mem W2 mem2.
Proof.
intros cx ly S W mem md k STK1 FP1 ly2 S2 W2 mem2 md2 k1 HBS HJ HJ1 HS1 HFP.
pose proof (k24_nums cx HBS) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct (k24_low cx ly S W mem md k HBS HJ) as (L1 & L2 & L3).
pose proof (proj1 HJ) as HAR.
destruct (k24_frame_at cx ly S W mem md k HJ) as (Hin & EFA & H4 & Hc & Happ & H32 & _).
destruct HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* where a footprint byte can be: below the ceiling, apart from the frame's header / flag words and its shadow *)
assert (HLOW : forall a, inFP FP1 a -> 4096 <= a < alloc_ceiling).
{ intros a Ha. destruct (HFP a Ha) as [(b & n & Hb & Hr) | Hr].
  - destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hb) as (_ & Hb4 & Hbc & _). lia.
  - unfold FO_N in Hr. lia. }
assert (HNF : forall a, x_fr cx <= a < x_fr cx + 24 \/ x_fr cx + 504 <= a < x_fr cx + 512 -> ~ inFP FP1 a).
{ intros a Ha Hf. destruct (HFP a Hf) as [(b & n & Hb & Hr) | Hr].
  - destruct (k24_blk_apart cx ly S W mem md k b n HJ Hb) as (HA & _). exact (HA a ltac:(lia) Hr).
  - unfold FO_N in Hr. lia. }
assert (HNS : forall i, 0 <= i < 36 -> ~ inFP FP1 (x_sh cx + i)).
{ intros i Hi Hf. destruct (HFP _ Hf) as [(b & n & Hb & Hr) | Hr].
  - destruct (k24_blk_apart cx ly S W mem md k b n HJ Hb) as (_ & HA). exact (HA i Hi Hr).
  - unfold x_sh, shadow_addr, SHADOW_OFF, FO_N in Hr. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia. }
split.
{ intros a Ha. apply F1; [lia | lia | intros Hf; pose proof (HLOW a Hf); lia]. }
split.
{ intros a Ha. apply (F4 3 (x_fpos cx) a Hin); [left | exact (HNF a Ha)].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia. }
split.
{ intros i Hi. apply (F4 3 (x_fpos cx) _ Hin); [right | exact (HNS i Hi)].
  unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3 / 8) with 64. unfold x_sh. lia. }
intros a Hi Ho He. apply F3; [exact Hi | exact Ho | exact He |].
apply fp_spares_closed.
- intros (r & Hr & Hr0). assert (Hf : inFP FP1 0) by (exists r; split; [exact Hr | exact Hr0]).
  pose proof (HLOW 0 Hf). lia.
- intros Hf. destruct (HFP a Hf) as [(b & n & Hb & Hr) | Hr].
  + exact (blk_img SEGS B LAWS ly S W mem md b n a HAR Hb Hr Hi).
  + apply (frm_img SEGS B LAWS ly S W mem md 3 (x_fpos cx) a HAR Hin); [|exact Hi]. rewrite EFA.
    change (fs_frame_bytes 3) with 512. unfold FO_N in Hr. lia.
Qed.

(* a block the call's footprint misses keeps its bytes (the journal's block clause) *)
Lemma k24_blk_kept : forall cx ly S (W : world SEGS) mem md k STK1 FP1 ly2 S2 (W2 : world SEGS) mem2 md2 k1 p n,
  k24_J cx ly S W mem md k ->
  ajournal SEGS B STK1 (x_s1 cx) FP1 ly S W mem md [] ly2 S2 W2 mem2 md2 k1 ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly2 S2) ->
  (forall a, inFP FP1 a -> (exists b m, In (b, m) (ablocks B ly S) /\ (b, m) <> (p, n) /\ b <= a < b + req_size m) \/
     (x_fr cx + FO_N <= a < x_fr cx + FO_N + 4)) ->
  forall i, 0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W mem (p + i).
Proof.
intros cx ly S W mem md k STK1 FP1 ly2 S2 W2 mem2 md2 k1 p n HJ HJ1 Hp Hp2 HFP i Hi.
pose proof (proj1 HJ) as HAR.
destruct HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hp Hp2 Hi). intros Hf. destruct (HFP _ Hf) as [(b & m & Hb & Hne & Hr) | Hr].
- pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR Hb Hp Hne) as Hd. unfold zdisjoint in Hd.
  cbn [fst snd] in Hd. lia.
- destruct (k24_blk_apart cx ly S W mem md k p n HJ Hp) as (HA & _). exact (HA (p + i) ltac:(unfold FO_N in Hr; lia) ltac:(lia)).
Qed.

(* a live block of a positive size, from AR: nonzero, 16-aligned, every sub-range sa_addr, every byte mapped *)
Lemma k24n_blk : forall ly S (W : world SEGS) mem md p n,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n ->
  p <> 0 /\ p mod 16 = 0 /\
  (forall a k, p <= a -> a + k <= p + n -> sa_addr (rdW W mem) a k) /\
  (forall a, p <= a < p + n -> rdW W mem a <> None).
Proof.
  intros ly S W mem md p n HAR Hin Hn.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hm16 & H4096 & Hceil & _ & Hpres & _).
  pose proof (k24n_req n Hn) as Er. rewrite Er in Hceil, Hpres.
  pose proof asan_consts as (C1 & _).
  split; [lia|]. split; [exact Hm16|]. split.
  - intros a k Ha Hk. unfold sa_addr. split; [lia|].
    split; [change (2 ^ 63) with 9223372036854775808; lia|].
    split; [apply (amem_range_of_block _ _ LAWS ly S W mem md p n a k HAR Hin Ha); rewrite Er; exact Hk|].
    split; [apply (range_addressable_of_block _ _ LAWS ly S W mem md p n a k HAR Hin Ha); rewrite Er; exact Hk|].
    intros Hk0. apply (shadow_hull_vis_of_block _ _ LAWS ly S W mem md p n a k HAR Hin Ha); [rewrite Er; exact Hk | exact Hk0].
  - intros a Ha. apply (aview_some_of_apresent SEGS). exact (proj1 (Hpres a Ha)).
Qed.

(* reac_segconf_declared's pre at the call 0x85e70, and its room and events *)
Lemma k24_decl_pre : forall cx ly S (W : world SEGS) (regs : bvmap 5 word) mem md k acc (c m tab mt : Z),
  lt_base B MT cx ->
  lt_core B MT cx ly S W regs mem md k acc 4 LFO_N
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  lt_tabs cx (rdW W mem) tab mt (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))) ->
  declared_pre SEGS B ly S W mem regs c tab (x_cap cx) (x_fr cx + FO_N) (seg_spec.seg_rc (x_run cx)) (x_tab0 cx)
    gotwA guardA /\ sa_room S /\ st_nev S + EV_reac_segconf_declared <= EV_MAX.
Proof.
  intros cx ly S W regs mem md k acc c m tab mt HBS HC Hcm HT.
  destruct HBS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _ & Hnev0 & _).
  destruct HC as (HF & HI & HBl & HBud).
  destruct HF as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh & _).
  destruct HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _).
  destruct HBud as (_ & _ & Hkr & _).
  destruct Hcm as (Hrc & _).
  destruct HT as (Hcap & Hrt & _ & Hval & _).
  unfold lt_blocks in HBl.
  pose proof asan_consts as (C1 & _).
  (* the class-3 frame and the count cell n = frame + 256 *)
  assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; apply in_or_app; left; left; reflexivity).
  assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
  { unfold x_fr, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & HlyF & _). rewrite HlyF. reflexivity. }
  assert (E512 : fs_frame_bytes LT_FCLS = 512) by reflexivity.
  destruct (al_frames _ _ LAWS ly S W mem md _ _ HAR HinF) as (Hm32 & _ & _ & Hshp).
  destruct (frames_bounds _ _ LAWS ly S W mem md _ _ HAR HinF) as (Hf1 & Hf2 & Hf3).
  rewrite EF in Hm32, Hshp, Hf1, Hf2, Hf3. rewrite E512 in Hshp, Hf2, Hf3.
  unfold x_sh in Hsh.
  assert (H32 : rdW W mem (shadow_addr (x_fr cx) + 32) = Some 4)
    by exact (Hsh 32%nat ltac:(rewrite lt_fsh_len; lia)).
  assert (Hra : range_addressable (rdW W mem) SHADOW_OFF (x_fr cx + FO_N) 4).
  { intros x Hx. unfold FO_N in Hx. exists 4. split.
    - replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr (x_fr cx) + 32); [exact H32|].
      unfold shadow_of_addr, shadow_addr. lia.
    - right. split; lia. }
  assert (Hhv : shadow_hull_vis (rdW W mem) (x_fr cx + FO_N) 4).
  { intros s Hs. unfold FO_N, shadow_addr, SHADOW_OFF in Hs.
    assert (Hi : 0 <= s - shadow_addr (x_fr cx) < 512 / 8) by (unfold shadow_addr, SHADOW_OFF; lia).
    destruct (Hshp _ Hi) as [Hp _].
    replace s with (shadow_addr (x_fr cx) + (s - shadow_addr (x_fr cx))) by lia.
    apply (aview_some_of_apresent SEGS). exact Hp. }
  assert (Hff : sa_fframe ly S (x_fr cx + FO_N) 4).
  { exists LT_FCLS, (x_fpos cx). split; [exact HinF|]. split; [unfold LT_FCLS; lia|].
    rewrite EF, E512. unfold FO_N. lia. }
  assert (Ham : amem_range (x_fr cx + FO_N) 4).
  { unfold amem_range, in_app, FO_N, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia. }
  assert (Han : sa_addr (rdW W mem) (x_fr cx + FO_N) 4).
  { split; [unfold FO_N; lia|]. split; [unfold FO_N; change (2 ^ 63) with 9223372036854775808; lia|].
    split; [exact Ham|]. split; [exact Hra|]. intros _; exact Hhv. }
  (* the blocks c and tab *)
  assert (Hinc : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HBl)). apply in_or_app. left. right. right. right. left. reflexivity. }
  assert (Hint : In (tab, x_tabn cx) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HBl)). apply in_or_app. left. right. left. reflexivity. }
  assert (Htn : 0 < x_tabn cx) by (unfold x_tabn, seg_spec.RVLAN_SIZE; lia).
  destruct (k24n_blk ly S W mem md c seg_spec.SEG_C_SIZE HAR Hinc ltac:(unfold seg_spec.SEG_C_SIZE; lia))
    as (Hc0 & Hc16 & Hcaddr & _).
  destruct (k24n_blk ly S W mem md tab (x_tabn cx) HAR Hint Htn) as (Ht0 & Ht16 & Htaddr & _).
  pose proof (Htaddr tab (seg_spec.RVLAN_SIZE * x_cap cx + 8) ltac:(lia)
    ltac:(unfold x_tabn, seg_spec.RVLAN_SIZE; lia)) as (_ & _ & Ham8 & _).
  pose proof (sep_block_frame _ _ LAWS ly S W mem md _ _ _ _ HAR Hinc HinF) as Dcf.
  pose proof (sep_block_frame _ _ LAWS ly S W mem md _ _ _ _ HAR Hint HinF) as Dtf.
  assert (Hne : (c, seg_spec.SEG_C_SIZE) <> (tab, x_tabn cx)).
  { intros E. injection E. intros E1 E2. unfold x_tabn, seg_spec.RVLAN_SIZE, seg_spec.SEG_C_SIZE in *. lia. }
  pose proof (sep_blocks _ _ LAWS ly S W mem md _ _ _ _ HAR Hinc Hint Hne) as Dct.
  unfold zdisjoint in Dcf, Dtf, Dct. cbn [fst snd] in Dcf, Dtf, Dct.
  rewrite EF, E512 in Dcf, Dtf.
  rewrite (k24n_req seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)) in Dcf, Dct.
  rewrite (k24n_req (x_tabn cx) Htn) in Dtf, Dct.
  split; [|split].
  - unfold declared_pre.
    split; [exact Hc0|]. split; [exact Hc16|]. split; [exact Hrc|].
    split; [exists c, seg_spec.SEG_C_SIZE; split; [exact Hinc | lia]|].
    split; [apply Hcaddr; lia|].
    split.
    + unfold vtab_pre.
      split; [exact Ht0|]. split; [exact Ht16|]. split; [exact Hrt|].
      split; [change (2 ^ 31) with 2147483648; lia|].
      split; [exists tab, (x_tabn cx); split; [exact Hint | unfold x_tabn, seg_spec.RVLAN_SIZE; lia]|].
      split; [apply Htaddr; unfold x_tabn, seg_spec.RVLAN_SIZE; lia|].
      split; [exact Ham8|].
      split; [unfold FO_N; lia|].
      split; [unfold FO_N; lia|].
      split; [exact Hval|].
      split; [left; split; [exact Hff | exact Hra]|].
      split; [exact Han|].
      unfold sa_disj, FO_N, x_tabn, seg_spec.RVLAN_SIZE in *. lia.
    + split; [unfold sa_disj, x_tabn, seg_spec.RVLAN_SIZE in *; lia|].
      split; [unfold sa_disj, FO_N in *; lia|].
      exact (s24_ssp ly S W mem md HAR).
  - unfold sa_room. rewrite Hfrs, Hfr0. cbn [length app]. lia.
  - unfold EV_reac_segconf_declared. lia.
Qed.

(* check_declared's pre at the call 0x85e90, after reac_segconf_declared returned *)
Lemma k24_chk_pre : forall cx ly2 S2 (W2 : world SEGS) mem2 md2 (tab mt got want : Z),
  lt_base B MT cx -> AR SEGS B ly2 S2 W2 mem2 md2 ->
  In (tab, x_tabn cx) (ablocks B ly2 S2) -> In (mt, x_mtn cx) (ablocks B ly2 S2) ->
  (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat ->
  got = fst (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx)) mod 2 ^ 64 ->
  want = fst (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)) mod 2 ^ 64 ->
  Z.of_nat (length (x_tab0 cx)) <= x_cap cx < 40 ->
  sa_rtab (rdW W2 mem2) tab (snd (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx))) ->
  sa_guardtab (rdW W2 mem2) tab (x_cap cx) ->
  sa_mtab (rdW W2 mem2) mt (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))) ->
  Z.of_nat (length (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)))) <= x_cap cx ->
  check_declared_pre B ly2 S2 (rdW W2 mem2) got want tab
    (Z.of_nat (length (snd (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx))))) mt
    (Z.of_nat (length (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))))) (x_cap cx)
    (fst (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx)))
    (fst (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)))
    (snd (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx)))
    (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))).
Proof.
  intros cx ly2 S2 W2 mem2 md2 tab mt got want _ HAR Hint Hinm Hlen Hgot Hwant Hcap Hrt Hg Hmt Hml.
  assert (HV : SegModel.vlans_are (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx))
                 (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)) (x_cap cx) = true)
    by (unfold x_mcF, x_run, x_tab0, x_cap; exact (s24_vlans (x_pl cx))).
  pose proof (k24_mdecl_bnd (x_mcF cx) (x_tab0 cx) (x_cap cx) Hlen) as Hbnd.
  revert HV Hbnd Hgot Hwant Hrt Hg Hmt Hml.
  generalize (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx)) as R.
  generalize (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)) as M.
  intros M R HV Hbnd Hgot Hwant Hrt Hg Hmt Hml.
  pose proof HV as HV'. unfold SegModel.vlans_are in HV'.
  apply andb_prop in HV' as [HV' Hle]. apply andb_prop in HV' as [HV' _]. apply andb_prop in HV' as [Hfst _].
  apply Z.eqb_eq in Hfst. apply Z.leb_le in Hle.
  destruct (k24n_blk ly2 S2 W2 mem2 md2 tab (x_tabn cx) HAR Hint ltac:(unfold x_tabn, seg_spec.RVLAN_SIZE; lia))
    as (Ht0 & Ht16 & Htaddr & Htvis).
  destruct (k24n_blk ly2 S2 W2 mem2 md2 mt (x_mtn cx) HAR Hinm ltac:(unfold x_mtn, seg_spec.MVLAN_SIZE; lia))
    as (Hm0 & Hm16 & Hmaddr & Hmvis).
  unfold check_declared_pre.
  unfold x_tabn, x_mtn, seg_spec.RVLAN_SIZE, seg_spec.MVLAN_SIZE in *.
  split; [exact Hgot|]. split; [exact Hwant|].
  split; [rewrite Hfst; exact Hbnd|]. split; [exact Hbnd|].
  split; [lia|].
  split; [exact Ht0|]. split; [exact Ht16|]. split; [exact Hrt|]. split; [exact Hg|].
  split; [do 2 eexists; split; [exact Hint | lia]|].
  split; [apply Htaddr; lia|].
  split.
  { intros i Hi. refine (k24_rtab_str _ _ _ Hrt _ i Hi). intros x Hx. apply Htvis. lia. }
  split; [reflexivity|].
  split; [exact Hm0|]. split; [exact Hm16|]. split; [exact Hmt|].
  split; [do 2 eexists; split; [exact Hinm | lia]|].
  split; [apply Hmaddr; lia|].
  split.
  { intros i Hi. refine (k24_mtab_str _ _ _ Hmt _ i Hi). intros x Hx. apply Hmvis. lia. }
  split; [exact Hml|]. split; [reflexivity|].
  rewrite <- !surjective_pairing. exact HV.
Qed.

(* ============================== S16 0x85e50 .. 0x85e98 ============================== *)
(* the image-A twin's lt_seg_S16 (image A's S16 .. S20 commit 68d839b8d799, lib/A/Prog/LLVMFuzzerTestOneInput_s24.v),
   over image B's runs s16_run1 / s16_runC / s16_free3 and the twin's kit as k24_* *)
Theorem lt_seg_S16 : lt_seg_S16_stmt B MT.
Proof.
unfold lt_seg_S16_stmt. intros K9c.
unfold LT_K85e50_stmt.
intros cx ly S W regs mem md k acc c m tab mt HBASE HFRM HCORE Hhc Hhm Hht Hhmt R24 HSL HCM HTABS.
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & _).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKOK & _).
destruct (s24_s1_arith cx (x_ly cx) HSTKOK) as (E16 & EB & Hc1 & Emod & Hr1 & Hr0 & Htop0).
pose proof HSTKOK as (Hal16 & _ & Hceil2 & Hslo2 & Hshi2 & H47 & _ & _ & _).
unfold STK_LLVMFuzzerTestOneInput in Hslo2.
pose proof HBASE as (HPRE0 & _).
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof (proj1 alloc_ceiling_value) as HAC.
pose proof pa_base_lo as HBLO. pose proof (pa_B_ok (L := seg_listing)) as (HB0 & HB1 & HB4).
destruct (k24_frame_at cx ly S W mem md k HJ) as (Hin3 & EFA & HF4 & HFc & HFapp & HF32 & HFp & HFsp).
destruct (k24_blk_two cx ly S W mem md _ _ _ HAR HBL) as (Hmt_tab & Hmt0 & Htab0).
pose proof Hhmt as (HinMT & HmtF & HmtA & _). pose proof Hht as (HinT & HtF & HtA & _).
pose proof Hhc as (HinC & HcF & HcA & _).
pose proof (al_blocks _ _ LAWS ly S W mem md tab _ HAR HinT) as (_ & _ & HtC & _).
pose proof (al_blocks _ _ LAWS ly S W mem md mt _ HAR HinMT) as (_ & _ & HmtC & _).
pose proof (al_blocks _ _ LAWS ly S W mem md c _ HAR HinC) as (_ & _ & HcC & _).
pose proof HTABS as (Hcap & _ & _ & _ & _ & HmnLe).
assert (Hreqt : req_size (x_tabn cx) = x_tabn cx) by (apply k24n_req; unfold x_tabn, seg_spec.RVLAN_SIZE; lia).
assert (Hreqm : req_size (x_mtn cx) = x_mtn cx) by (apply k24n_req; unfold x_mtn, seg_spec.MVLAN_SIZE; lia).
rewrite Hreqt in HtC. rewrite Hreqm in HmtC.
assert (Hc64 : 0 <= c < 2 ^ 64)
  by (pose proof (req_size_pos seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)); lia).
(* the model: the reader's answer and table (gd) against the model's (wd) *)
set (gd := SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx)) in *.
set (wd := SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)) in *.
destruct (k24_vlans_parts gd wd (x_cap cx) (s24_vlans (x_pl cx))) as (Hgw & Hlt1).
assert (Hmc32 : (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat).
{ destruct HCM as [_ Hm]. unfold sa_mconf, sa_mconfp in Hm. destruct Hm as (bs & _ & Henc).
  unfold seg_spec.mconf_encp in Henc. destruct Henc as (_ & Hle & _). exact Hle. }
(* the slots the runs read *)
assert (S40 : rdword (rdW W mem) (x_s1 cx + 40) = Some (x_cap cx))
  by (apply HSL; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S48 : rdword (rdW W mem) (x_s1 cx + 48) = Some (x_fr cx + FO_N))
  by (apply HSL; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S104 : rdword (rdW W mem) (x_s1 cx + 104) = Some tab)
  by (apply HSL; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S112 : rdword (rdW W mem) (x_s1 cx + 112) = Some (fst wd mod 2 ^ 64))
  by (apply HSL; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S120 : rdword (rdW W mem) (x_s1 cx + 120) = Some mt)
  by (apply HSL; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S128 : rdword (rdW W mem) (x_s1 cx + 128) = Some (Z.of_nat (length (snd wd))))
  by (apply HSL; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S168 : rdword (rdW W mem) (x_s1 cx + 168) = Some c)
  by (apply HSL; cbn [In]; repeat (first [left; reflexivity | right])).
pose proof (Z.mod_pos_bound (fst wd) (2 ^ 64) ltac:(lia)) as Hwm.
(* ---- 0x85e50 .. 0x85e70, the jal of reac_segconf_declared ---- *)
apply (s16_run1 cx ly S W regs mem md k c tab _ HBASE HFR S40 S48 S104 S168).
intros regsA memA mdA QA2 QA3 QA4 QA8 QA9 QA24 PA10 PA11 PA12 PA13 PA1 PA18 PA19 PA20 PA21 KEEPA HJA.
assert (HFRA : k24_fregs regs regsA).
{ intros r Hr. destruct Hr as [-> | [-> | [-> | [-> | ->]]]]; [exact QA2 | exact QA3 | exact QA4 | exact QA8 | exact QA9]. }
(* the cut's facts at the run's end (it wrote nothing) *)
pose proof (k24_core_step_f cx ly S W regs mem md k acc 4 LFO_N _ ly S W regsA memA mdA k acc 4 _
  HBASE HCORE HJA HFRA (k24_kept_all cx W W mem memA KEEPA) HBL HBUD) as HCOREA.
pose proof (k24_cm_ext _ _ c m (x_run cx) KEEPA HCM) as HCMA.
pose proof (k24_tabs_ext cx _ _ tab mt _ KEEPA HTABS) as HTABSA.
pose proof HCOREA as ((_ & _ & _ & _ & _ & _ & HSVA & _) & (HRODA & _) & _).
destruct (k24_decl_pre cx ly S W regsA memA mdA k acc c m tab mt HBASE HCOREA HCMA HTABSA)
  as (HDP & HROOM & HEVD).
destruct (k24_chain cx ly S W memA mdA k HBASE HJA HSVA) as (ch1 & HCH1).
(* the registers at the call *)
assert (Hspc : spZ regsA = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite QA2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hs0A : s0Z regsA = x_sp0 cx).
{ unfold s0Z. rewrite QA8, R8. unfold w64. apply unsigned_lit_small. lia. }
assert (HgpA : getr regsA 3 = w64 (as_gp B)) by (rewrite QA3, R3; exact Hgp0).
assert (HtpA : getr regsA 4 = w64 (as_tp B)) by (rewrite QA4, R4; exact Htp0).
assert (HraA : YK0s.ret_ok (getr regsA 1)) by (rewrite PA1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4A : 4096 <= bv_unsigned (getr regsA 1)) by (rewrite PA1; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (HCH1' : achain ly (rdW W memA) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regsA) ch1)
  by (rewrite Hs0A; replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia; exact HCH1).
assert (HSTKD : STK_reac_segconf_declared = 12592) by reflexivity.
assert (Ht64 : 0 <= tab < 2 ^ 64) by (unfold x_tabn, seg_spec.RVLAN_SIZE in HtC; lia).
(* the call of reac_segconf_declared (cl_callS_wide: its footprint holds the count cell n in this function's frame) *)
pose proof (fun HPRE1 => HDECLARED fx ly S W regsA memA mdA ch1 c tab (x_cap cx) (x_fr cx + FO_N)
  (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) HPRE1 HRODA PA10 Hc64 PA11 Ht64 PA12 ltac:(lia) PA13
  ltac:(unfold FO_N; lia) HDP HROOM HEVD) as HCALL.
lazymatch type of HCALL with _ -> SRr _ _ _ (apost_base _ _ _ _ _ _ _ _ _ _ _ ?Kq) => set (KQ := Kq) in HCALL end.
set (FP1 := declared_W tab (x_fr cx + FO_N) (x_tab0 cx) (snd gd)) in *.
assert (HFP1 : forall a, inFP FP1 a -> (tab <= a < tab + x_tabn cx) \/ (x_fr cx + FO_N <= a < x_fr cx + FO_N + 4)).
{ intros a Ha. destruct (k24_vtab_in tab (x_fr cx + FO_N) (x_tab0 cx) (snd gd) (x_cap cx) a Hlt1 Ha) as [H | H];
    [left; unfold x_tabn, seg_spec.RVLAN_SIZE; lia | right; exact H]. }
eapply SRr_bind.
{ apply (cl_callS_wide B LAWS W regsA memA (Z_to_bv 64 (BASE + AF_reac_segconf_declared)) STK_LLVMFuzzerTestOneInput
    (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S mdA k
    STK_reac_segconf_declared FP1 EV_reac_segconf_declared (x_s1 cx - x_sp0 cx) (getr regsA 1) ch1 KQ HJA Hspc
    Emod ltac:(lia) ltac:(rewrite HSTKD; lia)
    ltac:(rewrite HSTKD; unfold STK_LLVMFuzzerTestOneInput; lia) HgpA HtpA eq_refl HraA Hra4A HCH1').
  - intros HPRE1. eapply SRr_mono; [exact (HCALL HPRE1)|].
    unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Ec & HJ3 & HP3 & HQ3).
    exists ly3, S3, regs3, mem3, md3. split; [exact Ec|]. split; [exact HJ3|]. split; [exact HP3 | exact HQ3].
  - intros a Ha. destruct (HFP1 a Ha) as [H | H].
    + right; right; left. exists tab, (x_tabn cx). split; [exact HinT|]. split; [exact Htab0|]. rewrite Hreqt. exact H.
    + right; right; right; left. exists 3, (x_fpos cx). split; [left; reflexivity|]. left.
      unfold in_zr; cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. unfold FO_N in H. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. destruct (HFP1 a Ha) as [H | H];
      unfold STK_LLVMFuzzerTestOneInput, FO_N in *; lia. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3).
unfold KQ in HK3. destruct HK3 as (R10d & HRT3 & HNV3 & HGD3 & (HPerm3 & -> & (f3 & ES3))).
rewrite PA1.
change EV_reac_segconf_declared with 0 in HJ3, HJc3. rewrite Z.add_0_r in HJ3.
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HJc3 by lia.
assert (HSTKD' : 0 <= STK_reac_segconf_declared <= ASTACK) by (rewrite HSTKD; unfold ASTACK; lia).
(* what reac_segconf_declared kept: the cut's parts and the table mt *)
assert (HFP1b : forall a, inFP FP1 a -> (exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
  (x_fr cx + FO_N <= a < x_fr cx + FO_N + 4)).
{ intros a Ha. destruct (HFP1 a Ha) as [H | H];
    [left; exists tab, (x_tabn cx); rewrite Hreqt; split; [exact HinT | exact H] | right; exact H]. }
pose proof (k24_kept_of_journal cx ly S W memA mdA k _ FP1 ly S3 W3 mem3 md3 0 HBASE HJA HJc3 HSTKD' HFP1b) as K3.
pose proof (k24_kept_trans cx W W W3 mem memA mem3 (k24_kept_all cx W W mem memA KEEPA) K3) as K03.
assert (HinMT3 : In (mt, x_mtn cx) (ablocks B ly S3)) by (apply (Permutation_in _ (Permutation_sym HPerm3)); exact HinMT).
assert (HinT3 : In (tab, x_tabn cx) (ablocks B ly S3)) by (apply (Permutation_in _ (Permutation_sym HPerm3)); exact HinT).
pose proof HTABSA as (_ & _ & HGDA & _ & HMTA & _).
assert (HMT3 : sa_mtab (rdW W3 mem3) mt (snd wd)).
{ apply (k24_mtab_range (rdW W memA) _ mt _ HMTA). intros i Hi.
  apply (k24_blk_kept cx ly S W memA mdA k _ FP1 ly S3 W3 mem3 md3 0 mt (x_mtn cx) HJA HJc3 HinMT HinMT3).
  - intros a Ha. destruct (HFP1 a Ha) as [H | H]; [left | right; exact H].
    exists tab, (x_tabn cx). split; [exact HinT|]. split; [intros E; apply Hmt_tab; symmetry; exact E|].
    rewrite Hreqt. exact H.
  - rewrite Hreqm. unfold x_mtn, seg_spec.MVLAN_SIZE. lia. }
pose proof (HGD3 HGDA) as HGD3'.
(* the registers after the call *)
assert (P3 : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr regsA (Z_to_bv 5 r)) by exact HP3.
assert (R3_9 : getr regs3 9 = w64 (x_s1 cx))
  by exact (eq_trans (P3 9 ltac:(unfold acallee_saved; lia)) (eq_trans QA9 R9)).
assert (R3_20 : getr regs3 20 = w64 (x_fr cx + FO_N))
  by exact (eq_trans (P3 20 ltac:(unfold acallee_saved; lia)) PA20).
(* ---- 0x85e74 .. 0x85e90, the jal of check_declared ---- *)
set (len1 := Z.of_nat (length (snd gd))) in *. set (mn := Z.of_nat (length (snd wd))) in *.
assert (Hlen1 : 0 <= len1 <= 39) by (unfold len1; lia).
assert (Hmn : 0 <= mn <= 39) by (unfold mn; lia).
assert (Hmt64 : 0 <= mt < 2 ^ 64) by (unfold x_mtn, seg_spec.MVLAN_SIZE in HmtC; lia).
assert (S112' : rdword (rdW W3 mem3) (x_s1 cx + 112) = Some (fst wd mod 2 ^ 64))
  by (rewrite <- S112; apply rdword_ext; intros q Hq; apply (proj1 K03); lia).
assert (S120' : rdword (rdW W3 mem3) (x_s1 cx + 120) = Some mt)
  by (rewrite <- S120; apply rdword_ext; intros q Hq; apply (proj1 K03); lia).
assert (S128' : rdword (rdW W3 mem3) (x_s1 cx + 128) = Some mn)
  by (rewrite <- S128; apply rdword_ext; intros q Hq; apply (proj1 K03); lia).
apply (s16_runC cx ly S3 W3 regs3 mem3 md3 k len1 (fst wd mod 2 ^ 64) mt mn _ HJ3 R3_9 R3_20 HF4
  ltac:(lia) ltac:(lia) Hlen1 HNV3 S112' S120' S128').
intros regsC memC mdC QC PC11 PC12 PC13 PC14 PC15 PC16 PC20 PC1 KEEPC HJC.
Ltac s16_inbv := cbn [In]; repeat (first [left; reflexivity | left; apply bv_eq; reflexivity | right]).
assert (HFR3C : k24_fregs regs3 regsC).
{ intros r Hr. destruct Hr as [-> | [-> | [-> | [-> | ->]]]]; apply QC; s16_inbv. }
assert (HFRAC : k24_fregs regs regsC)
  by exact (k24_fregs_trans _ _ _ HFRA (k24_fregs_trans _ _ _ (k24_fregs_of_pres _ _ HP3) HFR3C)).
pose proof (k24_kept_trans cx W W3 W3 mem mem3 memC K03 (k24_kept_all cx W3 W3 mem3 memC KEEPC)) as K0C.
assert (HBL3 : lt_blocks B cx ly S3 [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)])
  by exact (Permutation_trans HPerm3 HBL).
assert (HBUD3 : lt_bud MT cx S3 k acc 4) by (rewrite ES3; exact (k24_bud_noalloc cx S k acc 4 f3 HBUD)).
pose proof (k24_core_step_f cx ly S W regs mem md k acc 4 LFO_N _ ly S3 W3 regsC memC mdC k acc 4 _
  HBASE HCORE HJC HFRAC K0C HBL3 HBUD3) as HCOREC.
pose proof HCOREC as ((_ & _ & _ & _ & _ & _ & HSVC & _) & (HRODC & _) & _).
destruct (k24_chain cx ly S3 W3 memC mdC k HBASE HJC HSVC) as (ch2 & HCH2).
(* check_declared's premises *)
set (got := fst gd mod 2 ^ 64) in *. set (want := fst wd mod 2 ^ 64) in *.
pose proof (proj1 HJC) as HARC.
assert (HCPRE : check_declared_pre B ly S3 (rdW W3 memC) got want tab len1 mt mn (x_cap cx) (fst gd) (fst wd)
  (snd gd) (snd wd)).
{ apply (k24_chk_pre cx ly S3 W3 memC mdC tab mt got want HBASE HARC HinT3 HinMT3 Hmc32 eq_refl eq_refl
    ltac:(lia) (k24_rtab_ext _ _ tab _ KEEPC HRT3) (k24_guard_ext _ _ tab _ KEEPC HGD3')
    (k24_mtab_ext _ _ mt _ KEEPC HMT3) HmnLe). }
pose proof (Z.mod_pos_bound (fst gd) (2 ^ 64) ltac:(lia)) as Hgm.
assert (PC10' : getr regsC 10 = w64 got)
  by (unfold got; rewrite k24_w64_mod; exact (eq_trans (QC 10%bv ltac:(s16_inbv)) R10d)).
assert (PC12' : getr regsC 12 = w64 tab)
  by exact (eq_trans PC12 (eq_trans (P3 21 ltac:(unfold acallee_saved; lia)) PA21)).
assert (PC16' : getr regsC 16 = w64 (x_cap cx))
  by exact (eq_trans PC16 (eq_trans (P3 19 ltac:(unfold acallee_saved; lia)) PA19)).
assert (HEVC : st_nev S3 + EV_check_declared <= EV_MAX).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _). pose proof HBUD3 as (Hk0 & _ & Hkr & _).
  pose proof HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV0 & _). unfold EV_check_declared. lia. }
assert (HspC : spZ regsC = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. transitivity (bv_unsigned (w64 (x_s1 cx)));
    [f_equal; exact (eq_trans (HFRAC 2 ltac:(lia)) R2) | unfold w64; rewrite unsigned_lit_small by lia; lia]. }
assert (Hs0C : s0Z regsC = x_sp0 cx).
{ unfold s0Z. transitivity (bv_unsigned (w64 (x_sp0 cx)));
    [f_equal; exact (eq_trans (HFRAC 8 ltac:(lia)) R8) | unfold w64; apply unsigned_lit_small; lia]. }
assert (HgpC : getr regsC 3 = w64 (as_gp B)) by exact (eq_trans (HFRAC 3 ltac:(lia)) (eq_trans R3 Hgp0)).
assert (HtpC : getr regsC 4 = w64 (as_tp B)) by exact (eq_trans (HFRAC 4 ltac:(lia)) (eq_trans R4 Htp0)).
assert (HraC : YK0s.ret_ok (getr regsC 1)) by (rewrite PC1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4C : 4096 <= bv_unsigned (getr regsC 1)) by (rewrite PC1; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (HCH2' : achain ly (rdW W3 memC) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regsC) ch2)
  by (rewrite Hs0C; replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia; exact HCH2).
assert (HSTKC : STK_check_declared = 8304) by reflexivity.
pose proof (fun HPRE1 => HCHECK_DECLARED fx ly S3 W3 regsC memC mdC ch2 got want tab len1 mt mn (x_cap cx)
  (fst gd) (fst wd) (snd gd) (snd wd) HPRE1 HRODC PC10' Hgm PC11 Hwm PC12' Ht64 PC13 ltac:(lia) PC14 Hmt64 PC15
  ltac:(lia) PC16' ltac:(lia) HCPRE HEVC) as HCALL2.
lazymatch type of HCALL2 with _ -> SRr _ _ _ (apost_base _ _ _ _ _ _ _ _ _ _ _ ?Kq) => set (KQ2 := Kq) in HCALL2 end.
eapply SRr_bind.
{ apply (cl_callS B LAWS W3 regsC memC (Z_to_bv 64 (BASE + AF_check_declared)) STK_LLVMFuzzerTestOneInput
    (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S3 mdC k
    STK_check_declared [] EV_check_declared (x_s1 cx - x_sp0 cx) (getr regsC 1) ch2 KQ2 HJC HspC
    Emod ltac:(lia) ltac:(rewrite HSTKC; lia)
    ltac:(rewrite HSTKC; unfold STK_LLVMFuzzerTestOneInput; lia) HgpC HtpC eq_refl HraC Hra4C HCH2').
  - intros HPRE1. eapply SRr_mono; [exact (HCALL2 HPRE1)|].
    unfold apost_base. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & Ec & HJ5 & HP5 & HQ5).
    exists ly5, S5, regs5, mem5, md5. split; [exact Ec|]. split; [exact HJ5|]. split; [exact HP5 | exact HQ5].
  - intros a (r & [] & _). }
cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HK5).
unfold KQ2 in HK5. destruct HK5 as (HSK5 & (HPerm5 & -> & (f5 & ES5))).
change EV_check_declared with 0 in HJ5. rewrite Z.add_0_r in HJ5.
rewrite PC1.
(* what check_declared kept, and the cut's facts at its return *)
pose proof (k24_kept_of_sa_kept cx ly S3 W3 memC mdC k W5 mem5 regsC STK_check_declared HBASE HJC
  ltac:(rewrite HspC; lia) ltac:(rewrite HSTKC; unfold ASTACK; lia) HSK5) as K5.
assert (HBL5 : lt_blocks B cx ly S5 [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)])
  by exact (Permutation_trans HPerm5 HBL3).
assert (HBUD5 : lt_bud MT cx S5 k acc 4) by (rewrite ES5; exact (k24_bud_noalloc cx S3 k acc 4 f5 HBUD3)).
pose proof (k24_core_step cx ly S3 W3 regsC memC mdC k acc 4 LFO_N _ ly S5 W5 regs5 mem5 md5 k acc 4 _
  HBASE HCOREC HJ5 HP5 K5 HBL5 HBUD5) as HCORE5.
pose proof (k24_kept_trans cx W W3 W5 mem memC mem5 K0C K5) as K05.
assert (P5 : forall r, acallee_saved r -> getr regs5 (Z_to_bv 5 r) = getr regsC (Z_to_bv 5 r)) by exact HP5.
assert (R5_20 : getr regs5 20 = w64 mt) by exact (eq_trans (P5 20 ltac:(unfold acallee_saved; lia)) PC20).
(* ---- 0x85e94 .. 0x85e98: free(mt), back at K85e9c ---- *)
change (mkCfg (mkst regs5 (w64 (BASE + 0x10d4)) mem5 (seg_rom SEGS)) md5)
  with (cfg_at SEGS (BASE + 0x10d4) regs5 mem5 md5).
apply (s16_free3 cx ly S5 W5 regs5 mem5 md5 k acc _ mt (x_mtn cx) _ HBASE HCORE5 R5_20).
intros ly6 S6 W6 regs6 mem6 md6 HCORE6 HP6 HK6.
pose proof HCORE6 as ((HJ6 & _) & _ & HBL6 & _).
pose proof (proj1 HJ6) as HAR6.
assert (P6 : forall r, acallee_saved r -> getr regs6 (Z_to_bv 5 r) = getr regs5 (Z_to_bv 5 r)) by exact HP6.
(* a callee-saved register of the cut, from the run of 0x85e50 through both calls, the run of 0x85e74 and free *)
assert (KR : forall (n : Z) (rr : bv 5), acallee_saved n -> Z_to_bv 5 n = rr ->
  In rr ([18; 21; 24]%bv : list (bv 5)) -> getr regs6 rr = getr regsA rr).
{ intros n rr Hn <- Hin. rewrite (P6 n Hn), (P5 n Hn). rewrite (QC (Z_to_bv 5 n)).
  - exact (P3 n Hn).
  - destruct Hin as [E | [E | [E | []]]]; rewrite <- E; s16_inbv. }
assert (R6_18 : getr regs6 18 = w64 c)
  by exact (eq_trans (KR 18 18%bv ltac:(unfold acallee_saved; lia) eq_refl ltac:(s16_inbv)) PA18).
assert (R6_21 : getr regs6 21 = w64 tab)
  by exact (eq_trans (KR 21 21%bv ltac:(unfold acallee_saved; lia) eq_refl ltac:(s16_inbv)) PA21).
assert (R6_24 : getr regs6 24 = w64 m)
  by exact (eq_trans (KR 24 24%bv ltac:(unfold acallee_saved; lia) eq_refl ltac:(s16_inbv)) (eq_trans QA24 R24)).
assert (HSL6 : lt_slots cx (rdW W6 mem6) (LT_LF cx)).
{ intros off v Hoff.
  assert (Hoff2 : (off = 16 \/ off = 24) /\ v = x_fr cx)
    by (unfold LT_LF in Hoff; cbn [In] in Hoff; destruct Hoff as [Hq|[Hq|[]]]; injection Hq as <- <-; auto).
  destruct Hoff2 as [Hoff2 ->].
  assert (H0 : rdword (rdW W mem) (x_s1 cx + off) = Some (x_fr cx))
    by (apply HSL; destruct Hoff2 as [-> | ->]; s16_inbv).
  apply (s24_word_of_kept W6 mem6 W5 mem5 (x_s1 cx + off) (x_fr cx) (x_s1 cx) HK6); [lia | lia|].
  rewrite <- H0. apply rdword_ext. intros q Hq. apply (proj1 K05). lia. }
exact (K9c fx cx ly6 S6 W6 regs6 mem6 md6 (k + 1) (acc + mo_free MT) c m tab HBASE HFRM HCORE6
  (s24_hblk_of_AR ly6 S6 W6 mem6 md6 c _ HAR6 (k24_blk_in cx ly6 S6 _ _ HBL6 ltac:(right; right; left; reflexivity)))
  (s24_hblk_of_AR ly6 S6 W6 mem6 md6 m _ HAR6 (k24_blk_in cx ly6 S6 _ _ HBL6 ltac:(right; left; reflexivity)))
  (s24_hblk_of_AR ly6 S6 W6 mem6 md6 tab _ HAR6 (k24_blk_in cx ly6 S6 _ _ HBL6 ltac:(left; reflexivity)))
  R6_18 R6_21 R6_24 HSL6).
Qed.

(* ================= S20: 0x85eb4 .. 0x85ec4: n out of scope (SH(FR) + 32 := 0xf8), a6 / a7 := FR ================= *)
(* the seed at 0x85eb4: every register its own atom, atom 32 = FR, atom 33 = SH(FR); the one-byte write window of n's
   shadow byte SH(FR) + 32 (base atom 33) and the three read-only slots 16(s1), 24(s1) (FR) and 184(s1) (SH(FR)),
   base s1 (atom 9). The run's shadow span is (0, 0): the five instructions run no instrumented check, and the write
   window lies in the shadow band, which sh_static_ok's cells_safe_b asks the span to miss (image A's S16 .. S20
   walk, the same segment at 0x85c34, commit 68d839b8d799, s24p_span) *)
Definition s20_rsh : YP09.region := YP09.mkRegion (Some 33%nat) 32 33 32 33 [].
Definition s20_rsl : YP09.region := YP09.mkRegion (Some 9%nat) 16 192 0 0
  [YP09.mkChunk 16 (CVal 8 (SOff 32 0)); YP09.mkChunk 24 (CVal 8 (SOff 32 0));
   YP09.mkChunk 184 (CVal 8 (SOff 33 0))].
Definition s20_facts : facts := mkFacts [(33%nat, mkAF 0 kHighShadowEnd 0)] [] [].
Definition s20_ss : sstate := mkSS LO_K85eb4 sr_atoms [s20_rsh; s20_rsl] None s20_facts.
Definition s20_span : Z * Z := (0, 0).

(* the 36 shadow bytes after n's byte (index 32) is set to 0xf8: the LFO0 pattern (image A's s24p_fsh_n0) *)
Lemma s20_fsh_n0 : forall (rd rd' : reader) sh,
  sa_zs rd sh (lt_fsh LFO_N) -> (forall i, 0 <= i < 36 -> i <> 32 -> rd' (sh + i) = rd (sh + i)) ->
  rd' (sh + 32) = Some 0xf8 -> sa_zs rd' sh (lt_fsh LFO0).
Proof.
intros rd rd' sh H HK H32 i Hi. rewrite lt_fsh_len in Hi.
destruct (Nat.eq_dec i 32) as [-> | Hne].
- exact H32.
- rewrite (HK (Z.of_nat i)) by lia.
  replace (nth i (lt_fsh LFO0) 0) with (nth i (lt_fsh LFO_N) 0).
  + exact (H i ltac:(rewrite lt_fsh_len; exact Hi)).
  + do 36 (destruct i as [|i]; [first [reflexivity | lia] |]). lia.
Qed.
(* a shadow byte lies between the low shadow's start and the high shadow's end *)
Lemma s20_band_bounds : forall a, in_band_rw a -> 0x7fff7000 <= a < 0x10007fff8000.
Proof. intros a H. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in H. lia. Qed.

Theorem lt_seg_S20 : lt_seg_S20_stmt B MT.
Proof.
unfold lt_seg_S20_stmt. intros HA.
unfold LT_K85eb4_stmt. intros cx ly S W regs mem md k acc HBASE HFRM HCORE HSL.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof HCORE as (HFRAMEc & HIMGc & HBLKc & HBUDc).
pose proof HFRAMEc as (HJ & _ & _ & _ & _ & H9 & _ & _ & _ & _ & _ & _ & HZS & HSH).
pose proof (proj1 HJ) as HAR.
(* where s1, FR and SH(FR) lie, without a mod or a disjunction in the context *)
pose proof (k24_nums cx HBASE) as (_ & _ & Hs1 & Hceil & H47 & _ & _).
destruct (k24_frame_at cx ly S W mem md k HJ) as (HinF & EFA & Hfr4 & Hfrc & Happ & _ & _ & HSHP).
destruct (k24_low cx ly S W mem md k HBASE HJ) as (_ & Hlow & _).
assert (Hlow' : x_sh cx + 64 <= x_s1 cx) by (unfold ASTACK in Hlow; lia).
clear Hlow.
pose proof (proj1 alloc_ceiling_value) as HAC.
assert (EFR : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact EFA.
assert (EFB : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
(* n's shadow byte SH(FR) + 32 is a shadow byte of the walk's own frame *)
assert (HBAND : in_band_rw (x_sh cx + 32)).
{ pose proof (s24_frame_shadow_band ly S W mem md (x_fpos cx) 32 HAR HinF ltac:(lia)) as HB0.
  rewrite EFR in HB0. exact HB0. }
pose proof (s20_band_bounds _ HBAND) as HBB.
(* the slots 16(s1) and 24(s1) hold FR *)
assert (SL16 : rdword (rdW W mem) (x_s1 cx + 16) = Some (x_fr cx)) by (apply HSL; cbn [LT_LF In]; left; reflexivity).
assert (SL24 : rdword (rdW W mem) (x_s1 cx + 24) = Some (x_fr cx))
  by (apply HSL; cbn [LT_LF In]; right; left; reflexivity).
(* the seed *)
set (E := Eimg (Ereg regs [w64 (x_fr cx); w64 (x_sh cx)])).
assert (HEI : img_env (@pa_val _ seg_listing PI) A_LIM E) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regs [w64 (x_fr cx); w64 (x_sh cx)]) E)
  by (split; [intros i Hi; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = w64 (x_fr cx)).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs [w64 (x_fr cx); w64 (x_sh cx)] 0). }
assert (E33 : ew E 33 = w64 (x_sh cx)).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs [w64 (x_fr cx); w64 (x_sh cx)] 1). }
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = x_sh cx) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS (@pa_val _ seg_listing PI) E s20_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85eb4)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s20_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold s20_rsh, s20_rsl. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U33. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). replace (x_sh cx + o) with (x_sh cx + 32) by lia.
      exact (HSHP 32 ltac:(lia)).
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      assert (DF : sv_denot E (SOff 32 0) = Z_to_bv 64 (x_fr cx))
        by (cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
      assert (DS : sv_denot E (SOff 33 0) = Z_to_bv 64 (x_sh cx))
        by (cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
      assert (BF : 0 <= x_fr cx < 2 ^ (8 * Z.of_N 8)) by (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
      assert (BS : 0 <= x_sh cx < 2 ^ (8 * Z.of_N 8)) by (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
      assert (B8 : Z.of_N 8 <= 8) by (change (Z.of_N 8) with 8; lia).
      constructor; [|constructor; [|constructor; [|constructor]]].
      * exact (chunk_ok_val SEGS E _ (x_s1 cx) 16 8 (SOff 32 0) (x_fr cx) DF BF B8
          (val_mem_of_rdword SEGS (w_H W) mem _ _ SL16)).
      * exact (chunk_ok_val SEGS E _ (x_s1 cx) 24 8 (SOff 32 0) (x_fr cx) DF BF B8
          (val_mem_of_rdword SEGS (w_H W) mem _ _ SL24)).
      * exact (chunk_ok_val SEGS E _ (x_s1 cx) 184 8 (SOff 33 0) (x_sh cx) DS BS B8
          (val_mem_of_rdword SEGS (w_H W) mem _ _ HSH)).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, s20_rsh, s20_rsl.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U33, U9.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold facts_ok, s20_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U33, Z.pow_0_r, Z.mod_1_r.
    unfold kHighShadowEnd. repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity; lia. }
assert (SHOK : sh_ok SEGS s24_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
(* 0x85eb4 .. 0x85ec4: a0 := -8, a1 := SH(FR) from 184(s1), SH(FR) + 32 := 0xf8, a6 := FR from 24(s1),
   a7 := FR from 16(s1); the run stops at 0x85ec8 *)
paj_run_to_tok RUNTO HS HJ SHOK s20_span 0x1108.
- (* what the run may write: n's shadow byte, a shadow byte of the walk's own frame (LT_FCLS, x_fpos cx) *)
  intros a (r & Hin & Ha). unfold s20_ss in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; unfold s20_rsh, s20_rsl in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  + rewrite U33 in Ha. right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFR, EFB. change (512 / 8) with 64. unfold x_sh in Ha. lia.
  + rewrite U9 in Ha. exfalso. lia.
- lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  pmkst HS.
  lazymatch type of HS with context [restrict _ ?m] => rename m into msK end.
  prreg HS (16%bv : bv 5) P16. prreg HS (17%bv : bv 5) P17.
  assert (G16 : getr (ms_regs msK) 16 = w64 (x_fr cx))
    by (rewrite P16; first [exact E32 | rewrite E32; unfold w64; rewrite ?Z_to_bv_bv_unsigned; reflexivity]).
  assert (G17 : getr (ms_regs msK) 17 = w64 (x_fr cx))
    by (rewrite P17; first [exact E32 | rewrite E32; unfold w64; rewrite ?Z_to_bv_bv_unsigned; reflexivity]).
  assert (HPRES : aregs_preserved regs (ms_regs msK)).
  { eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [w64 (x_fr cx); w64 (x_sh cx)]);
      [exact HS | exact HAE | vm_compute; reflexivity]. }
  (* every byte but SH(FR) + 32 is kept: the run's frame_of over the seed's two windows *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> a <> x_sh cx + 32 -> rdW W (ms_mem msK) a = rdW W mem a).
  { intros a Ha Hne. apply (aview_eq_of SEGS). apply HFr. rewrite unsigned_lit_small by lia.
    intros (r & Hin & Hr). unfold s20_ss in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<- | [<- | []]]; unfold s20_rsh, s20_rsl in Hr;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite U33 in Hr | rewrite U9 in Hr]; lia. }
  (* the new byte SH(FR) + 32: 0xf8, from the chunk the store left in the shadow region *)
  assert (HN32 : rdW W (ms_mem msK) (x_sh cx + 32) = Some 0xf8).
  { lazymatch type of HS with st_ok_pi _ _ _ ?ssB _ =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
      pose proof (PaLibG.st_ok_pi_region_nth E ssB (restrict (w_H W) msK) 0 r0 HS ltac:(vm_compute; reflexivity)) as RSH end.
    destruct RSH as (_ & _ & _ & CSH).
    cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in CSH. rewrite U33 in CSH.
    apply Forall_inv in CSH.
    destruct (CSH 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
    cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. injection Hb1 as <-.
    rewrite Z.add_0_r in Hb2. unfold aview. rewrite Hb2. reflexivity. }
  assert (HZS0 : sa_zs (rdW W (ms_mem msK)) (x_sh cx) (lt_fsh LFO0)).
  { apply (s20_fsh_n0 (rdW W mem) _ _ HZS); [|exact HN32].
    intros i Hi Hne. apply KEEP; lia. }
  (* what k24_frame_kept reads: the stack from s1 up, the frame's header and flag words *)
  assert (KS : forall a, x_s1 cx <= a < x_sp0 cx -> rdW W (ms_mem msK) a = rdW W mem a)
    by (intros a Ha; apply KEEP; lia).
  assert (KF : forall a, x_fr cx <= a < x_fr cx + 24 \/ x_fr cx + 504 <= a < x_fr cx + 512 ->
    rdW W (ms_mem msK) a = rdW W mem a).
  { intros a Ha. assert (Ha' : x_fr cx <= a < x_fr cx + 512) by lia.
    apply KEEP; [lia|]. intros Heq.
    apply (s24_app_not_band a); [exact (in_app_addr (x_fr cx) 512 a Happ Ha') | rewrite Heq; exact HBAND]. }
  assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> rdW W (ms_mem msK) a = rdW W mem a).
  { intros a Hi _ _. pose proof (pa_img_range _ Hi) as HIR. unfold kImgEnd in HIR. apply KEEP; lia. }
  (* lt_core at 0x85ec8, with n out of scope *)
  assert (HCORE2 : lt_core B MT cx ly S W (ms_regs msK) (ms_mem msK) mdv k acc 0 LFO0 []).
  { split; [exact (k24_frame_kept cx ly S W regs mem md k LFO_N ly S W (ms_regs msK) (ms_mem msK) mdv k LFO0
              HBASE HFRAMEc HJ (k24_fregs_of_pres _ _ HPRES) KS KF HZS0)|].
    split; [apply (s24_img_kept cx ly S W (ms_mem msK) mdv (rdW W mem) (proj1 HJ)); [exact KI | exact HIMGc]|].
    split; [exact HBLKc | exact HBUDc]. }
  exact (HA fx cx ly S W (ms_regs msK) (ms_mem msK) mdv k acc HBASE HFRM HCORE2 G16 G17).
Qed.

End e.
End f.
End d.
