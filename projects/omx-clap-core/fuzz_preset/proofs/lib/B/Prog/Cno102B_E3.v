(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (route (B''): the call memory in the call rules): Section allocm takes
   YGcallx's new QMm (the call's conjuncts on the state and the call memory) and QMQ (QMm S mem -> QM S); its eight
   _m rules take `QMm Sc <call memory>` instead of `QM Sc`, and pass QMm / QMQ to YGcallx's rules. *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): the free _m rules are proved once over the journal's
   world relation R and the callee's call post APOST (aj_free_x_ct_mR / aj_free_at_x_ct_mR; the old _m names are the
   instances at wle and acall_post_x; aj_free_x_mR / aj_free_at_x_mR likewise); every other call rule here with a
   journal takes it at any R, the old names being their wle instances: aj_intrin_at_xmR, aj_poison_at_x_mR and
   aj_poison_x_mR take R alone; aj_intrin_at_xm_frR, aj_bcmp_at_xmR, aj_strcmp_at_xroR, aj_strlen_at_xroR,
   aj_strcmp_at_xromR, aj_strlen_at_xromR, aj_strlen_at_xmR, aj_stack_malloc_at_xmR, aj_set_shadow_at_xmR,
   aj_unpoison_at_x_mR and aj_unpoison_x_mR take R reflexive and transitive, binders first (the stack-malloc form uses
   both to compose the call's own journal into the caller's); the malloc _m rules aj_malloc_x_mR, aj_malloc_x_ct_mR,
   aj_malloc_at_x_mR and aj_malloc_at_x_ct_mR also take wle inside R (YGcallx's malloc R forms); section 12 states the cf
   free forms under the re-hide (aj_free_x_ct_m_rh / aj_free_at_x_ct_m_rh: SRr' segs RZ_cf, the journal at wle' segs
   RZ_cf). *)
(* Modified by Theorem Labs, 2026-10-31 (field round 3 part 3c: memnorm out of every call text): YGcallx.v's leaves
   malloc_leaf_x / free_leaf_x / free_leaf_xA lost their memnorm keep, the conjunct family 4's keep was read from. So
   the eight _m malloc / free rules of section 10, their R forms (_mR) and section 12's two cf free forms (_m_rh) drop
   the keep (MN.memnorm segs memT -> MN.memnorm segs mem2) from their conclusion: each _m / _mR rule is now its
   YGcallx.v original VERBATIM (the _mR forms are proved by it), under its own name for the walks that apply it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallMxmn.v, with its module paths and module names changed; 948 of its 1094 lines of code are new or changed and 2183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Cno102B_E0.v, with its module names and addresses changed; 850 of its 951 lines of code are new or changed and 993 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b):
   SEGMENT CB3 Init of the re-walk of check_no_overread (cno, entry B' 0x819f0 = slot 201 of the whole-program
   listing). Lane R7-4 / CB3 (a Theorem Labs lane; #102 plan, the internal file PLAN-cno-caw-102.md sections 5.0 / 5.2, row
   "CB3 Init | 0x81bbc -> 0x81c40").
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   INPUTS (by path, blobs as named; this file adds none):
     SHARED CONTRACT lib/B/Prog/Cno102B_Base.v 06098b64f859 (a working branch 0e85941c7687, bound
     to the kit CUT a working branch 7cdbb61b5fa0): the cuts cnb_at_init (start) and cnb_ex_read1 /
     cnb_at_read1 (exit), cnb_pre CTX0 D (no DW), the budgeted journal cnb_J D wk (wk = 0 at both cuts), cnb_mid, the
     progress fact cnb_prog, the refused-copy fact cnb_cdead, the listing tables PL_cno_B.
     STEP KIT lib/B/Prog/Cno102B_Ro.v c1b5ec3f8fff (on the same head; cited, never restated): cnb_J_rebase /
     cnb_J_fixed (the journal across a fixed-trace step at the same spent wild budget), cnb_pre_fpre (cnb_pre's fpre
     by its type), ro_from (a conjunct by its type).
     LISTING (the cut's) lib/B/Listing_prog.v c97cc46b3e13 (slots 316-349, re-checked by cnb3_slots below).
     lib/B/PAImg_prog.v is NOT Required: this file is PARAMETRIC over {PA : PAImg B_prog_listing} (owner 12:48Z).
     ENGINE (the cut's P'' set): lib/Reusable/YGcallMxmn.v 3c08bbab8292 (aj_intrin_at_xm / aintrin_realizes_xm: the
     header table's row for memcpy / memset, with the memnorm keep), YGcallMx.v 403da6c072a9 (awr_byte_present_x),
     YC80x.v 14f84f225e8f (srr_inv_laws, SRr_step_inv), YSRrMemnorm.v 5ffa8525936b (srr_inv_call), YCbqG.v
     219748197d6b (ajournal_x read ONLY by its ajx_* projections, ajournal_x_after_write, ajournal_x_materialize, the
     AR_laws_x fields); lib/A/Prog/PRW_StepKit.v 0df3991c13f4; lib/A/Prog/S1Ledger.v 8cf15eeb6311
     (prh_ledger_kept_aview: it keeps the ledger, g_most and g_own_ran_out included); lib/Reusable/YK0u.v
     c1fa05103c55 (wbytes_inside / _outside); lib/Reusable/YImgTop.v d2a97d3111ce (IMG_TOP_B = 0x601000 and its
     value lemma). The kit texts at the cut (lib/A/PRH_Base.v ef7c8ca98529: prh_pst, prh_ledger with `.. ran most own`,
     prh_ledger_blocks / _heads, kept_at; lib/A/PRH_Reader.v 4266e709561a: pj_zeroR; lib/A/PRH_FnReader.v
     f1ae32e3b2cd: prhReader_home; lib/A/PRH_FnCheck.v c40cf3fdcd2a; lib/B/PRH_ImgB.v 3216eca68342).
     The hand-step lemmas (cnb3_step / _pc4 / _hs_addi / _hs_call) are the A' twin's lib/A/Prog/Cno102A_Ro.v
     (a working branch 8bc94560f61: cn_step / cn_pc4 / cn_hs_addi / cn_hs_call) restated over the
     B' contract's names (cnb_cfg, cnb_pc, B_prog_tpi_cno, PL_cno_B); cnb3_final's copy keep (KC) takes its
     head-disjointness from cn_call_keep (same commit).
   THE SEGMENT (DERIVED byte offsets inside check_no_overread; cnb3_slots pins every word):
     460 CNB_INIT  `sb zero, 4(s2)` .. 484 `sb zero, 10(s2)`   the 7 shadow bytes of d1 = F + 32 set to 0
     488 `li a2, 0x38`; 492 `mv a0, s6`; 496 `li a1, 0`; 500 `jal __asan_memset` -> 504 (CNB_MR1)
     504 `sb zero, 16(s2)` .. 528 `sb zero, 22(s2)`            the 7 shadow bytes of d2 = F + 128
     532 `li a2, 0x38`; 536 `mv a0, s5`; 540 `li a1, 0`; 544 `jal __asan_memset` -> 548 (CNB_MR2)
     548 `sb zero, 28(s2)` .. 572 `sb zero, 34(s2)`            the 7 shadow bytes of d3 = F + 224
     576 `li a2, 0x38`; 580 `mv a0, s4`; 584 `li a1, 0`; 588 `jal __asan_memset` -> 592 CNB_READ1
     No branch, no abort edge, no UBSan trap and no ASan report site lies in [460, 592): nothing to refute.
   HOW: the shadow stores are hand steps (cnb3_hs_sb0: one `sb zero` into a byte awr_byte allows, the journal by
   ajournal_x_after_write, ARx by its frame law alx_frame, P by srr_inv_laws through SRr_step_inv); the li / mv steps are
   the twin's hand steps; each memset is YGcallMxmn.aj_intrin_at_xm (OSet) at the text AMEMSET (the header table's
   row; its dest is the walk's own class-3 frame, in_frames of the journal's own), whose range_addressable /
   shadow-hull premises are the seven bytes just stored. P crosses each memset by srr_inv_call at the text's memnorm
   keep: the text states mem' through views only, so srr_inv_laws ALONE DOES NOT SUFFICE (YSRrMemnorm.v :1-5: a generic
   SRr -> invariant is not provable); the segment takes srr_inv_laws and srr_inv_call, as CB8 does at its runtime
   frees (Cno102B_F.v). Everything the exit cut reads outside the three structs, their 7-byte shadow spans and the
   memset's stack window [s1 - ESTACK, s1) is kept (cnb3_final): the frame flag word, the thirteen saved words and the
   three slots (stack at or above s1), the copies and the ledger heads (live blocks, disjoint from the frame by
   ARx_sep_law), the statics (the ledger's g_most = bi_most D and g_own_ran_out = own0 are kept: the memset rule keeps
   every byte outside its window), the
   input (prhReader_home: a block or a read-only global), the read-only image. The run progress fact cnb_prog D
   (cnb_cevs D r1 r2 r3) S passes through unchanged: CB3 makes no run event and leaves the allocator state S alone.
   THE CUT (the kit 7cdbb61b5fa0; this file was proved on the f97c contract, Cno102B_Base.v cd5327470344): cnb_pre is
   cnb_pre CTX0 D (the Variable DW is gone); the journal is cnb_J D 0, the budgeted ajournal_xw at the spent wild
   budget 0. The segment makes no allocator call: each shadow store and each memset row is a FIXED-trace step, made
   on the journal REBASED to the empty budget (the kit's cnb_J_rebase) and UNBASED at the same WS after
   (cnb_J_fixed), so the exit keeps wk = 0. The start cut's new conjunct `own0 <> 0 -> cnb_cdead D` reads D only,
   which the segment does not change: the exit carries it unchanged. The cuts and cnb_pre are read by type (ro_from,
   cnb_pre_fpre), the journal by its ajx_* projections, never by position.
   NAMED ARGUMENT (ONE, the brief's isolated B'-range step), CB1's premise in the same name and text (relayed by
   a Theorem Labs lane 16:0xZ; lib/B/Prog/Cno102B_E1.v :251):
     cnb1_img_top - some segment of the image reaches IMG_TOP_B. Used ONLY by cnb3_pst_frame: a live fake frame lies
       at or above the end of ly_img, which covers every segment (AR_laws_x field 17, alx_img), so at or above
       IMG_TOP_B, and every program static (prh_pst, PRH_ImgB.v's cells, computed) lies below IMG_TOP_B (0x601000 at
       YImgTop.v d2a97d3111ce; also below the old 0x600000). It closes by
       computation at the B' instance (the witness lib/B/PAImg_prog.v's B_prog_cover uses); owner: the B'
       instantiation file, once IMG_TOP_B lands.
   Numerals: 460 .. 592 and 500 / 504 / 544 / 548 / 588 (DERIVED: the offsets above); the listing words and their
   decoded immediates 4 .. 34 / 56 / 0 (DERIVED: Listing_prog.v slots 316-348); 32 / 128 / 224 / 56 / 280 / 512 / 64 /
   8 / 7 / 160 / 192 / 16 / 48 / 24 / 152 (LENGTH: struct offsets and size, the class-3 frame and its shadow, the
   shadow granule, the seven unpoisoned bytes, the realigned frame, the slots and saved words); 4096 + 256 (LENGTH: a
   stack lower bound, by computation); 0 (COUNT: the spent wild budget, cnb_J's wk); register numbers (WORD); 2 ^ 28
   / 2 ^ 29 / 2 ^ 40 / 2 ^ 63 / 2 ^ 64 (LENGTH: offset, code span, address bounds). No ADDRESS: SHADOW_OFF,
   kLowShadowBeg, kHighMemBeg, kLowMemEnd and the allocator ceiling are cited by name. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
(* YK06 is NOT imported: its plain alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YGcallMx YK0u YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_Base Cno102B_Ro.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
(* PRW_StepKit loads YF0v.v, which turns zify's division rewriting off globally; this file's arithmetic on the frame,
   struct and shadow offsets needs it on (the A' files' reset) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- this segment's call sites and return sites: DERIVED byte offsets inside check_no_overread ---- *)
Definition CNB_MS1 : Z := 500.
Definition CNB_MR1 : Z := 504.
Definition CNB_MS2 : Z := 544.
Definition CNB_MR2 : Z := 548.
Definition CNB_MS3 : Z := 588.

(* THE SLOT CHECK on the listing of record: the function's first word and slots 315 + 1 .. 349 (offsets 460 .. 592):
   the 21 shadow stores, the three (li a2, 0x38; mv a0, s_k; li a1, 0; jal __asan_memset) and CB4's auipc *)
Lemma cnb3_slots :
  map (fun k => nth_error B_prog_listing (CNB_SLOT + k))
      [0; 115; 116; 117; 118; 119; 120; 121; 122; 123; 124; 125; 126; 127; 128; 129; 130; 131; 132; 133; 134; 135;
       136; 137; 138; 139; 140; 141; 142; 143; 144; 145; 146; 147; 148]%nat =
  [Some (PW 0xf6010113);
   Some (PW 0x90223); Some (PW 0x902a3); Some (PW 0x90323); Some (PW 0x903a3); Some (PW 0x90423); Some (PW 0x904a3);
   Some (PW 0x90523); Some (PW 0x3800613); Some (PW 0xb0513); Some (PW 0x593);
   Some (PCall AS___asan_memset (1%bv : bv 5));
   Some (PW 0x90823); Some (PW 0x908a3); Some (PW 0x90923); Some (PW 0x909a3); Some (PW 0x90a23); Some (PW 0x90aa3);
   Some (PW 0x90b23); Some (PW 0x3800613); Some (PW 0xa8513); Some (PW 0x593);
   Some (PCall AS___asan_memset (1%bv : bv 5));
   Some (PW 0x90e23); Some (PW 0x90ea3); Some (PW 0x90f23); Some (PW 0x90fa3); Some (PW 0x2090023); Some (PW 0x20900a3);
   Some (PW 0x2090123); Some (PW 0x3800613); Some (PW 0xa0513); Some (PW 0x593);
   Some (PCall AS___asan_memset (1%bv : bv 5));
   Some (PHi (24%bv : bv 5) 9)].
Proof. vm_compute. reflexivity. Qed.

(* ==== PURE HELPERS ==== *)
Lemma cnb3_getr0 : forall regs, getr regs 0%bv = Z_to_bv 64 0.
Proof. intros regs. reflexivity. Qed.
Lemma cnb3_li : forall regs (imm : bv 12), v_addi (getr regs 0%bv) (bv_signed imm) = w64 (bv_signed imm).
Proof. intros regs imm. rewrite cnb3_getr0. unfold v_addi, w64. rewrite unsigned_lit_small by lia. f_equal. Qed.
Lemma cnb3_getr_same : forall regs (r : bv 5) v, bv_eqb r 0%bv = false -> getr (regupd regs r v) r = v.
Proof. intros regs r v H. apply getr_same. intros E. subst r. discriminate H. Qed.
Lemma cnb3_getr_other : forall regs (r r' : bv 5) v, bv_eqb r' r = false -> getr (regupd regs r v) r' = getr regs r'.
Proof. intros regs r r' v H. apply getr_other. intros E. subst r'. rewrite bv_eqb_refl in H. discriminate H. Qed.
Ltac cnb3_getr := repeat first [rewrite cnb3_getr_same by reflexivity | rewrite cnb3_getr_other by reflexivity].

(* the register snapshot (Cno102A_Ro.v's cn_regsat_get / _kept / _pres) *)
Lemma cnb3_regsat_get : forall regs l (r : bv 5) v, cnb_regsat regs l -> In (r, v) l -> getr regs r = w64 v.
Proof. intros regs l r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma cnb3_regsat_pres : forall regs regs' l, cnb_regsat regs l -> aregs_preserved regs regs' ->
  Forall (fun p : bv 5 * Z => acallee_saved (bv_unsigned (fst p))) l -> cnb_regsat regs' l.
Proof.
intros regs regs' l H HP HF. unfold cnb_regsat in *. rewrite Forall_forall in *.
intros [r v] Hin. cbn [fst snd] in *. specialize (HF (r, v) Hin). specialize (H (r, v) Hin). cbn [fst snd] in HF, H.
pose proof (HP (bv_unsigned r) HF) as E. rewrite Z_to_bv_bv_unsigned in E. rewrite E. exact H.
Qed.
Lemma cnb3_pres_get : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP (bv_unsigned r) Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
Ltac cnb3_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?r] =>
    let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end; lia.
Ltac cnb3_forall_cs := repeat (apply Forall_cons; [cbn [fst]; cnb3_cs |]); apply Forall_nil.
Ltac cnb3_in := cbn [app In]; repeat (first [left; reflexivity | right]).

(* a callee-saved register is none of ra, a0, a1, a2 *)
Lemma cnb3_cs_ne : forall r, acallee_saved r ->
  bv_eqb (Z_to_bv 5 r) 1%bv = false /\ bv_eqb (Z_to_bv 5 r) 10%bv = false /\
  bv_eqb (Z_to_bv 5 r) 11%bv = false /\ bv_eqb (Z_to_bv 5 r) 12%bv = false.
Proof.
intros r Hr. unfold acallee_saved in Hr.
assert (Hu : bv_unsigned (Z_to_bv 5 r) = r).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia. }
unfold bv_eqb. rewrite Hu.
repeat split; apply Z.eqb_neq;
  match goal with |- _ <> bv_unsigned ?k => let v := eval vm_compute in (bv_unsigned k) in change (bv_unsigned k) with v end;
  lia.
Qed.

(* a block list read through a pairwise-disjoint map (Cno102A_Ro.v ro_pairwise_map) *)
Lemma cnb3_pairwise_map : forall (f : Z * Z -> Z * Z) (l : list (Z * Z)) x y,
  pairwise zdisjoint (map f l) -> In x l -> In y l -> fst x <> fst y -> zdisjoint (f x) (f y).
Proof.
intros f l. induction l as [|z t IH]; intros x y H Hx Hy Hne; [destruct Hx|].
cbn [map pairwise] in H. destruct H as [Hz Ht].
destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
- exfalso. apply Hne. reflexivity.
- exact (proj1 (Forall_forall _ _) Hz (f y) (in_map f t y Hy)).
- pose proof (proj1 (Forall_forall _ _) Hz (f x) (in_map f t x Hx)) as Hd. unfold zdisjoint in *. lia.
- exact (IH x y Ht Hx Hy Hne).
Qed.

Lemma cnb3_hull_mono : forall (rd : reader) x n n', 0 < n' <= n -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hn H s Hs. apply H.
assert (E1 : shadow_addr (x + n' - 1) <= shadow_addr (x + n - 1))
  by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (E2 : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.

Lemma cnb3_rdword_kept : forall (rd rd' : reader) lo hi x,
  (forall a, lo <= a < hi -> rd' a = rd a) -> lo <= x -> x + 8 <= hi -> rdword rd' x = rdword rd x.
Proof. intros rd rd' lo hi x Hk H1 H2. apply rdword_ext. intros kk Hkk. apply Hk. lia. Qed.

(* the shadow hull of a 56-byte struct at F + c (F 32-aligned, 32 <= c <= 224) lies in F's 64 shadow bytes *)
Lemma cnb3_hull_in : forall F c s, F mod 32 = 0 -> 0 <= F -> 32 <= c <= 224 -> c mod 8 = 0 ->
  shadow_addr (F + c) / 8 * 8 <= s < shadow_addr (F + c + 56 - 1) / 8 * 8 + 8 ->
  shadow_addr F <= s < shadow_addr F + 64.
Proof. intros F c s HF HF0 Hc Hc8 Hs. unfold shadow_addr, SHADOW_OFF in *. lia. Qed.

(* a struct whose seven shadow bytes read 0 is addressable *)
Lemma cnb3_ra_of_zero : forall (rd : reader) F c, F mod 32 = 0 -> 0 <= F -> 0 <= c -> c mod 8 = 0 ->
  (forall j, 0 <= j < 7 -> rd (shadow_addr F + c / 8 + j) = Some 0) ->
  range_addressable rd SHADOW_OFF (F + c) 56.
Proof.
intros rd F c HF HF0 Hc Hc8 Hz x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (shadow_addr F + c / 8 + (x / 8 - F / 8 - c / 8)) by (unfold shadow_addr; lia).
apply Hz. lia.
Qed.

(* ==== THE IMAGE B' WALK CONTEXT: the contract's section context; the PAImg instance is a PARAMETER ==== *)
Section cb3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Instance CB3_PL : PAListing B_prog_listing := PL_cno_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma cnb3_off : CNB_OFF = 804.
Proof. reflexivity. Qed.

(* ---- the hand steps (Cno102A_Ro.v cn_step / cn_pc4 / cn_pcj / cn_hs_addi / cn_hs_call over the B' names) ---- *)
Lemma cnb3_step : forall (W : world SEGS) fxk regs mem md regs' off off' Q,
  0 <= off < 2 ^ 29 -> 0 <= off' < 2 ^ 29 ->
  RiscvSemantics.step SEGS (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CNB_OFF + off))) (mrestrict (w_H W) mem)
      (YK11.seg_rom SEGS)) =
    MachineOk (@YK11.mkst fxk regs' (Z_to_bv 64 (BASE + (CNB_OFF + off'))) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) ->
  (forall X, SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off') regs' mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md regs' off off' Q Ho Ho' Hst HK.
unfold cnb_cfg, cnb_pc, w64. replace (BASE + CNB_OFF + off) with (BASE + (CNB_OFF + off)) by lia.
eapply (SRr_step SEGS pa_wx W); [reflexivity | rewrite (@restrict_mkst_fx fxk); exact Hst |].
intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
cbn [ms_mem YK11.mkst]. rewrite (@unrestrict_mkst_mrestrict fxk).
specialize (HK (m_vm_materialized md')). unfold cnb_cfg, cnb_pc, w64 in HK.
replace (BASE + CNB_OFF + off') with (BASE + (CNB_OFF + off')) in HK by lia. exact HK.
Qed.

Lemma cnb3_pc4 : forall off, 0 <= off < 2 ^ 29 ->
  v_addi (Z_to_bv 64 (BASE + (CNB_OFF + off))) 4 = Z_to_bv 64 (BASE + (CNB_OFF + (off + 4))).
Proof.
intros off Ho. pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _). pose proof cnb3_off as HO.
unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma cnb3_cfg_eq : forall fxk off regs mem md,
  @cnb_cfg SEGS fxk (cnb_pc off) regs mem md =
  mkCfg (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CNB_OFF + off))) mem (YK11.seg_rom SEGS)) md.
Proof. intros. unfold cnb_cfg, cnb_pc, w64. rewrite <- Z.add_assoc. reflexivity. Qed.

Lemma cnb3_hs_addi : forall (W : world SEGS) fxk regs mem md Q off off' w rd rs imm,
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) -> bv_eqb rd 0%bv = false ->
  0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off') (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' w rd rs imm Hpl Hdec Hrd Ho -> HK.
apply (cnb3_step W fxk regs mem md (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) off (off + 4) Q
  ltac:(lia) ltac:(lia)); [|exact HK].
rewrite (@step_addi fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd rs imm
  (@pa_fetch_pw _ _ PL_cno_B PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
rewrite Hrd, (cnb3_pc4 off ltac:(lia)). reflexivity.
Qed.

(* the PCall jal of a listing slot: pc = SIGMA s, ra = the next offset *)
Lemma cnb3_hs_call : forall (W : world SEGS) fxk regs mem md Q off off' s,
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PCall s 1%bv) -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRr SEGS W (@cnb_cfg SEGS fxk (SIGMA s) (regupd regs 1%bv (w64 (cnb_pc off'))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' s Hpl Ho -> HK.
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _). pose proof cnb3_off as HO.
pose proof (cert_slot asym (clookup pa_tbl) VAL SIGMA B_prog_listing pa_cert (CNB_OFF + off) (PCall s 1%bv) Hpl)
  as (Hck & _ & _).
unfold pi_slot_check in Hck. cbv zeta in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + (CNB_OFF + off))) as [wz|] eqn:Hf; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as (Hsz & Hck). apply Z.eqb_eq in Hsz. subst isz.
destruct i; try (cbn in Hck; discriminate Hck).
apply andb_prop in Hck as (Hck & Hsig). apply andb_prop in Hck as (Hrd & _). apply Z.eqb_eq in Hsig.
assert (Erd : rd = 1%bv).
{ unfold bv_eqb in Hrd. apply Z.eqb_eq in Hrd. apply bv_eq. symmetry. exact Hrd. }
subst rd.
pose proof (pa_fetch_ok _ _ Hf) as Hfw.
unfold cnb_cfg, cnb_pc, w64. replace (BASE + CNB_OFF + off) with (BASE + (CNB_OFF + off)) by lia.
eapply (SRr_step SEGS pa_wx W); [reflexivity | rewrite (@restrict_mkst_fx fxk);
  exact (@step_jal_link fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ 1%bv imm Hfw
           (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec) |].
intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
cbn [ms_mem YK11.mkst]. rewrite (@unrestrict_mkst_mrestrict fxk).
specialize (HK (m_vm_materialized md')). unfold cnb_cfg, cnb_pc, w64 in HK.
replace (BASE + CNB_OFF + (off + 4)) with (BASE + (CNB_OFF + (off + 4))) in HK by lia.
change (bv_eqb (1%bv : bv 5) 0%bv) with false. cbv iota.
rewrite (cnb3_pc4 off ltac:(lia)).
replace (btgt (Z_to_bv 64 (BASE + (CNB_OFF + off))) (bv_signed imm)) with (Z_to_bv 64 (SIGMA s)); [exact HK|].
unfold btgt, v_addi. rewrite unsigned_lit_small by lia. rewrite <- Hsig.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARx).
#[local] Notation STK := STK_check_no_overread.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Variable CTX0 : list (list Z).
(* the runtime text of __asan_memset, the header table's memset row (YGcallMxmn.v, with the memnorm keep), at every
   float state (the cut's float state is the one the callees left) *)
Hypothesis AMEMSET : forall fz : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fz) SEGS B ARx OSet (SIGMA AS___asan_memset).
(* THE NAMED ARGUMENT (header; CB1's cnb1_img_top, same name and text): some segment of the image reaches IMG_TOP_B *)
Definition cnb1_img_top : Prop :=
  exists sg, In sg SEGS /\ YImgTop.IMG_TOP_B <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Hypothesis HTOP : cnb1_img_top.

Lemma cnb3_stk_ge : 4096 + 256 <= STK.
Proof. vm_compute. discriminate. Qed.

(* ---- the memory one `sb` of a byte b at a leaves ---- *)
Lemma cnb3_mr_upd_at : forall (H : word -> bool) (mem : word -> option byte) (a : Z) (b : byte),
  0 <= a < 2 ^ 64 -> H (Z_to_bv 64 a) = false ->
  mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 a) [b])) (Z_to_bv 64 a) = Some b.
Proof.
intros H mem a b Ha Hh. unfold mrestrict, munrestrict. rewrite Hh.
rewrite YK0u.wbytes_inside by (cbn [length]; rewrite ?unsigned_lit_small by lia; lia).
rewrite Z.sub_diag. reflexivity.
Qed.
Lemma cnb3_mr_upd_other : forall (H : word -> bool) (mem : word -> option byte) (a : Z) (b : byte) (x : word),
  0 <= a < 2 ^ 64 -> bv_unsigned x <> a ->
  mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 a) [b])) x = mrestrict H mem x.
Proof.
intros H mem a b x Ha Hx. unfold mrestrict, munrestrict. destruct (H x) eqn:E; [reflexivity|].
rewrite YK0u.wbytes_outside by (cbn [length]; rewrite ?unsigned_lit_small by lia; lia).
cbv beta. rewrite E. reflexivity.
Qed.

Lemma cnb3_apresent_aview : forall (H : word -> bool) mem a, apresent H mem a -> aview SEGS H mem a <> None.
Proof. intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

(* ---- ONE `sb zero, imm(rs)` into a byte awr_byte allows: the journal, ARx and P after it ---- *)
Lemma cnb3_hs_sb0 : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall (W : world SEGS) fxk regs mem md Q off w (rs : bv 5) (imm : bv 12) a
    STKa sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k,
  AJ STKa sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Store SZ1 rs 0%bv imm, 4%Z) ->
  0 <= off < 2 ^ 28 ->
  bv_unsigned (getr regs rs) + bv_signed imm = a -> 0 <= a < 2 ^ 64 ->
  awr_byte STKa sp0 FP (ablocks B ly0 S0) (ablocks B ly S) ly own a ->
  P mem ->
  (forall mem' md', AJ STKa sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem' md' k -> P mem' ->
     aview SEGS (w_H W) mem' a = Some 0 ->
     (forall x, 0 <= x < 2 ^ 64 -> x <> a -> aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x) ->
     (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x) ->
     SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc (off + 4)) regs mem' md') Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros P PLAW W fxk regs mem md Q off w rs imm a STKa sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k HJ Hpl Hdec Ho
  Ha Ha64 Hwr HPm HK.
destruct (YGcallMx.awr_byte_present_x (SK := SK) SEGS B prh_pst ARx LAWS STKa sp0 FP ly0 S0 Hp0 W0 mem0 md0 own
  ly S Hp W mem md k a HJ Hwr) as [Hpa Hno].
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_frs HJ) as Hfrs. pose proof (ajx_qt HJ) as HQT.
pose proof Hpa as [Hh _].
assert (HuA : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha64).
assert (Eaddr : v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a) by (unfold v_addi; rewrite Ha; reflexivity).
assert (Hok : RiscvSemantics.store_ok SEGS (mrestrict (w_H W) mem) (Z_to_bv 64 a) 1 = true).
{ apply (store_ok_of_all SEGS 1 _ (Z_to_bv 64 a)); [rewrite HuA; lia|]. intros x Hx. rewrite HuA in Hx.
  assert (Ex : x = Z_to_bv 64 a) by (apply bv_eq; rewrite HuA; lia).
  subst x. exact (apresent_writable SEGS (w_H W) mem a Hpa). }
assert (Hst : RiscvSemantics.step SEGS (restrict (w_H W)
    (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CNB_OFF + off))) mem (YK11.seg_rom SEGS))) =
  MachineOk (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CNB_OFF + (off + 4))))
    (wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 a) [Z_to_bv 8 0]) (YK11.seg_rom SEGS))).
{ rewrite (@restrict_mkst_fx fxk).
  rewrite (@step_sb fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rs 0%bv imm
    (@pa_fetch_pw _ _ PL_cno_B PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec
    ltac:(rewrite Eaddr; exact Hok)).
  rewrite Eaddr, (cnb3_pc4 off ltac:(lia)), N_to_le_bytes_1_small, cnb3_getr0. reflexivity. }
set (mem' := munrestrict (w_H W) mem (wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 a) [Z_to_bv 8 0])).
assert (Hm1 : mrestrict (w_H W) mem' (Z_to_bv 64 a) = Some (Z_to_bv 8 0))
  by (exact (cnb3_mr_upd_at (w_H W) mem a (Z_to_bv 8 0) Ha64 Hh)).
assert (Hm2 : forall x : word, bv_unsigned x <> a -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x)
  by (intros x Hx; exact (cnb3_mr_upd_other (w_H W) mem a (Z_to_bv 8 0) x Ha64 Hx)).
assert (Hva : aview SEGS (w_H W) mem' a = Some 0) by (unfold aview, mbyte; rewrite Hm1; reflexivity).
assert (Hvo : forall x, 0 <= x < 2 ^ 64 -> x <> a -> aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x).
{ intros x Hx Hne. apply aview_eq_of. apply Hm2. rewrite unsigned_lit_small by lia. exact Hne. }
assert (Hpres : forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x).
{ intros x [Hhx [c Hc]]. split; [exact Hhx|].
  destruct (Z.eq_dec (bv_unsigned (Z_to_bv 64 x)) a) as [E|E].
  - assert (Ex : Z_to_bv 64 x = Z_to_bv 64 a) by (apply bv_eq; rewrite E, HuA; reflexivity).
    rewrite Ex in Hhx |- *. pose proof Hm1 as E1. unfold mrestrict in E1. rewrite Hhx in E1.
    exists (Z_to_bv 8 0). exact E1.
  - pose proof (Hm2 _ E) as E2. unfold mrestrict in E2. rewrite Hhx in E2. rewrite E2. exists c. exact Hc. }
assert (HAR' : ARx ly S Hp W mem' md).
{ apply (alx_frame SEGS B ARx LAWS ly S Hp W mem md mem' md HAR).
  - intros x Hx Hown. apply Hvo; [exact Hx|]. intros ->. exact (Hno Hown).
  - intros x Hv. unfold aview, mbyte in Hv |- *.
    destruct (Z.eq_dec (bv_unsigned (Z_to_bv 64 x)) a) as [E|E].
    + replace (Z_to_bv 64 x) with (Z_to_bv 64 a) by (apply bv_eq; rewrite E, HuA; reflexivity).
      rewrite Hm1. cbn. discriminate.
    + rewrite (Hm2 _ E). exact Hv.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros x _ Hx. unfold mem', munrestrict. rewrite Hx. reflexivity. }
assert (HJ' : AJ STKa sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem' md k).
{ apply (ajournal_x_after_write (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PA) STKa sp0 FP ly0 S0 Hp0 W0
    mem0 md0 own ly S Hp W mem md k mem' md (fun x => x = a) S Hp own HJ).
  - intros x Hx Hne. exact (Hvo x Hx Hne).
  - exact Hpres.
  - apply same_but_materialized_refl.
  - intros x Hx. cbv beta in Hx. subst x. left. exact Hwr.
  - exact HAR'.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT.
  - reflexivity. }
rewrite cnb3_cfg_eq.
eapply (SRr_step_inv SEGS pa_wx P PLAW W); [reflexivity | exact Hst | exact HPm |].
intros md' Hs HPm'.
rewrite (same_but_materialized_wvb md md' Hs).
change (SRr SEGS W (mkCfg (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CNB_OFF + (off + 4)))) mem' (YK11.seg_rom SEGS))
  (with_vm_backing (m_vm_lazy md) (m_vm_materialized md') md)) Q).
rewrite <- cnb3_cfg_eq.
apply (HK mem' (with_vm_backing (m_vm_lazy md) (m_vm_materialized md') md)).
- exact (ajournal_x_materialize (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ (m_vm_materialized md') HJ').
- exact HPm'.
- exact Hva.
- exact Hvo.
- exact Hpres.
Qed.

(* ---- the budgeted journal at a materialised model (rebase, YCbqG's materialize, unbase at the same wk) ---- *)
Lemma cnb3_J_mat : forall D wk ly S Hp W mem md k X, cnb_J B ARx D wk ly S Hp W mem md k ->
  cnb_J B ARx D wk ly S Hp W mem (with_vm_backing (m_vm_lazy md) X md) k.
Proof.
intros D wk ly S Hp W mem md k X HJ.
apply (cnb_J_fixed B ARx D wk ly S Hp W mem md k _ _ _ _ _ _ _ HJ).
exact (ajournal_x_materialize (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  X (cnb_J_rebase B ARx D wk ly S Hp W mem md k HJ)).
Qed.

(* the frame F of the cuts is the journal's own class-3 frame at the current layout (layout_le's ly_F, by type) *)
Lemma cnb3_FA : forall D wk ly S Hp W mem md k, cnb_J B ARx D wk ly S Hp W mem md k ->
  frame_addr ly CNB_CID (bi_fpos D) = cnb_F D.
Proof.
intros D wk ly S Hp W mem md k HJ.
pose proof (ajx_ly (cnb_J_rebase B ARx D wk ly S Hp W mem md k HJ)) as Hly.
assert (EF : ly_F ly = ly_F (bi_ly D)) by (unfold layout_le in Hly; ro_from Hly).
unfold cnb_F, frame_addr. rewrite EF. reflexivity.
Qed.

(* ---- THE GEOMETRY of the segment: the frame F, the realigned sp s1 and the stack above the allocator ceiling ---- *)
Definition cnb3_geo (D : cnb_in) : Prop :=
  cnb_F D mod 32 = 0 /\ 4096 <= cnb_F D /\ cnb_F D + 512 <= YM05.alloc_ceiling /\
  (cnb_F D + 512 <= kLowShadowBeg \/ kHighMemBeg <= cnb_F D) /\
  cnb_sp0 D mod 16 = 0 /\ cnb_S1 D mod 32 = 0 /\ cnb_sp0 D - 192 < cnb_S1 D /\ cnb_S1 D <= cnb_sp0 D - 160 /\
  YM05.alloc_ceiling + STK <= cnb_sp0 D /\ cnb_sp0 D <= 2 ^ 47.

Lemma cnb3_geo_of : forall D wk ly S Hp W mem md k,
  cnb_pre (fx := fx) B ARx CTX0 D -> cnb_J B ARx D wk ly S Hp W mem md k -> cnb_frame D ly S W mem -> cnb3_geo D.
Proof.
intros D wk ly S Hp W mem md k HPRE HJ HF.
pose proof (cnb_pre_fpre B ARx CTX0 D HPRE) as HFP.
destruct HFP as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & HROD0 & HSTKHI & HRAC).
destruct Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof (cnb3_FA D wk ly S Hp W mem md k HJ) as HFA.
pose proof (ajx_ar (cnb_J_rebase B ARx D wk ly S Hp W mem md k HJ)) as HAR.
destruct HF as (Hfrs & _).
assert (Hin : In (CNB_CID, bi_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin) as (Hal32 & Happ & _).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin) as (HF4096 & HFceil & _).
rewrite HFA in Hal32, Happ, HF4096, HFceil.
assert (HFB : fs_frame_bytes CNB_CID = 512) by reflexivity. rewrite HFB in Happ, HFceil.
assert (Hsp16 : cnb_sp0 D mod 16 = 0) by exact Hal16.
destruct (cnb_S1_bounds D Hsp16) as (HS1a & HS1b & HS1c).
unfold in_app, ASAN_CEIL in Happ.
unfold cnb3_geo. unfold cnb_sp0 in *.
repeat split; try lia.
Qed.

(* ---- THE BYTES THE SEGMENT MAY CHANGE, per stretch (struct c, its 7 shadow bytes, the memset's stack window), and
   the bytes it keeps ---- *)
Definition cnb3_X (D : cnb_in) (c a : Z) : Prop :=
  (cnb_F D + c <= a < cnb_F D + c + 56) \/
  (shadow_addr (cnb_F D) + c / 8 <= a < shadow_addr (cnb_F D) + c / 8 + 7) \/
  (cnb_S1 D - ESTACK <= a < cnb_S1 D).
Definition cnb3_safe (D : cnb_in) (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\
  (cnb_S1 D <= a \/
   (~ (cnb_F D + 32 <= a < cnb_F D + 280) /\ (a < SHADOW_OFF \/ kHighMemBeg <= a) /\ a < cnb_S1 D - ESTACK)).

Lemma cnb3_safe_notX : forall D c a, cnb3_geo D -> 32 <= c <= 224 -> cnb3_safe D a -> ~ cnb3_X D c a.
Proof.
intros D c a HG Hc (Ha & Hs) HX.
destruct HG as (HF32 & HF0 & HFc & HFapp & Hsp16 & HS32 & HS1 & HS2 & Hsp & H47).
pose proof cnb3_stk_ge as HSTK. pose proof ASAN_CEIL_range as HCR. unfold ASAN_CEIL in HCR.
unfold cnb3_X, shadow_addr, ESTACK, SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *. lia.
Qed.

(* the bytes of one stretch are kept by the other two *)
Lemma cnb3_cross : forall D c c' a, cnb3_geo D -> (c = 32 \/ c = 128 \/ c = 224) -> (c' = 32 \/ c' = 128 \/ c' = 224) ->
  c <> c' ->
  ((cnb_F D + c <= a < cnb_F D + c + 56) \/ (shadow_addr (cnb_F D) + c / 8 <= a < shadow_addr (cnb_F D) + c / 8 + 7)) ->
  0 <= a < 2 ^ 64 /\ ~ cnb3_X D c' a.
Proof.
intros D c c' a HG Hc Hc' Hne Ha.
destruct HG as (HF32 & HF0 & HFc & HFapp & Hsp16 & HS32 & HS1 & HS2 & Hsp & H47).
pose proof cnb3_stk_ge as HSTK. pose proof ASAN_CEIL_range as HCR. unfold ASAN_CEIL in HCR.
unfold cnb3_X, shadow_addr, ESTACK, SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *.
destruct Hc as [-> | [-> | ->]]; destruct Hc' as [-> | [-> | ->]]; try congruence; lia.
Qed.

Lemma cnb3_safe_hi : forall D a, cnb3_geo D -> cnb_S1 D <= a < 2 ^ 64 -> cnb3_safe D a.
Proof.
intros D a HG Ha. destruct HG as (HF32 & HF0 & HFc & HFapp & Hsp16 & HS32 & HS1 & HS2 & Hsp & H47).
pose proof cnb3_stk_ge as HSTK. pose proof ASAN_CEIL_range as HCR. unfold ASAN_CEIL in HCR.
split; [lia | left; lia].
Qed.

(* an image byte is in no live fake frame (ARx_client_img_law), below the shadow and below the stack *)
Lemma cnb3_safe_img : forall D ly S Hp W mem md a, cnb3_geo D -> ARx ly S Hp W mem md ->
  In (CNB_CID, bi_fpos D) (frames S) -> frame_addr ly CNB_CID (bi_fpos D) = cnb_F D -> in_img SEGS a ->
  cnb3_safe D a.
Proof.
intros D ly S Hp W mem md a HG HAR Hin HFA Himg.
pose proof (@pa_segs_low _ _ PA a Himg) as Hlow.
destruct HG as (HF32 & HF0 & HFc & HFapp & Hsp16 & HS32 & HS1 & HS2 & Hsp & H47).
pose proof cnb3_stk_ge as HSTK. pose proof ASAN_CEIL_range as HCR. unfold ASAN_CEIL in HCR.
unfold kLowMemEnd in Hlow.
split; [lia|]. right. split; [|split; [left; unfold SHADOW_OFF; lia | unfold ESTACK; lia]].
intros Hr.
assert (Hfr : exists cid pos, In (cid, pos) (frames S) /\
  frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid).
{ exists CNB_CID, (bi_fpos D). split; [exact Hin|]. rewrite HFA. change (fs_frame_bytes CNB_CID) with 512. lia. }
apply (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md a HAR (or_intror (or_introl Hfr)))).
exact Himg.
Qed.

(* a byte of a live block of size >= 0, or within 8 bytes of its 16-aligned base (a harness head), is in no live fake
   frame (ARx_sep_law: the base is outside the 32-aligned frame), app memory below the allocator ceiling *)
Lemma cnb3_safe_blk : forall D ly S Hp W mem md a b m, cnb3_geo D -> ARx ly S Hp W mem md ->
  In (CNB_CID, bi_fpos D) (frames S) -> frame_addr ly CNB_CID (bi_fpos D) = cnb_F D ->
  In (b, m) (ablocks B ly S) -> 0 <= m -> b <= a < b + Z.max 8 (req_size m) -> cnb3_safe D a.
Proof.
intros D ly S Hp W mem md a b m HG HAR Hin HFA Hb Hm Ha.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _).
pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md b m CNB_CID (bi_fpos D) HAR Hb Hin) as Hdj.
rewrite HFA in Hdj. unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
change (fs_frame_bytes CNB_CID) with 512 in Hdj.
pose proof (req_size_pos m Hm) as (Hreq1 & Hreq2).
destruct HG as (HF32 & HF0 & HFc & HFapp & Hsp16 & HS32 & HS1 & HS2 & Hsp & H47).
pose proof cnb3_stk_ge as HSTK. pose proof ASAN_CEIL_range as HCR. unfold ASAN_CEIL in HCR.
unfold in_app, ASAN_CEIL in Hbapp.
unfold cnb3_safe, ESTACK, SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *. lia.
Qed.

(* every program static of B' (PRH_ImgB.v's cells, computed from the record, no address typed) lies in page 1 and
   below IMG_TOP_B (YImgTop.v's generated value lemma) *)
Lemma cnb3_pst_below : forall a, Exists (in_zr a) prh_pst -> 4096 <= a < YImgTop.IMG_TOP_B.
Proof.
intros a Ha. rewrite YImgTop.IMG_TOP_B_val. unfold prh_pst in Ha.
cbv [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most pi_g_own_ran_out pi_gz_live pi_gz_peak
  pi_gz_count pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out prh_img_B] in Ha.
repeat (apply Exists_cons in Ha as [Ha|Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; lia|]).
inversion Ha.
Qed.
(* THE ONE B'-RANGE STEP (brief "Blocker you may hit: IMG_TOP_B"): a program static is a kept byte. Its statement
   names the fact it needs, cnb1_img_top; proved at IMG_TOP_B's current value (and it holds at 0x601000). *)
Lemma cnb3_pst_frame : cnb1_img_top -> forall D ly S Hp W mem md a, cnb3_geo D -> ARx ly S Hp W mem md ->
  In (CNB_CID, bi_fpos D) (frames S) -> frame_addr ly CNB_CID (bi_fpos D) = cnb_F D ->
  Exists (in_zr a) prh_pst -> cnb3_safe D a.
Proof.
intros (sg & Hsg & Htop) D ly S Hp W mem md a HG HAR Hin HFA Ha.
destruct (alx_img SEGS B ARx LAWS ly S Hp W mem md HAR) as [Hseg Hfr].
destruct (Hseg sg Hsg) as [_ Hend]. pose proof (Hfr CNB_CID (bi_fpos D) Hin) as Hf. rewrite HFA in Hf.
pose proof (cnb3_pst_below a Ha) as Hb. rewrite YImgTop.IMG_TOP_B_val in Htop, Hb.
destruct HG as (HF32 & HF0 & HFc & HFapp & Hsp16 & HS32 & HS1 & HS2 & Hsp & H47).
pose proof cnb3_stk_ge as HSTK. pose proof ASAN_CEIL_range as HCR. unfold ASAN_CEIL in HCR.
unfold cnb3_safe, SHADOW_OFF, ESTACK. lia.
Qed.

(* ---- the shadow stores of one stretch: n `sb zero, (s + j)(s2)` at o + 4 j; each a fixed-trace step on the journal
   rebased to the empty budget (cnb_J_rebase), unbased after at the same wk (cnb_J_fixed) ---- *)
Definition cnb3_sb_slot (off s : Z) : Prop :=
  exists w (imm : bv 12), plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PW w) /\
    decode_any (Z_to_bv 32 w) = Some (Store SZ1 18%bv 0%bv imm, 4%Z) /\ bv_signed imm = s.

Lemma cnb3_stores : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall (n : nat) (D : cnb_in) (o s : Z) fxk wk ly S Hp W regs mem md k Q,
  (forall j, 0 <= j < Z.of_nat n -> cnb3_sb_slot (o + 4 * j) (s + j)) ->
  0 <= o -> o + 4 * Z.of_nat n < 2 ^ 28 -> 0 <= s -> s + Z.of_nat n <= 64 ->
  0 <= cnb_F D -> cnb_F D + 512 <= YM05.alloc_ceiling ->
  frame_addr ly CNB_CID (bi_fpos D) = cnb_F D ->
  getr regs 18%bv = w64 (shadow_addr (cnb_F D)) ->
  cnb_J B ARx D wk ly S Hp W mem md k -> P mem ->
  (forall mem' md', cnb_J B ARx D wk ly S Hp W mem' md' k -> P mem' ->
     (forall j, 0 <= j < Z.of_nat n -> aview SEGS (w_H W) mem' (shadow_addr (cnb_F D) + s + j) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (cnb_F D) + s <= a < shadow_addr (cnb_F D) + s + Z.of_nat n) ->
        aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
     SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc (o + 4 * Z.of_nat n)) regs mem' md') Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc o) regs mem md) Q.
Proof.
intros P PLAW n. induction n as [|n IH];
  intros D o s fxk wk ly S Hp W regs mem md k Q HSB Ho Hon Hs Hsn HF0 HFc HFA R18 HJ HPm HK.
- replace (o + 4 * Z.of_nat 0) with o in HK by lia.
  apply (HK mem md HJ HPm).
  + intros j Hj. cbn in Hj. lia.
  + intros a _ _. reflexivity.
  + intros a Ha. exact Ha.
- destruct (HSB 0 ltac:(lia)) as (w & imm & Hpl & Hdec & Himm).
  rewrite Z.mul_0_r, Z.add_0_r in Hpl. rewrite Z.add_0_r in Himm.
  pose proof ASAN_CEIL_range as HCR. unfold ASAN_CEIL in HCR.
  assert (Hsh : 0 <= shadow_addr (cnb_F D) /\ shadow_addr (cnb_F D) + 64 < 2 ^ 64)
    by (unfold shadow_addr, SHADOW_OFF; lia).
  apply (cnb3_hs_sb0 P PLAW W fxk regs mem md Q o w 18%bv imm (shadow_addr (cnb_F D) + s)
    STK (cnb_sp0 D) [] (bi_ly D) _ (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D) [(CNB_CID, bi_fpos D)] ly S Hp k
    (cnb_J_rebase B ARx D wk ly S Hp W mem md k HJ) Hpl Hdec).
  + lia.
  + rewrite R18, Himm. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + right. right. right. exists CNB_CID, (bi_fpos D). split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite HFA. change (fs_frame_bytes CNB_CID / 8) with 64. lia.
  + exact HPm.
  + intros mem1 md1 HJ1 HP1 Hz1 Hk1 Hp1.
    apply (IH D (o + 4) (s + 1) fxk wk ly S Hp W regs mem1 md1 k Q).
    * intros j Hj. replace (o + 4 + 4 * j) with (o + 4 * (j + 1)) by lia.
      replace (s + 1 + j) with (s + (j + 1)) by lia. apply HSB. lia.
    * lia.
    * lia.
    * lia.
    * lia.
    * exact HF0.
    * exact HFc.
    * exact HFA.
    * exact R18.
    * exact (cnb_J_fixed B ARx D wk ly S Hp W mem md k ly S Hp W mem1 md1 k HJ HJ1).
    * exact HP1.
    * intros mem2 md2 HJ2 HP2 Hz2 Hk2 Hp2.
      replace (o + 4 + 4 * Z.of_nat n) with (o + 4 * Z.of_nat (Datatypes.S n)) by lia.
      apply (HK mem2 md2 HJ2 HP2).
      -- intros j Hj. destruct (Z.eq_dec j 0) as [->|Hj0].
         ++ rewrite Z.add_0_r. rewrite (Hk2 (shadow_addr (cnb_F D) + s)) by lia. exact Hz1.
         ++ replace (shadow_addr (cnb_F D) + s + j) with (shadow_addr (cnb_F D) + (s + 1) + (j - 1)) by lia.
            apply Hz2. lia.
      -- intros a Ha Hna. rewrite (Hk2 a Ha) by lia. apply Hk1; [exact Ha | lia].
      -- intros a Ha. exact (Hp2 a (Hp1 a Ha)).
Qed.

(* ---- ONE STRETCH: the 7 shadow stores of struct c, then (li a2, 0x38; mv a0, rk; li a1, 0; jal __asan_memset) ---- *)
Definition cnb3_addi_slot (off : Z) (rd rs : bv 5) (v : Z) : Prop :=
  exists w (imm : bv 12), plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PW w) /\
    decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) /\ bv_signed imm = v.
Definition cnb3_stretch_slots (o c : Z) (rk : bv 5) : Prop :=
  (forall j, 0 <= j < 7 -> cnb3_sb_slot (o + 4 * j) (c / 8 + j)) /\
  cnb3_addi_slot (o + 28) 12%bv 0%bv 56 /\ cnb3_addi_slot (o + 32) 10%bv rk 0 /\
  cnb3_addi_slot (o + 36) 11%bv 0%bv 0 /\
  plookup B_prog_tpi_cno (CNB_OFF + (o + 40)) = Some (PCall AS___asan_memset 1%bv).

Lemma cnb3_stretch : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall (D : cnb_in) (o c : Z) (rk : bv 5) fxk wk ly S Hp W regs mem md k Q,
  cnb3_stretch_slots o c rk -> 0 <= o -> o mod 4 = 0 -> o + 44 < 2 ^ 28 -> 32 <= c <= 224 -> c mod 8 = 0 ->
  bv_eqb rk 12%bv = false ->
  cnb3_geo D -> frame_addr ly CNB_CID (bi_fpos D) = cnb_F D ->
  cnb_J B ARx D wk ly S Hp W mem md k -> P mem ->
  (forall j, 0 <= j < 64 -> apresent (w_H W) mem (shadow_addr (cnb_F D) + j)) ->
  getr regs 18%bv = w64 (shadow_addr (cnb_F D)) -> getr regs rk = w64 (cnb_F D + c) ->
  getr regs 2%bv = w64 (cnb_S1 D) -> getr regs 3%bv = w64 (as_gp B) -> getr regs 4%bv = w64 (as_tp B) ->
  (forall regs' mem' md', cnb_J B ARx D wk ly S Hp W mem' md' k -> P mem' -> aregs_preserved regs regs' ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ cnb3_X D c a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
     (forall i, 0 <= i < 56 -> aview SEGS (w_H W) mem' (cnb_F D + c + i) = Some 0) ->
     (forall j, 0 <= j < 7 -> aview SEGS (w_H W) mem' (shadow_addr (cnb_F D) + c / 8 + j) = Some 0) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
     SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc (o + 44)) regs' mem' md') Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc o) regs mem md) Q.
Proof.
intros P PLAW PCALL D o c rk fxk wk ly S Hp W regs mem md k Q (HSB & HA1 & HA2 & HA3 & HPC) Ho Ho4 Ho2 Hc Hc8 Hrk12
  HGEO HFA HJ HPm HSHP R18 Rk R2 R3 R4 HK.
pose proof HGEO as (HF32 & HF0 & HFc & HFapp & Hsp16 & HS32 & HS1 & HS2 & Hsp & H47).
pose proof cnb3_stk_ge as HSTK. pose proof ASAN_CEIL_range as HCR. unfold ASAN_CEIL in HCR.
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _). pose proof cnb3_off as HO.
apply (cnb3_stores P PLAW 7 D o (c / 8) fxk wk ly S Hp W regs mem md k Q).
{ intros j Hj. apply HSB. lia. }
{ lia. } { lia. } { lia. } { lia. } { lia. } { exact HFc. } { exact HFA. } { exact R18. } { exact HJ. } { exact HPm. }
intros mem1 md1 HJ1 HP1 Hz1 Hk1 Hp1.
replace (o + 4 * Z.of_nat 7) with (o + 28) by lia.
destruct HA1 as (w1 & i1 & Hpl1 & Hdec1 & Hi1).
apply (cnb3_hs_addi W fxk regs mem1 md1 Q (o + 28) (o + 32) w1 12%bv 0%bv i1 Hpl1 Hdec1 eq_refl ltac:(lia) ltac:(lia)).
intros X1.
destruct HA2 as (w2 & i2 & Hpl2 & Hdec2 & Hi2).
apply (cnb3_hs_addi W fxk _ mem1 _ Q (o + 32) (o + 36) w2 10%bv rk i2 Hpl2 Hdec2 eq_refl ltac:(lia) ltac:(lia)).
intros X2.
destruct HA3 as (w3 & i3 & Hpl3 & Hdec3 & Hi3).
apply (cnb3_hs_addi W fxk _ mem1 _ Q (o + 36) (o + 40) w3 11%bv 0%bv i3 Hpl3 Hdec3 eq_refl ltac:(lia) ltac:(lia)).
intros X3.
apply (cnb3_hs_call W fxk _ mem1 _ Q (o + 40) (o + 44) AS___asan_memset HPC ltac:(lia) ltac:(lia)).
intros X4.
lazymatch goal with |- SRr _ _ (@cnb_cfg _ _ _ ?r _ ?m) _ => set (regsT := r); set (mdT := m) end.
(* the registers at the call *)
assert (T10 : getr regsT 10%bv = w64 (cnb_F D + c)).
{ unfold regsT. rewrite (cnb3_getr_other _ 1%bv 10%bv _ eq_refl), (cnb3_getr_other _ 11%bv 10%bv _ eq_refl),
    (cnb3_getr_same _ 10%bv _ eq_refl).
  rewrite (cnb3_getr_other regs 12%bv rk _ Hrk12), Rk, Hi2. unfold v_addi, w64.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
assert (T11 : getr regsT 11%bv = w64 0).
{ unfold regsT. rewrite (cnb3_getr_other _ 1%bv 11%bv _ eq_refl), (cnb3_getr_same _ 11%bv _ eq_refl).
  rewrite cnb3_li, Hi3. reflexivity. }
assert (T12 : getr regsT 12%bv = w64 56).
{ unfold regsT. rewrite (cnb3_getr_other _ 1%bv 12%bv _ eq_refl), (cnb3_getr_other _ 11%bv 12%bv _ eq_refl),
    (cnb3_getr_other _ 10%bv 12%bv _ eq_refl), (cnb3_getr_same _ 12%bv _ eq_refl).
  rewrite cnb3_li, Hi1. reflexivity. }
assert (T1 : getr regsT 1%bv = w64 (cnb_pc (o + 44))) by (unfold regsT; apply cnb3_getr_same; reflexivity).
assert (TK : forall r, acallee_saved r -> getr regsT (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. destruct (cnb3_cs_ne r Hr) as (N1 & N10 & N11 & N12). unfold regsT.
  rewrite (cnb3_getr_other _ _ _ _ N1), (cnb3_getr_other _ _ _ _ N11), (cnb3_getr_other _ _ _ _ N10),
    (cnb3_getr_other _ _ _ _ N12). reflexivity. }
assert (T2 : getr regsT 2%bv = getr regs 2%bv) by (unfold regsT; cnb3_getr; reflexivity).
assert (T3 : getr regsT 3%bv = getr regs 3%bv) by (unfold regsT; cnb3_getr; reflexivity).
assert (T4 : getr regsT 4%bv = getr regs 4%bv) by (unfold regsT; cnb3_getr; reflexivity).
assert (HJT : cnb_J B ARx D wk ly S Hp W mem1 mdT k)
  by (unfold mdT; repeat apply cnb3_J_mat; exact HJ1).
assert (Hsp' : spZ regsT = cnb_sp0 D + (cnb_S1 D - cnb_sp0 D)).
{ unfold spZ. rewrite T2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* the memset row is a fixed-trace call: made on the journal rebased to the empty budget *)
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_intrin_at_xm (fx := fxk) (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PA) OSet
    (SIGMA AS___asan_memset) (AMEMSET fxk) W regsT mem1 STK (cnb_sp0 D) [] (bi_ly D) _ (bi_Hp D) (bi_W D)
    (bi_mem D) (bi_md D) [(CNB_CID, bi_fpos D)] ly S Hp mdT k (cnb_F D + c) 0 56 (cnb_S1 D - cnb_sp0 D)
    (w64 (cnb_pc (o + 44))) (cnb_J_rebase B ARx D wk ly S Hp W mem1 mdT k HJT) T10 T11 T12).
  - lia.
  - lia.
  - lia.
  - exact Hsp'.
  - lia.
  - lia.
  - unfold ESTACK. lia.
  - rewrite T3. exact R3.
  - rewrite T4. exact R4.
  - exact T1.
  - unfold w64, cnb_pc. rewrite <- Z.add_assoc. apply ret_ok_codeptr_v; [lia|].
    rewrite HO. lia.
  - intros a Ha. split.
    + right. right. right. exists CNB_CID, (bi_fpos D). split; [left; reflexivity|]. left. unfold in_zr.
      cbn [fst snd]. rewrite HFA. change (fs_frame_bytes CNB_CID) with 512. lia.
    + unfold ESTACK. lia.
  - unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *. unfold kLowShadowBeg in HFapp. lia.
  - apply (cnb3_ra_of_zero _ (cnb_F D) c HF32 ltac:(lia) ltac:(lia) Hc8). intros j Hj. apply Hz1. lia.
  - intros _ sx Hsx. apply cnb3_apresent_aview. apply Hp1.
    pose proof (cnb3_hull_in (cnb_F D) c sx HF32 ltac:(lia) Hc Hc8 Hsx) as Hin.
    replace sx with (shadow_addr (cnb_F D) + (sx - shadow_addr (cnb_F D))) by lia. apply HSHP. lia.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & R10' & Hset & Hfr & Hpres5 & Hmn).
cbn iota in Hset.
apply (HK regs5 mem5 md5).
- exact (cnb_J_fixed B ARx D wk ly S Hp W mem1 mdT k ly S Hp W mem5 md5 k HJT HJ5).
- exact (PCALL mem1 mem5 Hmn HP1).
- intros r Hr. rewrite (HP5 r Hr). exact (TK r Hr).
- intros a Ha HX. unfold cnb3_X in HX.
  rewrite (Hfr a Ha) by (unfold ESTACK in *; lia). apply Hk1; [exact Ha | lia].
- intros i Hi. rewrite (Hset i Hi). reflexivity.
- intros j Hj.
  rewrite (Hfr (shadow_addr (cnb_F D) + c / 8 + j)) by (unfold shadow_addr, SHADOW_OFF, ESTACK in *;
    unfold kLowShadowBeg, kHighMemBeg in HFapp; lia).
  apply Hz1. lia.
- intros a Ha. exact (Hpres5 a (Hp1 a Ha)).
Qed.

(* ---- the zeroed struct and the kept copies ---- *)
Lemma cnb3_zero56 : forall (H : word -> bool) mem v, (forall i, 0 <= i < 56 -> aview SEGS H mem (v + i) = Some 0) ->
  pj_zeroR SEGS (mrestrict H mem) v.
Proof.
intros H mem v Hz j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. split; [|lia].
intros kk Hk. assert (kk = 0%nat) by lia. subst kk.
destruct (aview_byte SEGS H mem (v + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Hb. f_equal.
rewrite <- (Z_to_bv_bv_unsigned _ b), <- Hv. reflexivity.
Qed.

(* ---- THE EXIT CUT from the start cut and the memory the three stretches leave; the start cut's conjuncts are read
   by type (the kit's ro_from), its `own0 <> 0 -> cnb_cdead D` passes to the exit unchanged (D is not changed) ---- *)
Lemma cnb3_final : forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0 regsF memF mdF,
  cnb_pre (fx := fx) B ARx CTX0 D ->
  cnb_at_init (fx := fx) B ARx D fxk ly S Hp W regs mem md k r1 r2 r3 own0 ->
  cnb_J B ARx D 0 ly S Hp W memF mdF k -> aregs_preserved regs regsF ->
  (forall a, cnb3_safe D a -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem a) ->
  (forall c i, (c = 32 \/ c = 128 \/ c = 224) -> 0 <= i < 56 -> aview SEGS (w_H W) memF (cnb_F D + c + i) = Some 0) ->
  (forall c j, (c = 32 \/ c = 128 \/ c = 224) -> 0 <= j < 7 ->
     aview SEGS (w_H W) memF (shadow_addr (cnb_F D) + c / 8 + j) = Some 0) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) memF a) ->
  cnb_at_read1 (fx := fx) B ARx D fxk ly S Hp W regsF memF mdF k r1 r2 r3 own0.
Proof.
intros D fxk ly S Hp W regs mem md k r1 r2 r3 own0 regsF memF mdF HPRE HAT HJF HRP HK HZ HZS HPR.
pose proof HAT as HAT'. unfold cnb_at_init in HAT'.
assert (HB : cnb_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k 0) by ro_from HAT'.
assert (HR : cnb_regsat regs (cnb_core D ++ [(23%bv, cnb_size D); (24%bv, bi_data D); (25%bv, r1)]))
  by ro_from HAT'.
assert (HSL : cnb_slots D W mem r2 r3) by ro_from HAT'.
assert (HC1 : cnb_copy B D ly S Hp W mem r1) by ro_from HAT'.
assert (HC2 : cnb_copy B D ly S Hp W mem r2) by ro_from HAT'.
assert (HC3 : cnb_copy B D ly S Hp W mem r3) by ro_from HAT'.
assert (HOWN0 : own0 = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0) by ro_from HAT'.
assert (HDEAD : own0 <> 0 -> cnb_cdead D) by ro_from HAT'.
assert (HPM : cnb_pre_mid B D ly S Hp W mem own0) by ro_from HAT'.
assert (HPROG : cnb_prog D (cnb_cevs D r1 r2 r3) S) by ro_from HAT'.
assert (HPERM : Permutation (ablocks B ly S) (cnb_cblks D r1 r2 r3 ++ ablocks B (bi_ly D) (bi_S D)))
  by ro_from HAT'.
assert (HBB : blocks_bytes S + 3 * PRH_FnPj.LIVE_pj_parse (bi_x D) <= LIVE_MAX) by ro_from HAT'.
assert (HHULL : PresetHullBudget.hull_budget S (cnb_hrest_copies (bi_x D))) by ro_from HAT'.
clear HAT'.
destruct HB as (Hz & Hfk & HJ & HF & HSV & R3 & R4 & HROD).
pose proof (cnb3_geo_of D 0%nat ly S Hp W mem md k HPRE HJ HF) as HGEO.
pose proof (cnb3_FA D 0%nat ly S Hp W mem md k HJ) as HFA.
pose proof (ajx_ar (cnb_J_rebase B ARx D 0%nat ly S Hp W mem md k HJ)) as HAR.
pose proof (ajx_ar (cnb_J_rebase B ARx D 0%nat ly S Hp W memF mdF k HJF)) as HARF.
pose proof HF as (Hfrs & Hnin & Hflag & Hfpres & Hspres).
assert (Hin : In (CNB_CID, bi_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct HPM as (EHp & HLED & HRL & HSRC & HHOME).
pose proof HGEO as (HF32 & HF0 & HFc & HFapp & Hsp16 & HS32 & HS1a & HS1b & Hsp & H47).
pose proof cnb3_stk_ge as HSTK. pose proof ASAN_CEIL_range as HCR. unfold ASAN_CEIL in HCR.
assert (HFB : fs_frame_bytes CNB_CID = 512) by reflexivity.
assert (Hh0 : 0 <= cf_head) by exact (@cf_head_nonneg cp).
(* the kept bytes, by kind *)
assert (KHI : forall a, cnb_S1 D <= a < 2 ^ 64 -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply HK; apply cnb3_safe_hi; [exact HGEO | exact Ha]).
assert (KIMG : forall a, in_img SEGS a -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply HK; exact (cnb3_safe_img D ly S Hp W mem md a HGEO HAR Hin HFA Ha)).
assert (KBLK : forall b m a, In (b, m) (ablocks B ly S) -> 0 <= m -> b <= a < b + Z.max 8 (req_size m) ->
  aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem a)
  by (intros b m a Hb Hm Ha; apply HK; exact (cnb3_safe_blk D ly S Hp W mem md a b m HGEO HAR Hin HFA Hb Hm Ha)).
assert (KPST : forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply HK; exact (cnb3_pst_frame HTOP D ly S Hp W mem md a HGEO HAR Hin HFA Ha)).
assert (KRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a).
{ intros a [(sg & Hsg & _ & Hlo & Hhi) | Hrel]; [exists sg; split; [exact Hsg | lia] | exact (pa_relro_img a Hrel)]. }
(* the ledger at memF *)
assert (HLEDF : prh_ledger B ly S Hp W memF (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D) (bi_most D) own0).
{ apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W memF (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D)
    (bi_most D) own0 HLED).
  - exact KPST.
  - intros a kk i Hak Hi.
    pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem (bi_Lam D) (bi_peak D) (bi_cnt D)
      SIZE_MAXZ (bi_ran D) (bi_most D) own0 HLED) (a, kk) Hak) as (Hkk0 & Hab & _). cbn [fst snd] in Hkk0, Hab.
    apply (KBLK _ _ _ Hab ltac:(lia)). lia.
  - intros a kk _ Hb. exact Hb.
  - apply Permutation_refl. }
(* the copies at memF *)
assert (KC : forall r, cnb_copy B D ly S Hp W mem r -> cnb_copy B D ly S Hp W memF r).
{ intros r [Hr0 | (Hinr & Hnh & Hsrc)]; [left; exact Hr0|]. right. split; [exact Hinr|]. split; [exact Hnh|].
  destruct Hsrc as (Hby & H4096r & Hceilr & Hamrr & Hrar & Hhvr).
  pose proof (req_size_pos (cnb_size D + 16) ltac:(unfold cnb_size; lia)) as (Hreq1 & Hreq2).
  assert (HnoH : forall h, In h Hp -> ~ (r <= h < r + req_size (cnb_size D + 16))).
  { intros h Hh Hhr.
    pose proof (prh_ledger_heads B ly S Hp W mem (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D) (bi_most D) own0 HLED) as HPmH.
    apply (Permutation_in _ HPmH) in Hh. apply in_map_iff in Hh as ((a & kk) & Ea & Hak). cbn [fst] in Ea.
    pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem (bi_Lam D) (bi_peak D) (bi_cnt D)
      SIZE_MAXZ (bi_ran D) (bi_most D) own0 HLED) (a, kk) Hak) as (Hkk0 & Hab & Hahp & _). cbn [fst snd] in Hkk0, Hab, Hahp.
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & _ & _ & _ & Hpw).
    assert (Hne : fst (a - cf_head, kk + cf_head) <> fst (r, cnb_size D + 16)).
    { cbn [fst]. intros E. apply Hnh. rewrite <- E. exact Hahp. }
    pose proof (cnb3_pairwise_map (fun b => (fst b, req_size (snd b))) _ _ _ Hpw Hab Hinr Hne) as Hdj.
    unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
    pose proof (req_size_pos (kk + @cf_head cp) ltac:(lia)) as (Hq1 & _). lia. }
  destruct (alx_shadow SEGS B ARx LAWS ly S Hp W memF mdF r (cnb_size D + 16) HARF Hinr HnoH) as (Hbs & Hhull).
  unfold cnb_size in *.
  split; [|split; [exact H4096r|]; split; [exact Hceilr|]; split; [exact Hamrr|]; split].
  - unfold bytes_at in *. apply (garr8R_frame SEGS (rdW W mem) (rdW W memF) r (bi_x D) Hby).
    intros x Hx. apply (mbyte_of_aview SEGS). apply (KBLK r (Z.of_nat (length (bi_x D)) + 16) x Hinr ltac:(lia)).
    lia.
  - apply (block_shadow_range _ SHADOW_OFF r (req_size (Z.of_nat (length (bi_x D)) + 16))); [exact Hbs | lia | lia].
  - intros Hl. apply (cnb3_hull_mono _ r (req_size (Z.of_nat (length (bi_x D)) + 16))); [lia | exact Hhull]. }
(* the structs at memF *)
assert (KO : forall c, (c = 32 \/ c = 128 \/ c = 224) -> cnb_open W memF (cnb_F D + c)).
{ intros c Hc. assert (Hc' : 32 <= c <= 224 /\ c mod 8 = 0) by (destruct Hc as [-> | [-> | ->]]; split; lia).
  split.
  - apply (cnb3_ra_of_zero _ (cnb_F D) c HF32 ltac:(lia) ltac:(lia) (proj2 Hc')).
    intros j Hj. exact (HZS c j Hc Hj).
  - intros sx Hsx. apply cnb3_apresent_aview. apply HPR.
    pose proof (cnb3_hull_in (cnb_F D) c sx HF32 ltac:(lia) (proj1 Hc') (proj2 Hc') Hsx) as Hsx'.
    apply Hspres. rewrite HFB. lia. }
assert (KD : forall c, (c = 32 \/ c = 128 \/ c = 224) -> cnb_doc W memF (bi_Lam D) (cnb_F D + c) None).
{ intros c Hc. cbn [cnb_doc]. apply cnb3_zero56. intros i Hi. exact (HZ c i Hc Hi). }
unfold cnb_at_read1.
split.
{ (* cnb_base *)
  split; [exact Hz|]. split; [exact Hfk|]. split; [exact HJF|].
  split.
  { split; [exact Hfrs|]. split; [exact Hnin|]. split.
    - rewrite <- Hflag. rewrite HFB. apply (cnb3_rdword_kept _ _ (cnb_F D + 280) (cnb_F D + 512)); [|lia|lia].
      intros a Ha. apply HK. split; [lia|]. right. split; [lia|].
      unfold kLowShadowBeg, SHADOW_OFF, kHighMemBeg, ESTACK in *. lia.
    - split.
      + intros a Ha. apply HPR. exact (Hfpres a Ha).
      + intros a Ha. apply HPR. exact (Hspres a Ha). }
  split.
  { unfold cnb_saved in *. apply Forall_forall. intros [o r] Hin'.
    pose proof (proj1 (Forall_forall _ _) HSV (o, r) Hin') as Hv. cbn [fst snd] in Hv |- *.
    assert (Ho : 56 <= o <= 152)
      by (cbn in Hin'; repeat destruct Hin' as [Hin'|Hin']; try (injection Hin' as <- _; lia); destruct Hin').
    rewrite <- Hv. apply (cnb3_rdword_kept _ _ (cnb_S1 D) (2 ^ 64)); [exact KHI | lia | lia]. }
  split; [rewrite (cnb3_pres_get regs regsF 3%bv HRP ltac:(cnb3_cs)); exact R3|].
  split; [rewrite (cnb3_pres_get regs regsF 4%bv HRP ltac:(cnb3_cs)); exact R4|].
  intros a Hro Hown Herr. rewrite <- (HROD a Hro Hown Herr). apply KIMG. exact (KRO a Hro). }
split.
{ apply (cnb3_regsat_pres regs regsF _ HR HRP). unfold cnb_core. cbn [app]. cnb3_forall_cs. }
split.
{ unfold cnb_slots in *. apply Forall_forall. intros [o v] Hin'.
  pose proof (proj1 (Forall_forall _ _) HSL (o, v) Hin') as Hv. cbn [fst snd] in Hv |- *.
  assert (Ho : 16 <= o <= 48)
    by (cbn in Hin'; repeat destruct Hin' as [Hin'|Hin']; try (injection Hin' as <- _; lia); destruct Hin').
  rewrite <- Hv. apply (cnb3_rdword_kept _ _ (cnb_S1 D) (2 ^ 64)); [exact KHI | lia | lia]. }
split; [exact HOWN0|].
(* the refused copy dead at a consumer run: a fact of D, carried unchanged *)
split; [exact HDEAD|].
split; [exact EHp|].
(* the progress fact: CB3 makes no run event and keeps S, so cnb_at_init's cnb_prog D (cnb_cevs D r1 r2 r3) S *)
split; [exact HPROG|].
(* cnb_mid, then the hull budget (the cut's last conjunct) *)
(* the hull budget: CB3's stores and the three __asan_memset calls leave the allocator state S as it is *)
split; [|exact HHULL].
unfold cnb_mid.
split; [exact (KC _ HC1)|]. split; [exact (KC _ HC2)|]. split; [exact (KC _ HC3)|].
split; [exact HLEDF|].
split; [lia|]. split; [cbn [Z.of_nat]; rewrite Z.mul_0_l; lia|].
split; [exact HRL|].
split; [change (Z.of_nat (3 - 0)) with 3; exact HBB|].
split; [unfold cnb_d1; exact (KO 32 (or_introl eq_refl))|].
split; [unfold cnb_d2; exact (KO 128 (or_intror (or_introl eq_refl)))|].
split; [unfold cnb_d3; exact (KO 224 (or_intror (or_intror eq_refl)))|].
split; [unfold cnb_d1; exact (KD 32 (or_introl eq_refl))|].
split; [unfold cnb_d2; exact (KD 128 (or_intror (or_introl eq_refl)))|].
split; [unfold cnb_d3; exact (KD 224 (or_intror (or_intror eq_refl)))|].
split; [cbn [cnb_Dof app]; apply Permutation_refl|].
split; [cbn [cnb_Dof app ck_hblks map]; exact HPERM|].
split; [intros a kk Hak; cbn [cnb_Dof app In] in Hak; destruct Hak|].
(* the input *)
destruct HSRC as (HBY & H4096 & Hceil & Hamr & Hra & Hhv).
unfold bytes_at in *. apply (garr8R_frame SEGS (rdW W mem) (rdW W memF) (bi_data D) (bi_x D) HBY).
intros x Hx. apply (mbyte_of_aview SEGS).
destruct (Z_lt_le_dec 0 (cnb_size D)) as [Hpos | Hz0]; [| unfold cnb_size in Hz0; lia].
destruct (HHOME Hpos) as [HKA | (b & m & Hb & Hnb & Hbl & Hbr)].
- destruct HKA as [(b & m & Hbm & Hbl & Hbr) | [(_ & _ & _ & Hro) | HKI]].
  + pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem (bi_Lam D) (bi_peak D) (bi_cnt D)
      SIZE_MAXZ (bi_ran D) (bi_most D) own0 HLED) (b, m) Hbm) as (Hm0 & Hab & _). cbn [fst snd] in Hm0, Hab.
    pose proof (req_size_pos (m + @cf_head cp) ltac:(lia)) as (_ & Hreq).
    apply (KBLK _ _ _ Hab ltac:(lia)). unfold cnb_size in *. lia.
  + apply KIMG. destruct (Hro x ltac:(unfold cnb_size in *; lia)) as (Hro' & _). exact (KRO x Hro').
  + destruct HKI as (_ & _ & Hro). apply KIMG.
    destruct (Hro x ltac:(unfold cnb_size in *; lia)) as (Hro' & _). exact (KRO x Hro').
- unfold cnb_size in *. assert (Hm : 0 <= m) by lia. pose proof (req_size_pos m Hm) as (_ & Hreq).
  apply (KBLK b m x Hb Hm). lia.
Qed.

(* ---- the slots of the three stretches, on the listing of record ---- *)
Ltac cnb3_slot w i := exists w, i; split; [vm_compute; reflexivity | split; [vm_refl_bv | vm_compute; reflexivity]].
Lemma cnb3_slots1 : cnb3_stretch_slots CNB_INIT 32 22%bv.
Proof.
split; [|split; [|split; [|split]]].
- intros j Hj. assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6) by lia.
  destruct Hj' as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
  + cnb3_slot 0x90223 (4%bv : bv 12).
  + cnb3_slot 0x902a3 (5%bv : bv 12).
  + cnb3_slot 0x90323 (6%bv : bv 12).
  + cnb3_slot 0x903a3 (7%bv : bv 12).
  + cnb3_slot 0x90423 (8%bv : bv 12).
  + cnb3_slot 0x904a3 (9%bv : bv 12).
  + cnb3_slot 0x90523 (10%bv : bv 12).
- cnb3_slot 0x3800613 (56%bv : bv 12).
- cnb3_slot 0xb0513 (0%bv : bv 12).
- cnb3_slot 0x593 (0%bv : bv 12).
- vm_compute. reflexivity.
Qed.
Lemma cnb3_slots2 : cnb3_stretch_slots CNB_MR1 128 21%bv.
Proof.
split; [|split; [|split; [|split]]].
- intros j Hj. assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6) by lia.
  destruct Hj' as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
  + cnb3_slot 0x90823 (16%bv : bv 12).
  + cnb3_slot 0x908a3 (17%bv : bv 12).
  + cnb3_slot 0x90923 (18%bv : bv 12).
  + cnb3_slot 0x909a3 (19%bv : bv 12).
  + cnb3_slot 0x90a23 (20%bv : bv 12).
  + cnb3_slot 0x90aa3 (21%bv : bv 12).
  + cnb3_slot 0x90b23 (22%bv : bv 12).
- cnb3_slot 0x3800613 (56%bv : bv 12).
- cnb3_slot 0xa8513 (0%bv : bv 12).
- cnb3_slot 0x593 (0%bv : bv 12).
- vm_compute. reflexivity.
Qed.
Lemma cnb3_slots3 : cnb3_stretch_slots CNB_MR2 224 20%bv.
Proof.
split; [|split; [|split; [|split]]].
- intros j Hj. assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6) by lia.
  destruct Hj' as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
  + cnb3_slot 0x90e23 (28%bv : bv 12).
  + cnb3_slot 0x90ea3 (29%bv : bv 12).
  + cnb3_slot 0x90f23 (30%bv : bv 12).
  + cnb3_slot 0x90fa3 (31%bv : bv 12).
  + cnb3_slot 0x2090023 (32%bv : bv 12).
  + cnb3_slot 0x20900a3 (33%bv : bv 12).
  + cnb3_slot 0x2090123 (34%bv : bv 12).
- cnb3_slot 0x3800613 (56%bv : bv 12).
- cnb3_slot 0xa0513 (0%bv : bv 12).
- cnb3_slot 0x593 (0%bv : bv 12).
- vm_compute. reflexivity.
Qed.

(* ==== THE SEGMENT (the contract's FORWARD form, the internal file lane-102.md :29-30): generic P with its runner laws and the call
   law (the memset text's only carrier of P is its memnorm keep; srr_inv_laws alone does not suffice) ==== *)
Lemma cnb_seg_init : forall P : (word -> option byte) -> Prop,
  srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  cnb_pre (fx := fx) B ARx CTX0 D ->
  cnb_at_init (fx := fx) B ARx D fxk ly S Hp W regs mem md k r1 r2 r3 own0 -> P mem ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc CNB_INIT) regs mem md)
    (fun W' c' => cnb_ex_read1 (fx := fx) B ARx D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k r1 r2 r3 own0 HPRE HAT HPm.
pose proof HAT as HAT'. unfold cnb_at_init in HAT'.
assert (HB : cnb_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k 0) by ro_from HAT'.
assert (HR : cnb_regsat regs (cnb_core D ++ [(23%bv, cnb_size D); (24%bv, bi_data D); (25%bv, r1)]))
  by ro_from HAT'.
clear HAT'.
pose proof HB as (_ & _ & HJ & HF & _ & R3 & R4 & _).
pose proof (cnb3_geo_of D 0%nat ly S Hp W mem md k HPRE HJ HF) as HGEO.
pose proof (cnb3_FA D 0%nat ly S Hp W mem md k HJ) as HFA.
pose proof HF as (_ & _ & _ & _ & Hspres).
assert (HSHP : forall j, 0 <= j < 64 -> apresent (w_H W) mem (shadow_addr (cnb_F D) + j)).
{ intros j Hj. apply Hspres. change (fs_frame_bytes CNB_CID / 8) with 64. lia. }
pose proof (cnb_pre_fpre B ARx CTX0 D HPRE) as HFP.
destruct HFP as ((_ & _ & _ & Hgp0 & Htp0 & _) & _).
assert (G2 : getr regs 2%bv = w64 (cnb_S1 D)) by (apply (cnb3_regsat_get regs _ _ _ HR); unfold cnb_core; cnb3_in).
assert (G18 : getr regs 18%bv = w64 (shadow_addr (cnb_F D)))
  by (apply (cnb3_regsat_get regs _ _ _ HR); unfold cnb_core; cnb3_in).
assert (G20 : getr regs 20%bv = w64 (cnb_F D + 224))
  by (change (cnb_F D + 224) with (cnb_d3 D); apply (cnb3_regsat_get regs _ _ _ HR); unfold cnb_core; cnb3_in).
assert (G21 : getr regs 21%bv = w64 (cnb_F D + 128))
  by (change (cnb_F D + 128) with (cnb_d2 D); apply (cnb3_regsat_get regs _ _ _ HR); unfold cnb_core; cnb3_in).
assert (G22 : getr regs 22%bv = w64 (cnb_F D + 32))
  by (change (cnb_F D + 32) with (cnb_d1 D); apply (cnb3_regsat_get regs _ _ _ HR); unfold cnb_core; cnb3_in).
assert (G3 : getr regs 3%bv = w64 (as_gp B)) by (rewrite R3; exact Hgp0).
assert (G4 : getr regs 4%bv = w64 (as_tp B)) by (rewrite R4; exact Htp0).
(* stretch 1: d1 *)
apply (cnb3_stretch P PLAW PCALL D CNB_INIT 32 22%bv fxk 0%nat ly S Hp W regs mem md k _ cnb3_slots1
  ltac:(unfold CNB_INIT; lia) eq_refl ltac:(unfold CNB_INIT; lia) ltac:(lia) eq_refl eq_refl HGEO HFA HJ HPm HSHP
  G18 G22 G2 G3 G4).
intros regs1 mem1 md1 HJ1 HP1 HRP1 Hk1 Hz1 Hs1 Hp1.
change (CNB_INIT + 44) with CNB_MR1.
(* stretch 2: d2 *)
apply (cnb3_stretch P PLAW PCALL D CNB_MR1 128 21%bv fxk 0%nat ly S Hp W regs1 mem1 md1 k _ cnb3_slots2
  ltac:(unfold CNB_MR1; lia) eq_refl ltac:(unfold CNB_MR1; lia) ltac:(lia) eq_refl eq_refl HGEO HFA HJ1 HP1
  ltac:(intros j Hj; exact (Hp1 _ (HSHP j Hj)))
  ltac:(rewrite (cnb3_pres_get regs regs1 18%bv HRP1 ltac:(cnb3_cs)); exact G18)
  ltac:(rewrite (cnb3_pres_get regs regs1 21%bv HRP1 ltac:(cnb3_cs)); exact G21)
  ltac:(rewrite (cnb3_pres_get regs regs1 2%bv HRP1 ltac:(cnb3_cs)); exact G2)
  ltac:(rewrite (cnb3_pres_get regs regs1 3%bv HRP1 ltac:(cnb3_cs)); exact G3)
  ltac:(rewrite (cnb3_pres_get regs regs1 4%bv HRP1 ltac:(cnb3_cs)); exact G4)).
intros regs2 mem2 md2 HJ2 HP2 HRP2 Hk2 Hz2 Hs2 Hp2.
change (CNB_MR1 + 44) with CNB_MR2.
assert (HRP12 : aregs_preserved regs regs2) by (intros r Hr; rewrite (HRP2 r Hr); exact (HRP1 r Hr)).
(* stretch 3: d3 *)
apply (cnb3_stretch P PLAW PCALL D CNB_MR2 224 20%bv fxk 0%nat ly S Hp W regs2 mem2 md2 k _ cnb3_slots3
  ltac:(unfold CNB_MR2; lia) eq_refl ltac:(unfold CNB_MR2; lia) ltac:(lia) eq_refl eq_refl HGEO HFA HJ2 HP2
  ltac:(intros j Hj; exact (Hp2 _ (Hp1 _ (HSHP j Hj))))
  ltac:(rewrite (cnb3_pres_get regs regs2 18%bv HRP12 ltac:(cnb3_cs)); exact G18)
  ltac:(rewrite (cnb3_pres_get regs regs2 20%bv HRP12 ltac:(cnb3_cs)); exact G20)
  ltac:(rewrite (cnb3_pres_get regs regs2 2%bv HRP12 ltac:(cnb3_cs)); exact G2)
  ltac:(rewrite (cnb3_pres_get regs regs2 3%bv HRP12 ltac:(cnb3_cs)); exact G3)
  ltac:(rewrite (cnb3_pres_get regs regs2 4%bv HRP12 ltac:(cnb3_cs)); exact G4)).
intros regs3 mem3 md3 HJ3 HP3 HRP3 Hk3 Hz3 Hs3 Hp3.
assert (HRP13 : aregs_preserved regs regs3) by (intros r Hr; rewrite (HRP3 r Hr); exact (HRP12 r Hr)).
apply SRr_ret. split; [|exact HP3].
exists fxk, ly, S, Hp, regs3, mem3, md3, k, r1, r2, r3, own0. split; [reflexivity|].
apply (cnb3_final D fxk ly S Hp W regs mem md k r1 r2 r3 own0 regs3 mem3 md3 HPRE HAT HJ3 HRP13).
- intros a Ha. pose proof (proj1 Ha) as Ha64.
  rewrite (Hk3 a Ha64 (cnb3_safe_notX D 224 a HGEO ltac:(lia) Ha)),
    (Hk2 a Ha64 (cnb3_safe_notX D 128 a HGEO ltac:(lia) Ha)).
  exact (Hk1 a Ha64 (cnb3_safe_notX D 32 a HGEO ltac:(lia) Ha)).
- intros c i Hc Hi. destruct Hc as [-> | [-> | ->]].
  + destruct (cnb3_cross D 32 224 (cnb_F D + 32 + i) HGEO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (Ha & N3).
    destruct (cnb3_cross D 32 128 (cnb_F D + 32 + i) HGEO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & N2).
    rewrite (Hk3 _ Ha N3), (Hk2 _ Ha N2). exact (Hz1 i Hi).
  + destruct (cnb3_cross D 128 224 (cnb_F D + 128 + i) HGEO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (Ha & N3).
    rewrite (Hk3 _ Ha N3). exact (Hz2 i Hi).
  + exact (Hz3 i Hi).
- intros c j Hc Hj. destruct Hc as [-> | [-> | ->]].
  + destruct (cnb3_cross D 32 224 (shadow_addr (cnb_F D) + 32 / 8 + j) HGEO ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(right; lia)) as (Ha & N3).
    destruct (cnb3_cross D 32 128 (shadow_addr (cnb_F D) + 32 / 8 + j) HGEO ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(right; lia)) as (_ & N2).
    rewrite (Hk3 _ Ha N3), (Hk2 _ Ha N2). exact (Hs1 j Hj).
  + destruct (cnb3_cross D 128 224 (shadow_addr (cnb_F D) + 128 / 8 + j) HGEO ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(right; lia)) as (Ha & N3).
    rewrite (Hk3 _ Ha N3). exact (Hs2 j Hj).
  + exact (Hs3 j Hj).
- intros a Ha. exact (Hp3 a (Hp2 a (Hp1 a Ha))).
Qed.

End cb3.
