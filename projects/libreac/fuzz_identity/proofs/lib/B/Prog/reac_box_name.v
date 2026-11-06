(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-148
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:388-392 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFfi.v:262-264 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC4t.v:438 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_identity_ingest.v, with its module paths and module names changed; 131 of its 168 lines of code are new or changed and 3028 lines of the source are left out. *)
(* reac_box_name (fuzz_identity.asan-ubsan 0x82d74, 0x85c bytes, listing offset AF_reac_box_name = 0x2600): its
   ASan+UBSan-build contract treac_box_name_spec, in the afn_pre / apost_base form (CONVENTIONS.md section 3;
   cgif lib/A/AChd.v:82-105, lib/YC7x.v:72-101): the call writes only its own stack window, its own class-3
   side-stack frame and the three heap blocks name / token / display (buf_of in fuzz_identity.c:421).
   It reads the caller's said_name (in the caller's side-stack frame), the image's stem table and strings,
   and the two stack arguments display / display_len.
   The B twin of the A contract lib/A/Prog/reac_box_name.v:115 treac_box_name_spec (A walk:
   reac_box_name_walk.v:62): the same names, argument order, premises and post. What image B changes:
   - the B listing layer (PAImg identb_listing, AF_reac_box_name = 0x2600) and the B frame helpers;
   - the stack REAC_BOX_NAME_STK: frame 320 (0x82d74 addi sp,sp,-320) and the 32-byte realignment;
   - the image objects of the B listing: the switch table is object 22 (0x9b4e0), "REAC" 19 (0x211c0),
     " (" 23 (0x211e0), " in / " 24 (0x21200), " out)" 25 (0x21220); the stems at 0x21160 / 0x21180 / 0x211a0;
   - B calls sb_ch (8 calls) out of line.
   The walk pb_reac_box_name chains the segment lemmas of lib/B/Prog/reac_box_name_seg_*.v. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase IdentRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBProgSig.
(* The side-stack frame helpers of image B. Only the walk uses them. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBFrame YC85.
(* The wrapper and runtime contracts the walk takes: the strlen wrapper
   and the shadow-fill entries (
   lib/B/Rt/SetShadowDef.v). Only the walk uses them. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef SetShadowDef.
(* The callees' contracts: sb_ch (proved) and sb_dec. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import sb_ch sb_dec.
(* The predicates the contract states (rbn_fp, rbn_cstr, rbn_glob, rbn_fixed, rbn_imgstr, rbn_img, rbn_said,
   rbn_bufs, rbn_postQ) and the walk's cut-point states: lib/B/Prog/reac_box_name_inv.v. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import reac_box_name_sbm reac_box_name_inv.
(* The walk's segments. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
reac_box_name_seg_entry reac_box_name_seg_mid reac_box_name_seg_cp reac_box_name_seg_tok reac_box_name_seg_lit
reac_box_name_seg_rel.
(* The plain model of reac_box_name (released, origin/ossv/recipes c8557374ad2e), used as it is. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Definition A_reac_box_name : Z := BASE + AF_reac_box_name.
(* The stack the call needs, measured from the listing: the 320-byte frame (0x82d74 addi sp,sp,-320; probe
   0x82d78 at sp0-320; ra, s0..s11 at sp0-8 .. sp0-104), the 32-byte alignment of sp (0x82db4 andi sp,sp,-32:
   sp0 - 320 is 16-aligned, so up to 16 more bytes), so every call is made with sp = s1 >= sp0 - 336. Below s1
   the deepest callee windows: the bcmp wrapper (abcmp_realizes: 2 * ESTACK, call at 0x83104) and the strlen
   wrapper (astrlen_realizes, lib/B/Rt/StrlenDef.v: 2 * ESTACK, call at 0x830dc); sb_dec needs
   SB_DEC_STK = 160 + ESTACK and sb_ch SB_CH_STK = 16 + ESTACK, both below 2 * ESTACK; the frame allocation,
   memset, memcpy and set_shadow need ESTACK.
   The real-stack fallback (0x82e20..0x82e38: frame at s1-288, probes every 4096 bytes) is not reached. *)
Definition REAC_BOX_NAME_STK : Z := 336 + 2 * ESTACK.
(* Allocator events and live heap bytes of one call: none (no malloc/free; the class-3 side-stack frame
   allocation counts no event; sb_dec's EV_SB_DEC = 0 and sb_ch's EV_SB_CH = 0). Both must fit under the
   shared EV_MAX / LIVE_MAX. *)
Definition EV_REAC_BOX_NAME : Z := 0.
Definition LIVE_REAC_BOX_NAME : Z := 0.
Section h.
Variable B : asyms.
(* The registered globals of the image with their sizes (IdentRo.v globs_marked; the composition gives the
   list and its start-up certificate). *)
Variable G : list (Z * Z).
(* The post: back at ra, the journal with the three buffers as write tokens, callee-saved registers kept,
   and rbn_postQ (reac_box_name_inv.v): the world and the heap blocks unchanged, and the plain model's result
   (reac_box_name_c.reac_box_name_contract): on acceptance a0 = 0 and the name / token / display strings with
   their NUL, the rest of the buffers kept; on refusal a0 = -1 and the buffers kept. *)
Definition treac_box_name_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (f : Z) (sd : list Z) (i o name name_len token token_len display display_len : Z)
  : world SEGS -> config -> Prop :=
  apost_base SEGS B REAC_BOX_NAME_STK (rbn_fp name name_len token token_len display display_len)
    regs ly S W mem md EV_REAC_BOX_NAME
    (rbn_postQ B ly S W mem f sd i o name name_len token token_len display display_len).
(* The pre-condition. a0 = f (enum), a1 = said_name, a2 = in_ch, a3 = out_ch, a4 = name, a5 = name_len,
   a6 = token, a7 = token_len; display and display_len are the stack arguments at sp0 and sp0 + 8
   (display_len read at 0x82e14 before the argument checks, display at 0x82f28 among them). *)
Definition treac_box_name_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch
         (f said i o name name_len token token_len display display_len : Z) (sd : list Z),
  afn_pre SEGS B REAC_BOX_NAME_STK ly S W regs mem md ch ->
  arodata_okP SEGS (@pa_relro_lo _ identb_listing PI) (@pa_relro_hi _ identb_listing PI) B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 f -> - 2 ^ 31 <= f < 2 ^ 31 ->
  getr regs 11 = w64 said -> 0 <= said < 2 ^ 64 ->
  getr regs 12 = w64 i -> - 2 ^ 31 <= i < 2 ^ 31 ->
  getr regs 13 = w64 o -> - 2 ^ 31 <= o < 2 ^ 31 ->
  getr regs 14 = w64 name -> 0 <= name < 2 ^ 64 ->
  getr regs 15 = w64 name_len -> 0 <= name_len < 2 ^ 64 ->
  getr regs 16 = w64 token -> 0 <= token < 2 ^ 64 ->
  getr regs 17 = w64 token_len -> 0 <= token_len < 2 ^ 64 ->
  (* the 9th and 10th arguments, pushed by the caller below its sp: the two words of the caller's window at
     sp0 and sp0 + 8, present, holding display and display_len *)
  (forall a, spZ regs <= a < spZ regs + 16 -> apresent (w_H W) mem a) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs) 8 display -> 0 <= display < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + 8) 8 display_len -> 0 <= display_len < 2 ^ 64 ->
  rbn_img B G W mem ->
  (reac_box_name_c.bn_args_ok name name_len token token_len display display_len i o = true ->
     rbn_said ly S W mem said sd /\ rbn_bufs B ly S name name_len token token_len display display_len) ->
  (* room for the class-3 frame and, below it, sb_dec's class-0 frame (tsb_dec_spec asks <= 8) *)
  Z.of_nat (length (frames S)) <= 7 ->
  st_nev S + EV_REAC_BOX_NAME <= EV_MAX -> blocks_bytes S + LIVE_REAC_BOX_NAME <= LIVE_MAX ->
  SRr SEGS W (cfg_at SEGS A_reac_box_name regs mem md)
    (treac_box_name_post regs ly S W mem md f sd i o name name_len token token_len display display_len).
(* The walk's Section hypotheses (CONVENTIONS.md section 4; cgif lib/A/AChf.v:40-76). pb_reac_box_name :
   treac_box_name_spec is proved under them (below). *)
Section walk.
Context {RO : ro_below_ofl SEGS (@pa_relro_lo _ identb_listing PI) (@pa_relro_hi _ identb_listing PI)}.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM3 : astack_malloc_realizes SEGS B 3.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* identity B's PALibF (IdentBFrame.v): as_got_uar B = VAL (A_OBJ 0) and
   SIGMA IB___asan_stack_malloc_c = pc_stack_malloc (as_code B) c for c = 0, 3, 4. *)
Hypothesis TLF : PALibF B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IB___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IB___asan_memcpy).
(* the bcmp wrapper (cgif ACfz.v:69, AChv.v:117, AE2s.v:710 bcmp_icpt_contract) *)
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
(* the strlen wrapper, lib/B/Rt/StrlenDef.v: its read-only premise is aro_unowned
   (lib/B/Rt/WrapRo.v), which aro_unowned_of_arodata gives from the journal-kept arodata_okP. *)
Hypothesis ASTRLEN : astrlen_realizes SEGS B (SIGMA IB___interceptor_trampoline_strlen).
(* the shadow fill of the frame release (0x834c4), lib/B/Rt/SetShadowDef.v; 245 = 0xf5. *)
Hypothesis ASSF5 : aset_shadow_realizes SEGS B (SIGMA IB___asan_set_shadow_f5) 245.
(* the image reads (IdentRo.v): the registered globals' shadow and the image's shadow window *)
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
(* the program functions the listing calls, at BASE + AF_<f> (IdentBProgSig.v) *)
Hypothesis PSIG : identb_prog_sig_ok.
(* The callees, by their exact types at BASE + AF_sb_ch and BASE + AF_sb_dec. *)
Hypothesis HSC : tsb_ch_spec B.
Hypothesis HSB : tsb_dec_spec B.
(* The walk: the twelve segment lemmas of lib/B/Prog/reac_box_name_seg_{entry,mid,cp,tok,lit,rel}.v chained at the
   cut points of reac_box_name_inv.v (entry -> C1 | R, C1 -> C2, the stem copy C2 -> C3, C3 -> C4 | C5, the w4 copy
   C4 -> C5, C5 -> C6, the token loop C6 -> C7, C7 -> C8, the name copy C8 -> C9, C9 -> C10, C10 -> R, R -> post).
   Each segment lemma is closed over the Section hypotheses it uses; rbnw_spec feeds it this Section's. *)
Ltac rbnw_spec H := repeat match type of H with ?A -> _ => specialize (H ltac:(assumption)) end.
Theorem pb_reac_box_name : treac_box_name_spec.
Proof.
unfold treac_box_name_spec.
pose proof (rbn_seg_entry B G) as ENTRY. rbnw_spec ENTRY.
pose proof (rbn_seg_c1_c2 B G) as C12. rbnw_spec C12.
pose proof (rbn_cp_stem B G) as CPS. rbnw_spec CPS.
pose proof (rbn_seg_c3_c45 B G) as C345. rbnw_spec C345.
pose proof (rbn_cp_w4 B G) as CPW. rbnw_spec CPW.
pose proof (rbn_seg_c5_c6 B G) as S56. rbnw_spec S56.
pose proof (rbn_tok_loop B G) as TOKL. rbnw_spec TOKL.
pose proof (rbn_seg_c7_c8 B G) as S78. rbnw_spec S78.
pose proof (rbn_cp_dp B G) as CPD. rbnw_spec CPD.
pose proof (rbn_seg_c9_c10 B G) as S910. rbnw_spec S910.
pose proof (rbn_seg_c10_r B G) as C10R. rbnw_spec C10R.
pose proof (rbn_seg_rel B G) as REL. rbnw_spec REL.
intros ly S W regs mem md ch f said i o name name_len token token_len display display_len sd
  HPRE HRO H10 Hf H11 Hsaid H12 Hi H13 Ho H14 Hname H15 Hnl H16 Htok H17 Htl HSTK Vd Hd Vdl Hdl HIMG HARGS Hfr Hev Hlive.
set (c := mkRbx ly S W regs mem md ch f said i o name name_len token token_len display display_len sd 0).
assert (HP : rbn_pre B G c).
{ unfold rbn_pre, x_sp0, x_mem_at. cbn [x_ly x_S x_W x_regs x_mem x_md x_ch x_f x_said x_i x_o x_name x_name_len
    x_token x_token_len x_display x_display_len x_sd c].
  unfold REAC_BOX_NAME_STK, EV_REAC_BOX_NAME, LIVE_REAC_BOX_NAME in *. rewrite Z.add_0_r in Hev, Hlive.
  repeat (split; [assumption|]); assumption. }
unfold treac_box_name_post.
eapply SRr_bind; [ exact (ENTRY c HP) | ].
intros W2 c2 _ (-> & fpos & st & lyc & Sc & regs2 & mem2 & md2 & [(-> & HC1) | (-> & HR)]);
  [ | exact (REL _ _ _ _ _ _ HR) ].
set (c1 := x_setpos c fpos) in *.
(* C5 -> the post, used by both outcomes of the strlen / bcmp test *)
assert (TAIL : forall lyc5 Sc5 mem5 md5 regs5, rbn_C5 B G c1 lyc5 Sc5 mem5 md5 regs5 ->
  SRr SEGS (x_W c1) (mkCfg (mkst regs5 (Z_to_bv 64 (BASE + AF_reac_box_name + 0x3f8)) mem5 (seg_rom SEGS)) md5)
    (apost_base SEGS B (336 + 2 * ESTACK) (x_FP c1) (x_regs c1) (x_ly c1) (x_S c1) (x_W c1) (x_mem c1) (x_md c1) 0
       (rbn_postQ B (x_ly c1) (x_S c1) (x_W c1) (x_mem c1) (x_f c1) (x_sd c1) (x_i c1) (x_o c1) (x_name c1)
          (x_name_len c1) (x_token c1) (x_token_len c1) (x_display c1) (x_display_len c1)))).
{ intros lyc5 Sc5 mem5 md5 regs5 HC5.
  eapply SRr_bind; [ exact (S56 _ _ _ _ _ _ HC5) | ].
  intros W6 c6 _ (-> & lyc6 & Sc6 & regs6 & mem6 & md6 & -> & HC6).
  eapply SRr_bind; [ exact (TOKL (length (x_nmc c1)) c1 0 _ _ _ _ _ (eq_sym (Z.sub_0_r _)) HC6) | ].
  intros W7 c7 _ (-> & lyc7 & Sc7 & regs7 & mem7 & md7 & -> & HC7).
  eapply SRr_bind; [ exact (S78 _ _ _ _ _ _ HC7) | ].
  intros W8 c8 _ (-> & lyc8 & Sc8 & regs8 & mem8 & md8 & -> & HC8).
  eapply SRr_bind; [ exact (CPD (length (x_nmc c1)) c1 0 _ _ _ _ _ (eq_sym (Z.sub_0_r _)) HC8) | ].
  intros W9 c9 _ (-> & lyc9 & Sc9 & regs9 & mem9 & md9 & -> & HC9).
  eapply SRr_bind; [ exact (S910 _ _ _ _ _ _ HC9) | ].
  intros W10 c10 _ (-> & lyc10 & Sc10 & regs10 & mem10 & md10 & -> & HC10).
  eapply SRr_bind; [ exact (C10R _ _ _ _ _ _ HC10) | ].
  intros W11 c11 _ (-> & lyc11 & Sc11 & regs11 & mem11 & md11 & -> & HR).
  exact (REL _ _ _ _ _ _ HR). }
eapply SRr_bind; [ exact (C12 _ _ _ _ _ _ _ HC1) | ].
intros W3 c3 _ (-> & lyc3 & Sc3 & regs3 & mem3 & md3 & -> & HC2).
eapply SRr_bind; [ exact (CPS (length (x_stem c1)) c1 _ 0 _ _ _ _ _ (eq_sym (Z.sub_0_r _)) HC2) | ].
intros W4 c4 _ (-> & lyc4 & Sc4 & regs4 & mem4 & md4 & -> & HC3).
eapply SRr_bind; [ exact (C345 _ _ _ _ _ _ _ HC3) | ].
intros W5 c5 _ (-> & lyc5 & Sc5 & regs5 & mem5 & md5 & [(-> & HC4) | (-> & HC5)]); [ | exact (TAIL _ _ _ _ _ HC5) ].
eapply SRr_bind; [ exact (CPW 4%nat c1 0 _ _ _ _ _ eq_refl HC4) | ].
intros W6 c6 _ (-> & lyc6 & Sc6 & regs6 & mem6 & md6 & -> & HC5).
exact (TAIL _ _ _ _ _ HC5).
Qed.
End walk.
End h.
End f.
End d.
(* The predicates that moved to reac_box_name_inv.v, re-exported under their earlier names (files on the
   integration tip cite them as reac_box_name.<name>, e.g. lib/B/Prog/LLVMFuzzerTestOneInput.v:261-274). *)
Notation rbn_fp := reac_box_name_inv.rbn_fp (only parsing).
Notation rbn_cstr := reac_box_name_inv.rbn_cstr (only parsing).
Notation rbn_glob := reac_box_name_inv.rbn_glob (only parsing).
Notation rbn_fixed := reac_box_name_inv.rbn_fixed (only parsing).
Notation rbn_imgstr := reac_box_name_inv.rbn_imgstr (only parsing).
Notation rbn_img := reac_box_name_inv.rbn_img (only parsing).
Notation rbn_said := reac_box_name_inv.rbn_said (only parsing).
Notation rbn_bufs := reac_box_name_inv.rbn_bufs (only parsing).
