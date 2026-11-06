(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the tail of pcap_source_open (fuzz_pcap.asan-ubsan 0x811e0, listing offset
   AF_pcap_source_open = 0xa58, 246 instructions) on libreac v1.9.0's ASan+UBSan build: lib/A's PcapSourceOpenB.v, the
   walk from the two semantic cuts of lib/B/Prog/PcapSourceOpenPh.v to the return. op_from_null and op_from_read prove
   `op_from op_gi_null` and `op_from op_gi_read`, i.e. lib/A's image-generic post tpcap_source_open_post (with
   topen_kept, lib/A/Prog/PcapSourceOpenDefs.v) at this image (SEGS = pa_segs, the relro window pa_relro_lo /
   pa_relro_hi of the lib/B PAImg instance PI); PcapSourceOpen.v (the head) composes them. At ossv/recipes 25e3d17bdb50 (2026-10-29), this image had no released
   proof (rule 24, a Theorem Labs lane, 22:35Z); the released v1.8 UBSan proof lib/U/Prog/pcap_source_open.v is the guard
   template only.

   The paths, at this image's pcs:
   - the empty input (cut 0x813f8, f = NULL): a0 := -1, `j 0x81474`, the epilogue without the buffer re-poison;
   - the short read (cut 0x8138c, kr <> 24): `bne a0,s9` to 0x81400, the shadow test of ps (0x81400 `lbu`, 0x81404
     `bnez`), f = ps->f (0x81408), the fclose wrapper's call (0x8140c), the second shadow test (0x81410, 0x81414
     `beqz` to 0x8145c), ps->f := NULL (0x8145c), a0 := -1, the epilogue from 0x81464 (op_fclose);
   - kr = 24: the UBSan guard G6 (below), the magic of the four header bytes F + 32 .. F + 35 (0x81398..0x813c4, the
     top byte through `slliw`, magic_U), then 0xd4c3b2a1 (0x813c8 `beq` to 0x81420: ps->swapped := 1, a0 := 0,
     `j 0x81464`), 0xa1b2c3d4 (0x813d4 `bne` falls to 0x813d8: ps->swapped := 0, a0 := 0, `j 0x81464`), or the bad
     magic (0x81444: as the short read, fclose at 0x81450);
   - the epilogue (op_epi): the buffer out of scope (0x81464..0x81470, 3 shadow bytes 0xf8), the retired magic
     0x45e0360e at F (0x8147c); 0x81480 `beqz s2` NOT taken (s2 = F >= 4096, atom 18's fact), so the machine-frame
     arm 0x814d4..0x81500 is dead; F's 16 shadow bytes 0xf5 (0x81484..0x814c4); the flag through `ld a1,0x78(s2)` and
     `sb zero,0(a1)` (0x814c8, 0x814cc), which gives the frame back (lib/B/Prog/PcapFrame.v aj_flag_store_pi:
     astack_free_law, frame_flag_lawP); the restores and `ret` (0x81504..0x81538).
   The two guards on ps (G5, 0x812f8 and 0x81300 / 0x81304) are before the cuts, in the head.

   THE GUARD G6. 0x81390 `addi a0,zero,-3`, 0x81394 `bgeu s4,a0` branches to the `unimp` at 0x8153c when the header
   buffer s4 = F + 32 lies within 3 bytes of 2^64. The symbolic run decides it, NOT taken: decide_cond2
   (Reusable/YP0e.v:932) maps BC_GEU to the negation of decide_ltu2 (:922), and decide_ltu (Reusable/YP0m.v:673) finds
   atom 20 (s4) below the literal 2^64 - 3 from its range fact [4128, 0x7fffff800020] (rd_facts), which rd_entry
   proves from frames_bounds on the class-1 frame (F + 128 <= alloc_ceiling <= 0x7fffff800000). Templates: the released
   UBSan proof of the v1.8 image, proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v on origin/ossv/recipes
   c8557374ad2e, open_mid :286 (premise bv_unsigned sp0 < 2 ^ 63 at :291, frame bounds :295-299), which decides the
   guard at :410-412; and the earlier walk of this image, on a working branch
   (a8ccd33b1a7) pcap_source_open_tl.v (sha256 4aaa5af08467; internal record) pso_rdchk :36-67 (premise bv_unsigned s4 < 2 ^ 64 - 3 at :44,
   `step; step; if_false` at :65).

   THE REPORT PATHS are proved unreachable; no run steps into one. Every shadow test of ps in this stretch
   (0x81400 / 0x81404 and 0x81410 / 0x81414 on the short read, 0x81444 / 0x81448 and 0x81454 / 0x81458 on the bad
   magic, 0x813e4 / 0x813e8 and 0x8142c / 0x81430 on ps + 8 before the slow checks 0x81570 / 0x81584) is decided by
   the shadow entry of ps (rd_SH: ps's 24 bytes addressable; shent_rd_ok from op_pre's range_addressable, kept to the
   cut by op_mid's topen_kept and across fclose by its journal, shok_transfer), so the token run reads a 0 shadow byte
   and takes the non-report successor: the report calls 0x8141c, 0x81580, 0x81594 and 0x815a0..0x815b4 are never
   reached.

   The callees are Section hypotheses of their exact statement types: the fclose wrapper AFCLOSE, of
   lib/A/Stdio/PFclose.v's image-generic afclose_source_spec (= afclose_source_spec_stk PFCLOSE_STK) at this image,
   bound as lib/B/Prog/PcapSourceClose.v binds it (its data-buffer premise from op_pre's input block); the file meter
   FM (lib/A/Stdio/PSourceMeter.v asrc_file_meter); the frame give-back laws astack_free_law (Reusable/YG0d.v:301) and
   frame_flag_lawP (Reusable/YCbq.v:797) with model_laws; the meter laws (Reusable/YC5d.v ameter_laws,
   ameter_fs_laws); ASIL (lib/A/Stdio/PSourceMeta.v asource_img_laws). The stream predicates' frame lemmas are copied
   from lib/B/Prog/PcapSourceClose.v (not required). getr / mkst / seg_rom come from YK11; nothing from lib/Lib is
   imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpenB.v, with its module paths, module names and numbers changed; 660 of its 725 lines of code are new or changed and 1681 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_entry.v, with its module names and numbers changed; 799 of its 873 lines of code are new or changed and 651 lines of the source are left out. *)
(* mark_quietly (fuzz_link.c:153-164) on image A (fuzz_link.asan 0x883d4, 124 bytes; listing
   (internal path) (internal record, sha256 83bb83545bf3)), the opening arm (g_sink = 0):
   the walk of mark_quietly_c.v `mark_quietly_acontract_open` (aleaf_alloc_fx_sk, K = 24608, EV = 1, LIVE = AMF_BLOCK),
   at any MO and CTX, LedPre := True, LedPost := the depot's wild count does not grow.

   The walk on link's program tables (LinkWalk.v paj_run_x over the caller's journal ajournal_gx); every later state
   is tracked by mark_quietlyDefs.v `mqo_rel` (mark_quietlyOrel.v):
   - run 1, +0x00 .. +0x3c: the frame, s0 / s1 / s2, g_sink = 0 (a literal chunk, so `bnez` falls through), the
     arguments g_said / 4096 / "w";
   - fmemopen (0x430a8): mark_quietlyFo.v aj_gx_fmemopen_at over LinkFoSpec.v afmemopen_w_spec at CTX [[]] (s0 is the
     name pointer, below the allocator's ceiling); the fresh FILE block res, the depot's wild count not growing;
   - run 2, +0x40 .. +0x48: g_sink := res through s2 (region on the auipc atom A_HI 68), `beqz` not taken (res >= 4096
     as a range fact on a0's atom);
   - reac_served_say_to (0x89504, an aleaf): g_say := res;
   - run 3, +0x4c .. +0x50: a0 := g_sink; rewind (0x430d4): mark_quietlyRw.v aj_gx_rewind_at, the FILE's fields from
     fmemopen's post kept since;
   - run 4, +0x54 .. +0x70: the epilogue and the tail jump to reac_served_mark (0x895a8): its contract at the jump
     state, composed by LinkWalkMkTail.v apostF_tail_ly (the fresh block is no clause of the entry's kept clause);
     its Pre / read set / the caller's PostA from mark_quietlyOrsm.v.

   Section hypotheses: LAWS (AR_laws), TL (PALib), LV (LinkVals), TB (PcapSyms; instance AD2l.PcapB_syms), HSEGS
   (pa_segs = tfibsegs), MT_OK / MT_LE (the meter: `fun _ _ => I` / `fun _ _ _ => I` at YCbp.ameter_triv), FM
   (fmemopen's contract; discharge LinkFoOk.v afmemopen_w_ok_pcapb link_afmemopen_ctx), HL (amf_head_law SK link_amf;
   discharge AMemFile.v link_amf_head_law), UMR0 / UMR1 (fmemopen's two universe rows; discharge
   mark_quietlyOrel.v mqo_univ0_pcapb / mqo_univ1_pcapb), RST (reac_served_say_to_acontract), RW (the rewind
   wrapper, LinkMfDefs.v), RSM (reac_served_mark_acontract).

   Proves function mark_quietly (image A, the asan build), opening arm. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkFoSpec LinkFoInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkErrno LinkWalkErrnoInst LinkWalkSide LinkWalkMkTail LinkWalkMkCr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import mark_quietlyRw mark_quietlyFo.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_say_to_c reac_served_mark_c mark_quietly_c mark_quietlyDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import mark_quietlyAgain.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import mark_quietlyOrel mark_quietlyOrsm.
From OSSVerify.reac_pw.fuzz_link.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the entry state: the 32-byte frame and g_sink (0) at its object A_OBJ 29 ---------------------------- *)
Definition mqo_gs_obj : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 29)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 0))].
Definition mqo_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (A_OBJ 29, mkAF LA_G_SINK LA_G_SINK 0)] [] [].
Definition mqo_ss : sstate := mkSS AF_mark_quietly sr_atoms [stack_region 32; mqo_gs_obj] None mqo_facts.
(* g_sink through s2 (the auipc value A_HI 68, offset -0x52c), with its write window: the store at +0x40 *)
Definition mqo_gs_w : YP09.region :=
  YP09.mkRegion (Some (A_HI 68)) (-0x52c) (-0x524) (-0x52c) (-0x524) [YP09.mkChunk (-0x52c) (CVal 8 (SLit 0))].

(* g_sink is an image byte off the runtime's owned statics (row (0x62fec8, 0x18) starts after it) *)
Lemma mqo_gsink_in_img : forall a, LA_G_SINK <= a < LA_G_SINK + 8 -> YG0d.in_img tfibsegs a.
Proof.
  intros a Ha. unfold YG0d.in_img. unfold LA_G_SINK in Ha.
  assert (E : tfibsegs = [Asan.Asan_segment_000; Asan.Asan_segment_001;
                          Asan.Asan_segment_002; Asan.Asan_segment_003]) by reflexivity.
  exists Asan.Asan_segment_003. split; [rewrite E; cbn; tauto | cbn; lia].
Qed.
Lemma mqo_gsay_in_img : forall a, LA_G_SAY <= a < LA_G_SAY + 8 -> YG0d.in_img tfibsegs a.
Proof.
  intros a Ha. unfold YG0d.in_img. unfold LA_G_SAY in Ha.
  assert (E : tfibsegs = [Asan.Asan_segment_000; Asan.Asan_segment_001;
                          Asan.Asan_segment_002; Asan.Asan_segment_003]) by reflexivity.
  exists Asan.Asan_segment_003. split; [rewrite E; cbn; tauto | cbn; lia].
Qed.
Lemma mqo_ofl_in_img : forall a, LA_OFL_HEAD <= a < LA_OFL_HEAD + 8 -> YG0d.in_img tfibsegs a.
Proof.
  intros a Ha. unfold YG0d.in_img. unfold LA_OFL_HEAD in Ha.
  assert (E : tfibsegs = [Asan.Asan_segment_000; Asan.Asan_segment_001;
                          Asan.Asan_segment_002; Asan.Asan_segment_003]) by reflexivity.
  exists Asan.Asan_segment_003. split; [rewrite E; cbn; tauto | cbn; lia].
Qed.
Lemma mqo_ofl_not_static : forall a, LA_OFL_HEAD <= a < LA_OFL_HEAD + 8 -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros a Ha O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & X).
  unfold in_zr in X. unfold LA_OFL_HEAD in Ha. cbn [In] in Hr.
  repeat match type of Hr with
  | _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X; lia|]
  | False => destruct Hr
  end.
Qed.
Lemma mqo_gsink_not_static : forall a, LA_G_SINK <= a < LA_G_SINK + 8 -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros a Ha O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & X).
  unfold in_zr in X. unfold LA_G_SINK in Ha. cbn [In] in Hr.
  repeat match type of Hr with
  | _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X; lia|]
  | False => destruct Hr
  end.
Qed.

Ltac zrng := try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32);
  try change (Z.of_N 8) with 8; try change (Z.of_N 4) with 4; lia.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.

Lemma mqo_vals : VAL (A_OBJ 29) = LA_G_SINK /\ VAL (A_HI 68) = 0x6303ec /\ BASE = 0x821cc /\
  VAL (A_OBJ 30) = LA_G_SAID /\ VAL (A_OBJ 31) = LA_MODE_W /\
  pa_sigma LS___interceptor_trampoline_fmemopen = LA_W_FMEMOPEN /\
  pa_sigma LS_reac_served_say_to = REAC_SERVED_SAY_TO_A /\
  pa_sigma LS___interceptor_trampoline_rewind = LA_W_REWIND /\ pa_sigma LS_reac_served_mark = REAC_SERVED_MARK_A.
Proof.
  split; [rewrite (lv_obj LV 29) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_hi LV 68) by (unfold link_nhi; lia); reflexivity|].
  split; [exact (lv_text LV)|].
  split; [rewrite (lv_obj LV 30) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 31) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_sigma LV); reflexivity|].
  split; [rewrite (lv_sigma LV); reflexivity|].
  split; rewrite (lv_sigma LV); reflexivity.
Qed.

(* THE ENTRY STATE *)
Lemma mqo_entry : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 32 -> spZ regs <= sp0 ->
  au64_at SEGS (rdW W memc) LA_G_SINK 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) mqo_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_mark_quietly)) memc (seg_rom SEGS))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ H16 Hwlo Hwhi Hgs.
destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct mqo_vals as (V29 & _).
set (E := Eimg (Ereg regs [])).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Eg : ew E (A_OBJ 29) = Z_to_bv 64 LA_G_SINK)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V29; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VBv : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx. unfold mqo_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, mqo_gs_obj.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + fold E. rewrite (VBv _ _ Eg) by (unfold LA_G_SINK; lia).
    split; [unfold LA_G_SINK; lia|]. split; [unfold LA_G_SINK; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA_G_SINK 0 8 (SLit 0) 0); [reflexivity | zrng | zrng |].
    rewrite Z.add_0_r. exact Hgs.
- apply pairwise_disjoint_of_extents.
  unfold stack_region, mqo_gs_obj, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite (VBv _ _ Eg) by (unfold LA_G_SINK; lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LA_G_SINK.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [mqo_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, Eg.
  rewrite !unsigned_lit_small by (unfold LA_G_SINK; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold LA_G_SINK.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* writability of the four globals the arm writes: bytes of writable segments, at any memory *)
Hypothesis HSEGS : SEGS = tfibsegs.
Lemma mqo_glob_writable : forall m a,
  (LA_G_SINK <= a < LA_G_SINK + 8) \/ (LA_G_SAID <= a < LA_G_SAID + SAID_SIZE) \/ (LA_G_SAY <= a < LA_G_SAY + 8) ->
  writable_at SEGS m a.
Proof.
  intros m a Ha. rewrite HSEGS.
  destruct Ha as [Ha | [Ha | Ha]].
  - apply (writable_at_of_wseg tfibsegs m LA_G_SINK 8); [unfold LA_G_SINK; lia | unfold LA_G_SINK; lia | | exact Ha].
    vm_compute. reflexivity.
  - apply (writable_at_of_wseg tfibsegs m LA_G_SAID SAID_SIZE); [unfold LA_G_SAID; lia | unfold LA_G_SAID, SAID_SIZE; lia | | exact Ha].
    vm_compute. reflexivity.
  - apply (writable_at_of_wseg tfibsegs m LA_G_SAY 8); [unfold LA_G_SAY; lia | unfold LA_G_SAY; lia | | exact Ha].
    vm_compute. reflexivity.
Qed.

(* a view agreement on [a, a + n) moves a val_mem *)
Lemma val_mem_of_aview : forall (W W' : world SEGS) (m m' : word -> option byte) a n v,
  (forall i, 0 <= i < Z.of_nat n -> aview SEGS (w_H W') m' (a + i) = aview SEGS (w_H W) m (a + i)) ->
  val_mem SEGS (rdW W m) a n v -> val_mem SEGS (rdW W' m') a n v.
Proof.
  intros W W' m m' a n v HA HV kk Hkk.
  rewrite (mbyte_of_aview SEGS _ _ _ _ _ (HA (Z.of_nat kk) ltac:(lia))). exact (HV kk Hkk).
Qed.

(* ==========================================================================
   The walk of the opening arm
   ========================================================================== *)
Hypothesis TB : PcapSyms B.
Variable MT : ameter_ops.
Hypothesis MT_OK : forall S m, mo_ok MT S m.
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
Hypothesis FM : afmemopen_w_spec SK SEGS B link_amf MT link_afmemopen_ctx LA_W_FMEMOPEN LA_FM_MALLOC_RA 0x10360 0x10380.
Hypothesis HL : @amf_head_law SK link_amf.
Hypothesis UMR0 : In [pc_malloc_ra0 (as_code B)] (as_universe B).
Hypothesis UMR1 : forall c, In c link_afmemopen_ctx -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
  flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (LA_FM_MALLOC_RA :: c))) (as_universe B).
Hypothesis RST : reac_served_say_to_acontract SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis RW : arewind_mf_realizes SEGS B link_amf LA_W_REWIND.
Hypothesis RSM : reac_served_mark_acontract SK SEGS PCAP_RLO PCAP_RHI B.

(* the run's write permission: its frame and g_sink (the write set's ajw, at the current state) *)
Ltac mqo_awr :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons;
    [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ lia
      | lazymatch type of Ha with context [ew _ 2%nat] =>
          match goal with U : bv_unsigned (ew _ 2%nat) = _ |- _ => rewrite U in Ha end;
          left; split; [left; lia | lia] end
      | idtac ]
    | ]);
  try apply awr_ok_x_nil.

(* the bytes a run left as they were: every byte outside the frame (YC4b.v kept_of_frame) *)
Ltac mqo_kept HFr sp UN :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => sp - 32 <= a < sp) HFr
    ltac:(intros ?bb ?wlo ?whi ?aa ?Hin ?Hrr; vm_compute in Hin;
          repeat (destruct Hin as [?Hq | Hin];
                  [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta;
                   first
                   [ clear - Hrr; lia
                   | match goal with U : bv_unsigned (ew _ 2%nat) = _ |- _ =>
                       rewrite U in Hrr; clear - Hrr; lia end ] |]);
          destruct Hin)) as UN.

Theorem mark_quietly_aproof_open : forall MO CTX,
  mark_quietly_acontract_open SK SEGS PCAP_RLO PCAP_RHI B MT MO CTX (fun _ => True)
    (fun Sc S2 => (length (wild_part (as_universe B) (st_depot S2)) <=
                   length (wild_part (as_universe B) (st_depot Sc)))%nat).
Proof.
intros MO CTX. unfold mark_quietly_acontract_open, aleaf_alloc_fx_sk.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch HA HSO HRD HLIVE HMO HCH HCTX HLP HFRM HP.
pose proof HA as HA0.
destruct HA as (HJ & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
pose proof HP as HP0.
destruct HP as (Hgs0 & Hcom & Henv & Ha1 & Hofl0 & Hwsk & Hwsay & Hwsaid & Hsdr & Hsda & Hsdh & Hmode & Hmrt).
assert (HK : MARK_QUIETLY_AK = 24608) by reflexivity.
assert (HKR : REAC_SERVED_MARK_AK = 9504) by reflexivity.
assert (HARW : ARW_STK = 4256) by reflexivity.
assert (HAFM : AFMW_STK = 16432) by reflexivity.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as HJ0.
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct mqo_vals as (V29 & V68 & VB & V30 & V31 & Vfm & Vsay & Vrw & Vrsm).
pose proof (pal_env B TL) as ENV.
pose proof (link_errno_not_static B TB) as ERRF.
assert (Hceil0 : alloc_ceiling <= spZ regs - MARK_QUIETLY_AK) by (clear - Hwlo Hceil Hslo; lia).
assert (Hsp47 : spZ regs <= 2 ^ 47) by (clear - Hwhi H47 HXO Hshi Hstk0; lia).
pose proof (mqo_entry G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ H16
  ltac:(rewrite HK in Hwlo; clear - Hwlo; lia) Hwhi Hgs0) as HS.
replace (cfg_at SEGS MARK_QUIETLY_A regs memc mdc)
  with (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_mark_quietly)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, MARK_QUIETLY_A, AF_mark_quietly; rewrite VB; reflexivity).
remember (Eimg (Ereg regs [])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E388 : ew E (A_HI 68) = Z_to_bv 64 0x6303ec)
  by (subst E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); rewrite V68; reflexivity).
assert (E271 : ew E (A_OBJ 30) = Z_to_bv 64 LA_G_SAID)
  by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V30; reflexivity).
assert (E272 : ew E (A_OBJ 31) = Z_to_bv 64 LA_MODE_W)
  by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V31; reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U388 : bv_unsigned (ew E (A_HI 68)) = 0x6303ec) by (rewrite E388; apply unsigned_lit_small; lia).
clear HEdef EL.
assert (SHOK : sh_ok SEGS (SLit SHADOW_OFF) [] E (mrestrict (w_H W) memc)) by constructor.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
          aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
assert (HGc : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN.
(* run 1, +0x00 .. +0x3c: the frame, s0 / s1 / s2, g_sink = 0 (bnez not taken), the arguments, `jal fmemopen` *)
paj_run_tok RUN HS HJ SHOK mqa_span.
{ mqo_awr. }
mqo_kept HFr (spZ regs) UNk. clear HF HFr.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msC) => rename msC into ms1 | st_ok _ _ _ (restrict _ ?msC) => rename msC into ms1 end.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12.
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
rewrite Usp in R2. rewrite E3 in R3. rewrite E4 in R4. rewrite E11 in R8.
change (ew E 271) with (ew E (A_OBJ 30)) in R10. rewrite E271 in R10.
change (ew E 272) with (ew E (A_OBJ 31)) in R12. rewrite E272 in R12.
assert (Usp1 : spZ (ms_regs ms1) = spZ regs - 32)
  by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; rewrite HK in Hceil0; lia).
pose proof HJ as (_ & _ & (memS1 & HJ1i & _) & _).
pose proof HJ1i as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
(* the relation at the call *)
assert (HR1 : mqo_rel SEGS B (spZ regs) lyc Sc W memc lyc Sc W (ms_mem ms1) md1).
{ apply ((mqo_rel_agree B LAWS) (spZ regs) lyc Sc W memc lyc Sc W memc mdc (ms_mem ms1) md1
    (fun a => spZ regs - 32 <= a < spZ regs) Hceil0 Hsp47).
  - apply (mqo_rel_refl B); [exact HAR | intros a Ha; apply Hpres; rewrite HK in Hwlo, Ha; lia].
  - exact HAR1.
  - intros a Ha Hn. exact (UNk a Ha Hn).
  - intros a Ha Hp. exact (apresent_grows _ _ _ _ HG Hp).
  - intros a Ha. right. left. rewrite HK. lia. }
(* fmemopen's arguments *)
assert (Hads : 0 <= amf_threaded link_amf < 0x700000 /\ 0 <= amf_need_locks link_amf < 0x700000 /\
               0 <= amf_ofl_lock link_amf /\ amf_ofl_lock link_amf + 4 <= 0x700000) by (cbn; lia).
assert (Hofl_eq : amf_ofl_head link_amf = LA_OFL_HEAD) by reflexivity.
assert (Henv1 : amf_env SEGS link_amf (rdW W (ms_mem ms1))).
{ destruct Henv as (Ev1 & Ev2 & Ev3).
  split; [|split]; eapply val_mem_of_aview; try eassumption; intros i Hi; cbn [Z.of_nat Pos.of_succ_nat] in Hi;
    apply UNk; rewrite HK in Hceil0; lia. }
assert (Hofl1 : val_mem SEGS (rdW W (ms_mem ms1)) (amf_ofl_head link_amf) 8 0).
{ rewrite Hofl_eq. eapply val_mem_of_aview; [|exact Hofl0].
  intros i Hi. apply UNk; unfold LA_OFL_HEAD in *; rewrite HK in Hceil0; lia. }
assert (HROD1 : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) (ms_mem ms1)))
  by (eapply (mqo_arodata B HSEGS); [exact HAR | exact Hceil0 | exact HR1 | exact HROD]).
assert (HARGS : afm_w_args SEGS link_amf 0x10360 0x10380 (ms_regs ms1) (rdW W (ms_mem ms1)))
  by (eapply (mqo_fm_args B TB HSEGS); [exact HAR1 | exact R10 | exact R11 | exact R12 | exact HROD1 | exact Henv1 | exact Hofl1]).
assert (Hs01 : s0Z (ms_regs ms1) < alloc_ceiling).
{ unfold s0Z. rewrite R8. unfold aarg, argZ in Ha1.
  replace (Z_to_bv 5 (10 + 1)) with (11%bv : bv 5) in Ha1 by (apply bv_eq; reflexivity). exact Ha1. }
clear HG.
(* the call of fmemopen *)
eapply SRr_bind.
{ rewrite Vfm.
  apply (aj_gx_fmemopen_at SK SEGS B LAWS pa_segs_low MT LA_W_FMEMOPEN FM G XO OUT W (ms_regs ms1) (ms_mem ms1)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc md1 k (getr (ms_regs ms1) 1) HGX HJ HSO);
  [ rewrite Usp1; lia
  | rewrite Usp1, HAFM; rewrite HK in Hwlo; lia
  | rewrite Usp1; lia
  | rewrite R3; exact Hgp
  | rewrite R4; exact Htp
  | reflexivity
  | rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite R1, VB; rewrite unsigned_lit_small; lia
  | exact Hs01
  | exact HL
  | exact HARGS
  | exact Hev
  | exact HLIVE
  | apply MT_OK
  | exact UMR0
  | exact UMR1 ]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Hres & Hfr2 & Hmo2 & Hfd2 & Hfs2
  & H4096 & H16r & Hbl2 & HnR & Hk2 & Hdyn2 & Hofl2 & Henv2 & Hwild2 & Hwle2 & Hly2 & HK2 & Hgrant).
pose proof HJ2 as (_ & _ & (memS2 & HJ2i & _) & _). pose proof HJ2i as (HAR2 & _).
assert (HinR2 : In (res, AMF_BLOCK) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
assert (HR2 : mqo_rel SEGS B (spZ regs) lyc Sc W memc ly2 S2 W2 mem2 md2).
{ apply ((mqo_rel_akept B) (spZ regs) lyc Sc W memc lyc Sc W (ms_mem ms1) md1 ly2 S2 W2 mem2 md2
    (spZ (ms_regs ms1) - AFMW_STK) (spZ (ms_regs ms1)) (fun a => amf_ofl_head link_amf <= a < amf_ofl_head link_amf + 8)
    Hceil0 Hsp47 HR1 HAR2 Hwle2 Hly2 Hfr2).
  - intros b n Hb. rewrite Hbl2. apply in_or_app. left. exact Hb.
  - rewrite Usp1, HAFM. rewrite HK. lia.
  - rewrite Usp1. lia.
  - intros a Ha. left. unfold mqo_E. right. right. right. left. rewrite <- Hofl_eq. exact Ha.
  - exact HK2. }
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil]. split.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp in Ha.
    apply (mbyte_of_aview SEGS). destruct HK2 as (K1 & _).
    rewrite HK in Hceil0.
    apply K1; [lia | rewrite Usp1, HAFM; lia | cbv beta; rewrite Hofl_eq; unfold LA_OFL_HEAD; lia].
  - intros a Ha Hw. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
    apply (apresent_writable SEGS). destruct HK2 as (_ & _ & _ & _ & K5 & _).
    apply K5; [rewrite HK in Hceil0; lia | rewrite Usp1, HAFM; lia |].
    apply Hpres1. rewrite HK in Hwlo. lia. }
clear HS. rename HS3 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall n, (n < 40)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite HE'; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE' : env_agree 32 (Ereg regs []) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
assert (E1' : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
assert (E3' : ew E' 3 = getr regs 3) by (rewrite OLD by lia; exact E3).
assert (E4' : ew E' 4 = getr regs 4) by (rewrite OLD by lia; exact E4).
assert (E10' : ew E' 10 = getr regs 10) by (rewrite OLD by lia; exact E10).
assert (E11' : ew E' 11 = getr regs 11) by (rewrite OLD by lia; exact E11).
assert (E388' : ew E' (A_HI 68) = Z_to_bv 64 0x6303ec).
{ rewrite HE'. unfold havoc. cbn [ew]. replace ((A_HI 68 <? 40)%nat) with false by reflexivity.
  rewrite nth_overflow; [exact E388 | rewrite length_map; vm_compute; lia]. }
assert (U388' : bv_unsigned (ew E' (A_HI 68)) = 0x6303ec) by (rewrite E388'; apply unsigned_lit_small; lia).
assert (E44' : ew E' 44 = getr regs2 10).
{ rewrite HE'. unfold havoc. cbn [ew]. replace ((44 <? 40)%nat) with false by reflexivity.
  replace (44 - 40)%nat with 4%nat by reflexivity.
  rewrite (nth_indep _ (ew E 44) (getr regs2 0%bv)) by (rewrite length_map; vm_compute; lia).
  rewrite map_nth. f_equal. all: apply bv_eq; reflexivity. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res AMF_BLOCK HAR2 HinR2) as (_ & _ & Hrc & _).
assert (Hreq : 1304 <= req_size AMF_BLOCK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (U44' : bv_unsigned (ew E' 44) = res) by (rewrite E44', Hres; apply unsigned_lit_small; lia).
clear HE' OLD.
(* g_sink at the post: still 0 (fmemopen wrote only the open-file list head among the image bytes) *)
assert (Hgs2 : au64_at SEGS (rdW W2 mem2) LA_G_SINK 0).
{ eapply val_mem_of_aview; [|exact Hgs0]. intros i Hi.
  destruct HK2 as (_ & _ & K3 & _).
  assert (Hia : LA_G_SINK <= LA_G_SINK + i < LA_G_SINK + 8) by (cbn in Hi; lia).
  rewrite (K3 (LA_G_SINK + i)).
  - apply UNk; unfold LA_G_SINK in *; rewrite HK in Hceil0; lia.
  - rewrite HSEGS. exact (mqo_gsink_in_img _ Hia).
  - rewrite (ts_owned B TB). exact (mqo_gsink_not_static _ Hia).
  - rewrite (ts_errno B TB). unfold TFIB_ERRNO, LA_G_SINK in *. lia.
  - cbv beta. rewrite Hofl_eq. unfold LA_OFL_HEAD, LA_G_SINK in *. lia. }
rewrite <- restrict_mkst_fx in HS.
lazymatch type of HS with st_ok_pi _ _ _ ?s3 ?m3 =>
  assert (HS4 : st_ok_pi SEGS VAL E'
    (add_atom (add_atom (mkSS (ss_pc s3) (ss_regs s3) (mqo_gs_w :: ss_mem s3) (ss_resv s3) (ss_facts s3))
       (A_HI 68) (mkAF 0x6303ec 0x6303ec 0)) 44%nat (mkAF 4096 (2 ^ 64 - 1) 0)) m3);
  [ apply st_ok_pi_add_fact; [apply st_ok_pi_add_fact; [apply st_ok_pi_add_region; [exact HS | vm_compute; reflexivity | | ] |] |]
  | ]
end.
{ unfold region_ok, mqo_gs_w.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U388'. split; [lia|]. split; [lia|].
  split.
  - intros o Ho. cbn [ms_mem restrict]. apply mqo_glob_writable. left. unfold LA_G_SINK. lia.
  - constructor; [|constructor].
    apply (chunk_ok_val SEGS E' _ 0x6303ec (-0x52c) 8 (SLit 0) 0); [reflexivity | zrng | zrng |].
    replace (0x6303ec + -0x52c) with LA_G_SINK by (unfold LA_G_SINK; lia).
    cbn [ms_mem restrict]. exact Hgs2. }
{ apply all_disjoint_of_extents. unfold mqo_gs_w, extent_of_region.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U388', Usp'. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite HK in Hceil0. repeat split; lia. }
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U388'. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U44'. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
clear HS. rename HS4 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end.
rewrite R1.
assert (SHOK2 : sh_ok SEGS (SLit SHADOW_OFF) [] E' (mrestrict (w_H W2) mem2)) by constructor.
(* run 2, +0x40 .. +0x48: g_sink := res, `beqz a0` not taken, `jal reac_served_say_to` *)
paj_run_tok RUN HS HJ2 SHOK2 mqa_span.
{ mqo_awr.
  all: match goal with |- context [awr_byte _ _ _ _ _ _ _ ?x] =>
    refine ((mark_quietlyOrel.ajw_mono B) G XO OUT STK sp0 FP ly S lyc Sc ly2 S2 own x (Hajw x _) Hly2 _);
    [ match goal with Ha : _ <= x < _ |- _ =>
        change (ew E' 388%nat) with (ew E' (A_HI 68)) in Ha; rewrite U388' in Ha;
        exists (LA_G_SINK, LA_G_SINK + 8); split; [cbn; tauto | cbn [fst snd]; unfold LA_G_SINK; lia] end
    | intros b n Hb; rewrite Hbl2; apply in_or_app; left; exact Hb ] end. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
  (fun a => (spZ regs - 32 <= a < spZ regs) \/ (LA_G_SINK <= a < LA_G_SINK + 8)) HFr
  ltac:(intros ?bb ?wlo ?whi ?aa ?Hin ?Hrr; vm_compute in Hin;
        repeat (destruct Hin as [?Hq | Hin];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta;
                 first
                 [ change (ew E' 388%nat) with (ew E' (A_HI 68)) in Hrr; rewrite U388' in Hrr;
                   right; unfold LA_G_SINK; clear - Hrr; lia
                 | rewrite Usp' in Hrr; left; clear - Hrr; lia ] |]);
        destruct Hin)) as UN2.
clear HF HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms3 end.
set (md3 := with_vm_backing (m_vm_lazy md2) mat0 md2) in *.
pose proof HJ2 as (_ & _ & (memS3 & HJ3i & _) & _). pose proof HJ3i as (HAR3 & _).
assert (HR3 : mqo_rel SEGS B (spZ regs) lyc Sc W memc ly2 S2 W2 (ms_mem ms3) md3).
{ apply ((mqo_rel_agree B LAWS) (spZ regs) lyc Sc W memc ly2 S2 W2 mem2 md2 (ms_mem ms3) md3
    (fun a => (spZ regs - 32 <= a < spZ regs) \/ (LA_G_SINK <= a < LA_G_SINK + 8)) Hceil0 Hsp47 HR2 HAR3).
  - intros a Ha Hn. exact (UN2 a Ha Hn).
  - intros a Ha Hp. exact (apresent_grows _ _ _ _ HG Hp).
  - intros a [Ha | Ha]; [right; left; rewrite HK; lia | left; left; exact Ha]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10.
rewrite Usp' in Q2. rewrite E3' in Q3. rewrite E4' in Q4. rewrite E44' in Q10.
assert (Usp3 : spZ (ms_regs ms3) = spZ regs - 32)
  by (unfold spZ at 1; rewrite Q2; apply unsigned_lit_small; rewrite HK in Hceil0; lia).
assert (Ha03 : aarg (ms_regs ms3) 0 = res).
{ unfold aarg, argZ. replace (Z_to_bv 5 (10 + 0)) with (10%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite Q10, Hres. apply unsigned_lit_small. lia. }
(* the call of reac_served_say_to (an aleaf at the current FP state) *)
eapply SRr_bind.
{ rewrite Vsay.
  replace (Z_to_bv 64 REAC_SERVED_SAY_TO_A) with (w64 REAC_SERVED_SAY_TO_A) by reflexivity.
  apply (RST G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem ms3) md3 (k + 1) (ms_regs ms3)).
  - split; [exact HJ2|]. split; [exact HGX|].
    split; [eapply (mqo_arodata B HSEGS); [exact HAR | exact Hceil0 | exact HR3 | exact HROD]|].
    split; [rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]|].
    split; [unfold raZ; rewrite Q1, VB; rewrite unsigned_lit_small; lia|].
    split; [rewrite Q3; exact Hgp|]. split; [rewrite Q4; exact Htp|].
    split; [rewrite Usp3; clear - H16; lia|].
    split; [unfold REAC_SERVED_SAY_TO_AK; rewrite Usp3; rewrite HK in Hwlo; lia|].
    split; [rewrite Usp3; lia|].
    split; [lia|].
    split; [constructor|].
    split.
    + intros a (r & Hr & Hra). unfold reac_served_say_to_awr in Hr. destruct Hr as [<- | []].
      apply ((mark_quietlyOrel.ajw_mono B) G XO OUT STK sp0 FP ly S lyc Sc ly2 S2 own a); [| exact Hly2 |].
      * apply Hajw. exists (LA_G_SAY, LA_G_SAY + 8). split; [cbn; tauto | exact Hra].
      * intros b n Hb. rewrite Hbl2. apply in_or_app. left. exact Hb.
    + intros a (r & Hr & Hra). unfold reac_served_say_to_awr in Hr. destruct Hr as [<- | []].
      apply Hnro. exists (LA_G_SAY, LA_G_SAY + 8). split; [cbn; tauto | exact Hra].
  - intros i Hi. apply mqo_glob_writable. right. right. lia. }
cbv beta. intros W4 c4 Hle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfr4 & Hfd4 & Hfs4 & HK4 & HS4k
  & (HS4eq & Hperm4 & Hsay4)).
pose proof HJ3i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
jafter_call_keep_pi HS 56%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1]%nat HS5.
match type of HS5 with ?tq -> _ => assert (HRK : tq); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; split.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    change (ew E' 388%nat) with (ew E' (A_HI 68)) in Ha. rewrite U388' in Ha.
    assert (Hia : LA_G_SINK <= a < LA_G_SINK + 8) by (unfold LA_G_SINK; lia).
    apply (mbyte_of_aview SEGS). destruct HK4 as (_ & _ & K3 & _).
    apply K3.
    + rewrite HSEGS. exact (mqo_gsink_in_img _ Hia).
    + rewrite (ts_owned B TB). exact (mqo_gsink_not_static _ Hia).
    + rewrite (ts_errno B TB). unfold TFIB_ERRNO, LA_G_SINK in *. lia.
    + intros (r & Hr & Hra). unfold reac_served_say_to_awr in Hr. destruct Hr as [<- | []].
      cbn [fst snd] in Hra. unfold LA_G_SAY, LA_G_SINK in *. lia.
  - intros a Ha Hw. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    change (ew E' 388%nat) with (ew E' (A_HI 68)) in Ha. rewrite U388' in Ha.
    apply mqo_glob_writable. left. unfold LA_G_SINK. lia.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp' in Ha.
    apply (mbyte_of_aview SEGS). destruct HK4 as (K1 & _).
    rewrite HK in Hceil0.
    apply K1; [lia | unfold REAC_SERVED_SAY_TO_AK; rewrite Usp3; lia |].
    intros (r & Hr & Hra). unfold reac_served_say_to_awr in Hr. destruct Hr as [<- | []].
    cbn [fst snd] in Hra. unfold LA_G_SAY in *. lia.
  - intros a Ha Hw. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp' in Ha.
    apply (apresent_writable SEGS). destruct HK4 as (_ & _ & _ & _ & K5 & _).
    apply K5; [rewrite HK in Hceil0; lia | unfold REAC_SERVED_SAY_TO_AK; rewrite Usp3; lia |].
    apply Hpres3. rewrite HK in Hwlo. lia. }
clear HS. rename HS5 into HS.
remember (havoc E' 56 (map (getr regs4) CLOB)) as E'' eqn:HE'' in HS.
assert (HEI'' : img_env VAL A_LIM E'') by (rewrite HE''; apply img_env_havoc; [exact HEI' | cbv; lia]).
assert (HAE'' : env_agree 32 (Ereg regs []) E'') by (rewrite HE''; apply env_agree_havoc_ge; [lia | exact HAE']).
assert (OLD : forall n, (n < 56)%nat -> ew E'' n = ew E' n) by (intros n Hn; rewrite HE''; apply YN3v.ew_havoc_old; exact Hn).
assert (Usp'' : bv_unsigned (ew E'' 2) = spZ regs) by (rewrite OLD by lia; exact Usp').
assert (E1'' : ew E'' 1 = getr regs 1) by (rewrite OLD by lia; exact E1').
assert (E3'' : ew E'' 3 = getr regs 3) by (rewrite OLD by lia; exact E3').
assert (E4'' : ew E'' 4 = getr regs 4) by (rewrite OLD by lia; exact E4').
assert (E10'' : ew E'' 10 = getr regs 10) by (rewrite OLD by lia; exact E10').
assert (E11'' : ew E'' 11 = getr regs 11) by (rewrite OLD by lia; exact E11').
assert (E44'' : ew E'' 44 = getr regs2 10) by (rewrite OLD by lia; exact E44').
assert (U44'' : bv_unsigned (ew E'' 44) = res) by (rewrite OLD by lia; exact U44').
assert (E388'' : ew E'' (A_HI 68) = Z_to_bv 64 0x6303ec).
{ rewrite HE''. unfold havoc. cbn [ew]. replace ((A_HI 68 <? 56)%nat) with false by reflexivity.
  rewrite nth_overflow; [exact E388' | rewrite length_map; vm_compute; lia]. }
assert (U388'' : bv_unsigned (ew E'' (A_HI 68)) = 0x6303ec) by (rewrite E388''; apply unsigned_lit_small; lia).
clear HE'' OLD.
(* the relation after the call *)
pose proof HJ4 as (_ & _ & (memS4 & HJ4i & _) & _). pose proof HJ4i as (HAR4 & _).
assert (Hbl4 : forall b n, In (b, n) (ablocks B ly2 S2) -> In (b, n) (ablocks B ly4 S4))
  by (intros b n Hb; apply (Permutation_in _ (Permutation_sym Hperm4)); exact Hb).
assert (Hly4 : layout_le 0 lyc ly4) by (eapply (layout_le0_of_gx SK SEGS B); [exact HJ0 | exact HJ4]).
assert (HR4 : mqo_rel SEGS B (spZ regs) lyc Sc W memc ly4 S4 W4 mem4 md4).
{ apply ((mqo_rel_akept B) (spZ regs) lyc Sc W memc ly2 S2 W2 (ms_mem ms3) md3 ly4 S4 W4 mem4 md4
    (spZ (ms_regs ms3) - REAC_SERVED_SAY_TO_AK) (spZ (ms_regs ms3))
    (fun a => inFP (reac_served_say_to_awr (ms_regs ms3) (rdW W2 (ms_mem ms3))) a)
    Hceil0 Hsp47 HR3 HAR4 Hle4 Hly4 Hfr4 Hbl4).
  - unfold REAC_SERVED_SAY_TO_AK. rewrite Usp3. rewrite HK. lia.
  - rewrite Usp3. lia.
  - intros a (r & Hr & Hra). unfold reac_served_say_to_awr in Hr. destruct Hr as [<- | []].
    left. unfold mqo_E. right. right. left. exact Hra.
  - exact HK4. }
assert (HblSc4 : forall b n, In (b, n) (ablocks B lyc Sc) -> In (b, n) (ablocks B ly4 S4))
  by (intros b n Hb; apply Hbl4; rewrite Hbl2; apply in_or_app; left; exact Hb).
assert (HinR4 : In (res, AMF_BLOCK) (ablocks B ly4 S4)) by (apply Hbl4; exact HinR2).
rewrite <- restrict_mkst_fx in HS. rewrite Q1.
assert (SHOK4 : sh_ok SEGS (SLit SHADOW_OFF) [] E'' (mrestrict (w_H W4) mem4)) by constructor.
(* run 3, +0x4c .. +0x50: a0 := g_sink (res), `jal wrapper_rewind` *)
paj_run_tok RUN HS HJ4 SHOK4 mqa_span.
{ mqo_awr.
  all: match goal with |- context [awr_byte _ _ _ _ _ _ _ ?x] =>
    refine ((mark_quietlyOrel.ajw_mono B) G XO OUT STK sp0 FP ly S lyc Sc ly4 S4 own x (Hajw x _) Hly4 HblSc4);
    match goal with Ha : _ <= x < _ |- _ =>
      change (ew E'' 388%nat) with (ew E'' (A_HI 68)) in Ha; rewrite U388'' in Ha;
      exists (LA_G_SINK, LA_G_SINK + 8); split; [cbn; tauto | cbn [fst snd]; unfold LA_G_SINK; lia] end end. }
clear HG.
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
  (fun a => (spZ regs - 32 <= a < spZ regs) \/ (LA_G_SINK <= a < LA_G_SINK + 8)) HFr
  ltac:(intros ?bb ?wlo ?whi ?aa ?Hin ?Hrr; vm_compute in Hin;
        repeat (destruct Hin as [?Hq | Hin];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta;
                 first
                 [ change (ew E'' 388%nat) with (ew E'' (A_HI 68)) in Hrr; rewrite U388'' in Hrr;
                   right; unfold LA_G_SINK; clear - Hrr; lia
                 | rewrite Usp'' in Hrr; left; clear - Hrr; lia ] |]);
        destruct Hin)) as UN5.
clear HF HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms5 end.
match goal with H : mem_grows (rdW W4 mem4) _ |- _ => rename H into HG5 end.
lazymatch type of HJ4 with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
  set (md5 := mdx) in * end.
pose proof HJ4 as (_ & _ & (memS5 & HJ5i & _) & _).
pose proof HJ5i as (HAR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
assert (HR5 : mqo_rel SEGS B (spZ regs) lyc Sc W memc ly4 S4 W4 (ms_mem ms5) md5).
{ apply ((mqo_rel_agree B LAWS) (spZ regs) lyc Sc W memc ly4 S4 W4 mem4 md4 (ms_mem ms5) md5
    (fun a => (spZ regs - 32 <= a < spZ regs) \/ (LA_G_SINK <= a < LA_G_SINK + 8)) Hceil0 Hsp47 HR4 HAR5).
  - intros a Ha Hn. exact (UN5 a Ha Hn).
  - intros a Ha Hp. exact (apresent_grows _ _ _ _ HG5 Hp).
  - intros a [Ha | Ha]; [right; left; rewrite HK; lia | left; left; exact Ha]. }
pmkst HS.
prreg HS (1%bv : bv 5) Z1. prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4.
prreg HS (10%bv : bv 5) Z10.
rewrite Usp'' in Z2. rewrite E3'' in Z3. rewrite E4'' in Z4. rewrite E44'' in Z10.
assert (Usp5 : spZ (ms_regs ms5) = spZ regs - 32)
  by (unfold spZ at 1; rewrite Z2; apply unsigned_lit_small; rewrite HK in Hceil0; lia).
(* the FILE block is off the image, so off g_sink *)
assert (HoffI : forall a, res <= a < res + req_size AMF_BLOCK -> ~ (LA_G_SINK <= a < LA_G_SINK + 8)).
{ intros a Ha Hg.
  destruct (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 a HAR2
    (or_introl (ex_intro _ res (ex_intro _ AMF_BLOCK (conj HinR2 Ha))))) as (_ & Hni).
  apply Hni. rewrite HSEGS. exact (mqo_gsink_in_img a Hg). }
(* the FILE at the rewind call: fmemopen's post, kept by the g_sink store, reac_served_say_to and run 3 *)
assert (HFa : forall a, res <= a < res + AMF_ZEROED ->
          aview SEGS (w_H W4) (ms_mem ms5) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. unfold AMF_ZEROED in Ha.
  assert (Hnx : ~ ((spZ regs - 32 <= a < spZ regs) \/ (LA_G_SINK <= a < LA_G_SINK + 8))).
  { intros [Hf | Hg]; [rewrite HK in Hceil0; lia | exact (HoffI a ltac:(lia) Hg)]. }
  rewrite (UN5 a ltac:(lia) Hnx).
  destruct HK4 as (_ & K2 & _).
  pose proof (K2 res AMF_BLOCK (a - res) HinR2 ltac:(lia)) as Ka.
  replace (res + (a - res)) with a in Ka by lia.
  rewrite Ka.
  - exact (UN2 a ltac:(lia) Hnx).
  - intros (r & Hr & Hra). unfold reac_served_say_to_awr in Hr. destruct Hr as [<- | []].
    cbn [fst snd] in Hra.
    assert (Hab' : res <= a < res + req_size AMF_BLOCK) by lia.
    destruct (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 a HAR2
      (or_introl (ex_intro _ res (ex_intro _ AMF_BLOCK (conj HinR2 Hab'))))) as (_ & Hni).
    apply Hni. rewrite HSEGS. exact (mqo_gsay_in_img a Hra). }
assert (Hk5 : LinkMfDefs.amf_k SEGS link_amf (rdW W4 (ms_mem ms5)) res 0).
{ eapply amf_k_agree; [|exact Hk2]. intros a Ha. apply (mbyte_of_aview SEGS). exact (HFa a Ha). }
assert (Hdyn5 : amf_dyn SEGS link_amf (rdW W4 (ms_mem ms5)) res AF_NORD 0 0 0 0 0 0).
{ eapply mqo_amf_dyn_agree; [|exact Hdyn2]. intros a Ha. apply (mbyte_of_aview SEGS). exact (HFa a Ha). }
assert (Hpend5 : amf_pend SEGS (rdW W4 (ms_mem ms5)) res []) by (intros i Hi; cbn in Hi; lia).
assert (Hbuf5 : amf_buf_ok SEGS B link_amf ARW_STK ly4 S4 W4 (ms_regs ms5) (ms_mem ms5))
  by (eapply (mqo_buf_ok B LAWS TB HSEGS); [exact HAR | exact Hceil0 | exact HP0 | exact HR5 | exact Usp5]).
assert (Hg1 : rdword (aview SEGS (w_H W4) (ms_mem ms5)) LinkMfDefs.LA_GOT_GUARD = Some LinkMfDefs.LA_GUARD)
  by (eapply link_guard_got; eassumption).
assert (Hg2 : exists g, rdword (aview SEGS (w_H W4) (ms_mem ms5)) LinkMfDefs.LA_GUARD = Some g)
  by (eapply link_guard_val; eassumption).
assert (Hab : amf_buf link_amf = LA_G_SAID /\ amf_size link_amf = SAID_SIZE) by (split; reflexivity).
eapply SRr_bind.
{ apply (aj_gx_rewind_at SK SEGS B LAWS pa_segs_low ENV ERRF (pa_sigma LS___interceptor_trampoline_rewind)
    ltac:(rewrite Vrw; exact RW)
    G XO OUT W4 (ms_regs ms5) (ms_mem ms5) STK sp0 FP ly S W0 mem0 md0 own ly4 S4 md5 (k + 1 + 0)
    (getr (ms_regs ms5) 1) res 0 AF_NORD 0 0 0 0 0 0 [] HGX HJ4);
  [ rewrite Usp5; clear - H16; lia
  | rewrite Usp5, HARW; rewrite HK in Hwlo; lia
  | rewrite Usp5; lia
  | rewrite Z3; exact Hgp
  | rewrite Z4; exact Htp
  | reflexivity
  | rewrite Z1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite Z10, Hres; reflexivity
  | exact HinR4 | exact Hk5 | exact Hdyn5 | exact Hpend5 | reflexivity | exact Hbuf5
  | exact Hg1 | exact Hg2
  | intros a Ha; exact (Hgrant a ltac:(unfold AMF_ZEROED in Ha; lia) ly4 S4 HinR4)
  | intros a Ha; destruct Hab as [Hab1 Hab2]; rewrite Hab1, Hab2 in Ha;
    apply ((mark_quietlyOrel.ajw_mono B) G XO OUT STK sp0 FP ly S lyc Sc ly4 S4 own a); [| exact Hly4 | exact HblSc4];
    apply Hajw; exists (LA_G_SAID, LA_G_SAID + SAID_SIZE); split; [cbn; tauto | cbn [fst snd]; lia] ]. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hsm6 & Hk6 & Hdyn6 & UN6 & Hgr6 & Hwin6).
pose proof HJ6 as (_ & _ & (memS6 & HJ6i & _) & _). pose proof HJ6i as (HAR6 & _).
assert (HR6 : mqo_rel SEGS B (spZ regs) lyc Sc W memc ly4 S4 W4 mem6 md6).
{ apply ((mqo_rel_agree B LAWS) (spZ regs) lyc Sc W memc ly4 S4 W4 (ms_mem ms5) md5 mem6 md6
    (fun a => (spZ (ms_regs ms5) - ARW_STK <= a < spZ (ms_regs ms5)) \/ (res <= a < res + AMF_ZEROED) \/
       (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) \/ (as_errno B <= a < as_errno B + 4))
    Hceil0 Hsp47 HR5 HAR6).
  - intros a Ha Hn. apply UN6; [exact Ha | intros h; apply Hn; tauto | intros h; apply Hn; tauto
                               | intros h; apply Hn; tauto | intros h; apply Hn; tauto].
  - intros a Ha Hp. exact (Hgr6 a Hp).
  - intros a [Ha | [Ha | [Ha | Ha]]].
    + right. left. rewrite Usp5, HARW in Ha. rewrite HK. lia.
    + right. right. exists res, AMF_BLOCK. split; [exact HinR4|]. split; [exact HnR|]. unfold AMF_ZEROED in Ha. lia.
    + left. unfold mqo_E. right. left. destruct Hab as [Hab1 Hab2]. rewrite Hab1, Hab2 in Ha. exact Ha.
    + left. unfold mqo_E. right. right. right. right. exact Ha. }
jafter_call_keep_pi HS 72%nat regs6 (mrestrict (w_H W4) mem6) HP6 [0; 1]%nat HS7.
match type of HS7 with ?tq -> _ => assert (HRK : tq); [|specialize (HS7 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. destruct Hab as [Hab1 Hab2].
  pose proof (ts_errno B TB) as HerrB. assert (Herrv : TFIB_ERRNO = 0x631b6c) by reflexivity.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; split.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    change (ew E'' 388%nat) with (ew E'' (A_HI 68)) in Ha. rewrite U388'' in Ha.
    apply (mbyte_of_aview SEGS).
    assert (Hga : LA_G_SINK <= a < LA_G_SINK + 8) by (unfold LA_G_SINK; lia).
    apply UN6.
    + unfold LA_G_SINK in Hga. lia.
    + rewrite Usp5, HARW. rewrite HK in Hceil0. unfold LA_G_SINK in Hga. lia.
    + intros Hf. apply (HoffI a); [unfold AMF_ZEROED in Hf; lia | exact Hga].
    + rewrite Hab1, Hab2. unfold LA_G_SAID, SAID_SIZE, LA_G_SINK in *. lia.
    + rewrite HerrB, Herrv. unfold LA_G_SINK in Hga. lia.
  - intros a Ha Hw. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    change (ew E'' 388%nat) with (ew E'' (A_HI 68)) in Ha. rewrite U388'' in Ha.
    apply mqo_glob_writable. left. unfold LA_G_SINK. lia.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp'' in Ha.
    apply (mbyte_of_aview SEGS).
    apply UN6; rewrite ?Usp5, ?HARW, ?Hab1, ?Hab2, ?HerrB, ?Herrv; unfold LA_G_SAID, SAID_SIZE, AMF_ZEROED;
      rewrite HK in Hceil0; lia.
  - intros a Ha Hw. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp'' in Ha.
    apply (apresent_writable SEGS). apply Hgr6. apply Hpres5. rewrite HK in Hwlo. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS7. rename HS7 into HS.
remember (havoc E'' 72 (map (getr regs6) CLOB)) as Ef eqn:HEf in HS.
assert (HEIf : img_env VAL A_LIM Ef) by (rewrite HEf; apply img_env_havoc; [exact HEI'' | cbv; lia]).
assert (OLD : forall n, (n < 72)%nat -> ew Ef n = ew E'' n) by (intros n Hn; rewrite HEf; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEf : env_agree 32 (Ereg regs []) Ef) by (rewrite HEf; apply env_agree_havoc_ge; [lia | exact HAE'']).
assert (Usp_3 : bv_unsigned (ew Ef 2) = spZ regs) by (rewrite OLD by lia; exact Usp'').
assert (E1_3 : ew Ef 1 = getr regs 1) by (rewrite OLD by lia; exact E1'').
assert (E10_3 : ew Ef 10 = getr regs 10) by (rewrite OLD by lia; exact E10'').
assert (U44_3 : bv_unsigned (ew Ef 44) = res) by (rewrite OLD by lia; exact U44'').
assert (E11_3 : ew Ef 11 = getr regs 11) by (rewrite OLD by lia; exact E11'').
assert (E388_3 : ew Ef (A_HI 68) = Z_to_bv 64 0x6303ec).
{ rewrite HEf. unfold havoc. cbn [ew]. replace ((A_HI 68 <? 72)%nat) with false by reflexivity.
  rewrite nth_overflow; [exact E388'' | rewrite length_map; vm_compute; lia]. }
assert (U388_3 : bv_unsigned (ew Ef (A_HI 68)) = 0x6303ec) by (rewrite E388_3; apply unsigned_lit_small; lia).
clear HEf OLD.
rewrite Z1.
assert (SHOK6 : sh_ok SEGS (SLit SHADOW_OFF) [] Ef (mrestrict (w_H W4) mem6)) by constructor.
(* run 4, +0x54 .. +0x70: a0 := s1, a1 := s0, the reloads, the pop, the tail jump to reac_served_mark *)
paj_run_tok RUN HS HJ6 SHOK6 mqa_span.
{ mqo_awr.
  all: match goal with |- context [awr_byte _ _ _ _ _ _ _ ?x] =>
    refine ((mark_quietlyOrel.ajw_mono B) G XO OUT STK sp0 FP ly S lyc Sc ly4 S4 own x (Hajw x _) Hly4 HblSc4);
    match goal with Ha : _ <= x < _ |- _ =>
      change (ew Ef 388%nat) with (ew Ef (A_HI 68)) in Ha; rewrite U388_3 in Ha;
      exists (LA_G_SINK, LA_G_SINK + 8); split; [cbn; tauto | cbn [fst snd]; unfold LA_G_SINK; lia] end end. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
  (fun a => (spZ regs - 32 <= a < spZ regs) \/ (LA_G_SINK <= a < LA_G_SINK + 8)) HFr
  ltac:(intros ?bb ?wlo ?whi ?aa ?Hin ?Hrr; vm_compute in Hin;
        repeat (destruct Hin as [?Hq | Hin];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta;
                 first
                 [ change (ew Ef 388%nat) with (ew Ef (A_HI 68)) in Hrr; rewrite U388_3 in Hrr;
                   right; unfold LA_G_SINK; clear - Hrr; lia
                 | rewrite Usp_3 in Hrr; left; clear - Hrr; lia ] |]);
        destruct Hin)) as UN7.
clear HF HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms7 end.
match goal with H : mem_grows (rdW W4 mem6) _ |- _ => rename H into HG7 end.
lazymatch type of HJ6 with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
  set (md7 := mdx) in * end.
pose proof HJ6 as (_ & _ & (memS7 & HJ7i & _) & _). pose proof HJ7i as (HAR7 & _).
assert (HR7 : mqo_rel SEGS B (spZ regs) lyc Sc W memc ly4 S4 W4 (ms_mem ms7) md7).
{ apply ((mqo_rel_agree B LAWS) (spZ regs) lyc Sc W memc ly4 S4 W4 mem6 md6 (ms_mem ms7) md7
    (fun a => (spZ regs - 32 <= a < spZ regs) \/ (LA_G_SINK <= a < LA_G_SINK + 8)) Hceil0 Hsp47 HR6 HAR7).
  - intros a Ha Hn. exact (UN7 a Ha Hn).
  - intros a Ha Hp. exact (apresent_grows _ _ _ _ HG7 Hp).
  - intros a [Ha | Ha]; [right; left; rewrite HK; lia | left; left; exact Ha]. }
(* g_sink at the jump: the store's value, from the symbolic state *)
pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HRg.
pose proof (field_of_region_any Ef _ 388%nat 0x6303ec _ _ _ _ _ (-1324) 8%N (SOff 44 0) HRg
  ltac:(change (ew Ef 388%nat) with (ew Ef (A_HI 68)); exact U388_3)
  ltac:(left; reflexivity) ltac:(lia)) as HVg.
assert (U44f : bv_unsigned (sv_denot Ef (SOff 44 0)) = res).
{ cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U44_3. }
rewrite U44f in HVg. rewrite Z.mod_small in HVg by (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
replace (0x6303ec + -1324) with LA_G_SINK in HVg by (unfold LA_G_SINK; lia).
cbn [ms_mem restrict] in HVg.
change (N.to_nat 8) with 8%nat in HVg.
pmkst HS.
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (10%bv : bv 5) F10. prreg HS (11%bv : bv 5) F11.
rewrite E1_3 in F1. rewrite E10_3 in F10. rewrite E11_3 in F11.
assert (E2_3 : ew Ef 2 = getr regs 2) by (apply bv_eq; rewrite Usp_3; reflexivity).
rewrite E2_3 in F2.
assert (Hspj : spZ (ms_regs ms7) = spZ regs) by (unfold spZ; rewrite F2; reflexivity).
assert (Ha0j : aarg (ms_regs ms7) 0 = aarg regs 0)
  by (unfold aarg, argZ; replace (Z_to_bv 5 (10 + 0)) with (10%bv : bv 5) by (apply bv_eq; reflexivity);
      rewrite F10; reflexivity).
assert (Ha1j : aarg (ms_regs ms7) 1 = aarg regs 1)
  by (unfold aarg, argZ; replace (Z_to_bv 5 (10 + 1)) with (11%bv : bv 5) by (apply bv_eq; reflexivity);
      rewrite F11; reflexivity).
pose proof (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs [] HS HAEf ltac:(vm_compute; reflexivity)) as HPj.
destruct Hab as [Hab1 Hab2].
pose proof (ts_errno B TB) as HerrB. assert (Herrv : TFIB_ERRNO = 0x631b6c) by reflexivity.
(* an image global off the FILE block *)
assert (Hoffimg : forall a, YG0d.in_img tfibsegs a -> ~ (res <= a < res + req_size AMF_BLOCK)).
{ intros a Hi Hb.
  destruct (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 a HAR2
    (or_introl (ex_intro _ res (ex_intro _ AMF_BLOCK (conj HinR2 Hb))))) as (_ & Hni).
  apply Hni. rewrite HSEGS. exact Hi. }
(* g_say at the jump: reac_served_say_to's value, kept since *)
assert (Hsayj : au64_at SEGS (rdW W4 (ms_mem ms7)) LA_G_SAY res).
{ unfold reac_served_say_to_apost in Hsay4. rewrite Ha03 in Hsay4. eapply val_mem_of_aview; [|exact Hsay4]. intros i Hi. cbn in Hi.
  assert (Hgi : LA_G_SAY <= LA_G_SAY + i < LA_G_SAY + 8) by lia.
  pose proof (Hoffimg _ (mqo_gsay_in_img _ Hgi)) as Hni.
  rewrite (UN7 (LA_G_SAY + i) ltac:(unfold LA_G_SAY in *; lia) ltac:(unfold LA_G_SAY, LA_G_SINK in *; rewrite HK in Hceil0; lia)).
  rewrite (UN6 (LA_G_SAY + i) ltac:(unfold LA_G_SAY in *; lia) ltac:(rewrite Usp5, HARW; unfold LA_G_SAY in *; rewrite HK in Hceil0; lia)
             ltac:(intros Hf; apply Hni; unfold AMF_ZEROED in Hf; lia)
             ltac:(rewrite Hab1, Hab2; unfold LA_G_SAY, LA_G_SAID, SAID_SIZE in *; lia)
             ltac:(rewrite HerrB, Herrv; unfold LA_G_SAY in *; lia)).
  exact (UN5 (LA_G_SAY + i) ltac:(unfold LA_G_SAY in *; lia) ltac:(unfold LA_G_SAY, LA_G_SINK in *; rewrite HK in Hceil0; lia)). }
(* the open-file list head at the jump: fmemopen's value, kept since *)
assert (Hoflj : au64_at SEGS (rdW W4 (ms_mem ms7)) LA_OFL_HEAD res).
{ rewrite Hofl_eq in Hofl2. eapply val_mem_of_aview; [|exact Hofl2]. intros i Hi. cbn in Hi.
  assert (Hgi : LA_OFL_HEAD <= LA_OFL_HEAD + i < LA_OFL_HEAD + 8) by lia.
  pose proof (Hoffimg _ (mqo_ofl_in_img _ Hgi)) as Hni.
  rewrite (UN7 (LA_OFL_HEAD + i) ltac:(unfold LA_OFL_HEAD in *; lia) ltac:(unfold LA_OFL_HEAD, LA_G_SINK in *; rewrite HK in Hceil0; lia)).
  rewrite (UN6 (LA_OFL_HEAD + i) ltac:(unfold LA_OFL_HEAD in *; lia) ltac:(rewrite Usp5, HARW; unfold LA_OFL_HEAD in *; rewrite HK in Hceil0; lia)
             ltac:(intros Hf; apply Hni; unfold AMF_ZEROED in Hf; lia)
             ltac:(rewrite Hab1, Hab2; unfold LA_OFL_HEAD, LA_G_SAID, SAID_SIZE in *; lia)
             ltac:(rewrite HerrB, Herrv; unfold LA_OFL_HEAD in *; lia)).
  rewrite (UN5 (LA_OFL_HEAD + i) ltac:(unfold LA_OFL_HEAD in *; lia) ltac:(unfold LA_OFL_HEAD, LA_G_SINK in *; rewrite HK in Hceil0; lia)).
  destruct HK4 as (_ & _ & K3 & _).
  rewrite (K3 (LA_OFL_HEAD + i) ltac:(rewrite HSEGS; exact (mqo_ofl_in_img _ Hgi))
             ltac:(rewrite (ts_owned B TB); exact (mqo_ofl_not_static _ Hgi))
             ltac:(rewrite HerrB, Herrv; unfold LA_OFL_HEAD in *; lia)).
  - exact (UN2 (LA_OFL_HEAD + i) ltac:(unfold LA_OFL_HEAD in *; lia) ltac:(unfold LA_OFL_HEAD, LA_G_SINK in *; rewrite HK in Hceil0; lia)).
  - intros (r & Hr & Hra). unfold reac_served_say_to_awr in Hr. destruct Hr as [<- | []].
    cbn [fst snd] in Hra. unfold LA_OFL_HEAD, LA_G_SAY in *. lia. }
(* the FILE at the jump: rewind's post, kept by run 4 *)
assert (Hkj : LinkMfDefs.amf_k SEGS link_amf (rdW W4 (ms_mem ms7)) res 0).
{ eapply amf_k_agree; [|exact Hk6]. intros a Ha. apply (mbyte_of_aview SEGS). unfold AMF_ZEROED in Ha.
  apply UN7; [lia|]. intros [Hf | Hg]; [rewrite HK in Hceil0; lia | exact (HoffI a ltac:(lia) Hg)]. }
assert (HfrS4 : frames S4 = frames Sc) by (rewrite Hfr4; exact Hfr2).
(* reac_served_mark's write set: the caller's, and the FILE block *)
assert (HE21 : forall a, inFP (reac_served_mark_awr res (ms_regs ms7) (rdW W4 (ms_mem ms7))) a ->
                 inFP (mark_quietly_awr_open regs (rdW W memc)) a \/ akept_out SEGS B lyc Sc a).
{ intros a (r & Hr & Hra). unfold reac_served_mark_awr in Hr. rewrite Ha0j in Hr.
  cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]].
  - left. exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [cbn; tauto | exact Hra].
  - left. exists (aivl (aarg regs 0) MK_SIZE). split; [cbn; tauto | exact Hra].
  - right. unfold aivl in Hra. cbn [fst snd] in Hra.
    replace (res =? 0) with false in Hra by (symmetry; apply Z.eqb_neq; lia).
    apply ((mqo_fresh_out B LAWS) lyc Sc ly4 S4 W4 (ms_mem ms7) md7 res AMF_BLOCK a HAR7 Hly4 HfrS4 HblSc4 HinR4 HnR).
    assert (AMF_BLOCK = 1304) by reflexivity. lia. }
assert (HlyF : ly_F ly4 = ly_F lyc) by (destruct Hly4 as (_ & _ & _ & _ & _ & HF & _); exact HF).
assert (Hperm4' : Permutation (ablocks B ly4 S4) (ablocks B lyc Sc ++ [(res, AMF_BLOCK)])) by (rewrite <- Hbl2; exact Hperm4).
rewrite Vrsm.
apply (apostF_tail_ly SK SEGS B MARK_QUIETLY_AK 1 _ REAC_SERVED_MARK_AK 0
  (fun a => inFP (reac_served_mark_awr res (ms_regs ms7) (rdW W4 (ms_mem ms7))) a)
  G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ly4 S4 W4 (ms_mem ms7) md7 (k + 1 + 0)
  (ms_regs ms7) _
  (fun ly2 S2 W2 regs2 mem2 md2 => S2 = set_fs (st_fs S2) S4 /\
     Permutation (ablocks B ly2 S2) (ablocks B ly4 S4) /\
     reac_served_mark_apost SEGS res (ms_regs ms7) (rdW W4 (ms_mem ms7)) regs2 (rdW W2 mem2))).
- lia.
- exact F1.
- exact HPj.
- rewrite Hspj, HK, HKR. lia.
- rewrite Hspj. lia.
- exact Hceil0.
- exact HlyF.
- exact HfrS4.
- transitivity (m_fds md6). { unfold md7. exact (proj1 (wvb_fds_fs _ _ _)). }
  rewrite (same_but_materialized_wvb _ _ Hsm6). rewrite (proj1 (wvb_fds_fs _ _ _)).
  unfold md5. rewrite (proj1 (wvb_fds_fs _ _ _)). rewrite Hfd4.
  unfold md3. rewrite (proj1 (wvb_fds_fs _ _ _)). rewrite Hfd2.
  unfold md1. exact (proj1 (wvb_fds_fs _ _ _)).
- transitivity (m_fs md6). { unfold md7. exact (proj2 (wvb_fds_fs _ _ _)). }
  rewrite (same_but_materialized_wvb _ _ Hsm6). rewrite (proj2 (wvb_fds_fs _ _ _)).
  unfold md5. rewrite (proj2 (wvb_fds_fs _ _ _)). rewrite Hfs4.
  unfold md3. rewrite (proj2 (wvb_fds_fs _ _ _)). rewrite Hfs2.
  unfold md1. exact (proj2 (wvb_fds_fs _ _ _)).
- destruct HR7 as (_ & _ & _ & _ & _ & HK7).
  apply (akept_errno SEGS B LAWS ENV lyc Sc W memc mdc W4 (ms_mem ms7) _ _ _ HAR).
  apply (akept_mono SK SEGS B LAWS pa_segs_low lyc Sc W memc W4 (ms_mem ms7) _ _ (mqo_E B) _ HK7).
  intros a Ha. unfold mqo_E in Ha. destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
  + left. exists (LA_G_SINK, LA_G_SINK + 8). split; [cbn; tauto | exact Ha].
  + left. exists (LA_G_SAID, LA_G_SAID + SAID_SIZE). split; [cbn; tauto | exact Ha].
  + left. exists (LA_G_SAY, LA_G_SAY + 8). split; [cbn; tauto | exact Ha].
  + left. exists (LA_OFL_HEAD, LA_OFL_HEAD + 8). split; [cbn; tauto | exact Ha].
  + right. exact Ha.
- eapply (ashadow_kept_AR SK); first [exact LAWS | exact pa_segs_low | exact HAR | exact HAR7].
- exact HblSc4.
- exact HE21.
- intros ly2f S2f W2f regs2f mem2f md2f Hlef HK2f (HS2f & Hperm2f & Hpost2f).
  split; [apply MT_LE|].
  split.
  + rewrite HS2f. cbn [st_depot set_fs]. rewrite HS4eq. cbn [st_depot set_fs]. exact Hwild2.
  + eapply ((mqo_q B LAWS TB HSEGS) res lyc Sc W memc mdc regs ly4 S4 W4 (ms_mem ms7) md7 (ms_regs ms7) ly2f S2f W2f regs2f mem2f
      HAR Hceil0 HP0 HRD HR7 HinR4 HnR HVg Hsayj Hoflj Hkj Ha0j Ha1j Hspj Hlef HK2f Hpost2f Hperm2f Hperm4').
- apply (RSM res G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly4 S4 W4 (ms_mem ms7) _ (k + 1 + 0) (ms_regs ms7)).
  + split; [exact HJ6|].
    split; [exact HGX|].
    split; [eapply (mqo_arodata B HSEGS); [exact HAR | exact Hceil0 | exact HR7 | exact HROD]|].
    split; [rewrite F1; exact Hret|].
    split; [unfold raZ; rewrite F1; exact Hra4|].
    split; [pose proof (HPj 3 ltac:(unfold acallee_saved; lia)) as G3;
            replace (Z_to_bv 5 3) with (3%bv : bv 5) in G3 by (apply bv_eq; reflexivity);
            rewrite G3; exact Hgp|].
    split; [pose proof (HPj 4 ltac:(unfold acallee_saved; lia)) as G4;
            replace (Z_to_bv 5 4) with (4%bv : bv 5) in G4 by (apply bv_eq; reflexivity);
            rewrite G4; exact Htp|].
    split; [rewrite Hspj; exact H16|].
    split; [rewrite Hspj, HKR; rewrite HK in Hwlo; lia|].
    split; [rewrite Hspj; exact Hwhi|].
    split; [lia|].
    split; [unfold aside_room in *; rewrite HfrS4; exact Hside|].
    split.
    * intros a (r & Hr & Hra). unfold reac_served_mark_awr in Hr. rewrite Ha0j in Hr.
      cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]].
      -- apply ((mark_quietlyOrel.ajw_mono B) G XO OUT STK sp0 FP ly S lyc Sc ly4 S4 own a); [| exact Hly4 | exact HblSc4].
         apply Hajw. exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [cbn; tauto | exact Hra].
      -- apply ((mark_quietlyOrel.ajw_mono B) G XO OUT STK sp0 FP ly S lyc Sc ly4 S4 own a); [| exact Hly4 | exact HblSc4].
         apply Hajw. exists (aivl (aarg regs 0) MK_SIZE). split; [cbn; tauto | exact Hra].
      -- unfold aivl in Hra. cbn [fst snd] in Hra. assert (AMF_BLOCK = 1304) by reflexivity.
         replace (res =? 0) with false in Hra by (symmetry; apply Z.eqb_neq; lia).
         exact (Hgrant a ltac:(lia) ly4 S4 HinR4).
    * intros a (r & Hr & Hra). unfold reac_served_mark_awr in Hr. rewrite Ha0j in Hr.
      cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]].
      -- apply Hnro. exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [cbn; tauto | exact Hra].
      -- apply Hnro. exists (aivl (aarg regs 0) MK_SIZE). split; [cbn; tauto | exact Hra].
      -- unfold aivl in Hra. cbn [fst snd] in Hra. assert (AMF_BLOCK = 1304) by reflexivity.
         replace (res =? 0) with false in Hra by (symmetry; apply Z.eqb_neq; lia).
         exact ((mqo_blk_not_ro B LAWS HSEGS) ly4 S4 W4 (ms_mem ms7) md7 res AMF_BLOCK a HAR7 HinR4 ltac:(lia)).
  + eapply (mqo_rsm_rd B TB HSEGS) with (lyc := lyc) (Sc := Sc) (memc := memc) (mdc := mdc) (regs := regs); eassumption.
  + exact HFRM.
  + eapply (mqo_rsm_pre B LAWS TB HSEGS) with (memc := memc) (mdc := mdc) (regs := regs); eassumption.
Qed.

End w.

About mark_quietly_aproof_open.
Print Assumptions mark_quietly_aproof_open.
