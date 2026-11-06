(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reply on the ASan build of plugin-hostd/fuzz_command, proving
   treply_spec (lib/A/Prog/reply_c.v) in cgif_file_fuzzer's walk style (A/ACh1.v..ACh8.v): the verified symbolic
   executor over the position-abstract listing (PaLibF's SRr_run_pi_AJ, PaCallRun's SRr_run_pi_AJ_call), the strlen
   wrapper through STRLEN and the kit's aj_art_at (PaArt.v), socket_send through its statement and the
   call rule (PaNoChain.v cl_callS_wide), and the tail jump into the free wrapper through cgif's afree04_rule (PaCall.v
   afree04_sub). reply has no inline check, no loop and no side-stack frame.
   Repaired 2026-10-29 to the statement pass: RLO/RHI fixed (CmdGlob.v
   CMD_RLO/CMD_RHI), LAWS from YG0q.AR_laws_ok, socket_send's astack_pres from the new astack_pres premise through
   the journal (YCbq.v astack_pres_journal), the text's tail word from cmd_heap_tail_vis, and the live-bytes bound of
   the post from socket_send's bound and the free (YCbq.v blocks_bytes_bsum).
   Re-pointed 2026-10-29 to the base lemmas of the record facts: cmd_heap_tail_vis
   (CmdRecImg.v), cmd_prog_unowned (CmdRecImg.v) and relro_img (CmdRecRo.v) over `SEGS B LAWS HB` and the record
   hypothesis IMG : cmd_img_facts SEGS B, in place of three Section hypotheses.
   Re-fitted 2026-10-29 to statement passes 4, 4b and 5:
   reply's post stays apost_base and no callee reaches printf (socket_send's post is apost_base), so the old
   closing stands (the case with no printf-reaching callee); the callee and runtime-entry hypotheses take every FP
   state and are used at the entry's fx (pass 4b); astack_pres is gone (pass 5): socket_send's chain at s0 =
   the text (a heap block) is achain_low, the free wrapper's chain_pre is achain_chain_pre on afn_pre's chain. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/reply.v, with its module paths and module names changed; 377 of its 459 lines of code are new or changed and 293 lines of the source are left out. *)
(* reac_segconf_parse (reac_segconf.c:327-332) on reac-pw/fuzz_segconf's ASan+UBSan image B (fuzz_segconf.asan-ubsan,
   pin c3796c0b38f3, twin 80e82127e8ca; 0x89784, 72 bytes, 18 instructions, frame 32 bytes, no inline check, no
   UBSan trap branch, no side-stack frame): the walk proving reac_segconf_parse_contract (lib/B/Prog/
   reac_segconf_parse_c.v, the B copy of the image-A owner's image-independent text, closed against G3 FINAL at
   6f783602b5e3) at image B's numbers. The image-B reac_segconf_parse walk lane of the image-B G3 walk owner, 2026-10-30.
   RELOCATION of the image-A G3 walk owner's image-A walk lib/A/Prog/reac_segconf_parse.v (commit
   5a66beb279ab, the image-A reac_segconf_parse walk lane): image B's code is image A's instruction for instruction except the auipc's
   PC-relative immediate (the listing: the same 18 slots, `PHi 105` in place of `PHi 103`, the same object atom
   A_OBJ 34 for the label). Changed from the A text: the module paths (lib.A -> lib.B for the listing, the Pa engine,
   RtDefs, the contracts and the kit copies), the two return offsets (A 0x44c0 / 0x44cc -> B 0x49e8 / 0x49f4), and
   the image values: image B's instantiation lib/B/Prog/SegInstB.v (the image-B harness owner, 1f771e2f2066), which keeps
   SegInstA's names (RLO_A, RHI_A, catA, gotwA, guardA, seg_litA_rc, STK_<F>) at image B's values, in place of A's
   SegInstA. The proof script is A's.
   THE B CUT PLAN (reac_segconf_parse.fuzz_segconf.asan-ubsan.s; listing lib/B/Prog/SegList.v,
   AF_reac_segconf_parse = 0x49c4, BASE = seg_text = 0x84dc0; A's cut points, one per call):
     0x89784 addi sp,sp,-32; sd ra,24(sp); sd s0,16(sp); sd s1,8(sp); mv s0,a0
     0x89798 auipc a0,0xfff98 / 0x8979c addi a2,a0,-1080   a2 = 0x21360 = seg_litA_rc S_base (listing object 34,
                                                           .str.1 of the twin's .symtab, size 0x20)
     0x897a0 mv a0,s0; 0x897a4 jal reac_segconf_parse_file (0x87e38 = BASE + AF 0x3078; return 0x897a8 = BASE + 0x49e8)
     0x897a8 mv s1,a0; mv a0,s0; 0x897b0 jal cross_check (0x897cc = BASE + AF 0x4a0c; return 0x897b4 = BASE + 0x49f4)
     0x897b4 mv a0,s1; ld ra; ld s0; ld s1; addi sp,sp,32; 0x897c8 ret
   Checks: none (no shadow load, no errpath_ call). UBSan trap sites: 0 of 0 (no branch to an unimp). Calls: the two
   program callees above, at sp - 32. Frame: 32 bytes, no realignment.
   The two call sites, each a closed lemma below (A's text):
     reac_segconf_parse_file_site_ok: reader_pre at the entry reader gives parse_file's premise at the call's
       reader (the three stores lie in this call's 32-byte frame, above every object reader_pre names), with the
       label lit S_base in its image arm (sa_img, sa_pinned, and its tail from sa_romtail).
     cross_check_site_ok: parse_file's post (the block holds fst (r_parse_file ..), the live blocks permuted) and
       the journal from the entry give cross_check's premise: the formats' bytes kept by the journal's image clause
       (their footprint is in the block), their tails by sa_romtail, their shadow by sa_pinned, the block's shadow
       from AR at the new state, the refusal count by lib/Spec/SegRefusedBound.v, the frame room by the journal's
       frames clause, the rounding mode by fxrel_frm0, the stack-protector cells by SSPX.
   The post: a0 = s1 = parse_file's result, the block holds cross_check's result (r_parse_snd / r_parse_fst),
   the two sa_noalloc tails composed.
   POSITIONAL NAMES carried from the A file, checked against image B's own tables by bounds and anchor:
   listing object 34 = 0x21360 (B SegAddr seg_objs, index 34; the twin's .str.1 of reac_segconf.c, the same
   address and bytes as on A), so the label atom 275 = A_OBJ 34 is B's label too (lbl_atom checks it by
   computation); the walk's region `stack_region 32` (B's frame is 32); the havoc atom 1028 = 1024 + 4 (a0's
   place in CLOB, the B engine is a copy of A's). No region letter or STK row of an A table is used.
   SECTION HYPOTHESES: PF, CC (the contract's head comment: parse_file's and cross_check's contracts at image B's
   entries and windows, every FP state); SIGP, OBJ, VRO (the listing's facts over the walk's abstract PAImg
   instance, SegObj.v, as fuzz_command's walks take SIGP); SSPX (the image-A G3 walk owner's SSPX, B twin: the stack-protector
   GOT word and guard at every AR state, which the allocator record pins; image B's stage-2 SegRecCells gives it
   from SegBSyms, as SegRecCells.seg_rec_cells does on A). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel SegRefusedBound.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c cross_check_c
reac_segconf_parse_file_c reac_segconf_parse_c SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* reac_segconf_parse's model is parse_file's, then cross_check of the block (SegModel.r_parse) *)
Lemma r_parse_snd rc s : snd (r_parse rc s) = snd (r_parse_file rc s (Some S_base)).
Proof. unfold r_parse. destruct (r_parse_file rc s (Some S_base)). reflexivity. Qed.
Lemma r_parse_fst rc s : fst (r_parse rc s) = cross_check (fst (r_parse_file rc s (Some S_base))).
Proof. unfold r_parse. destruct (r_parse_file rc s (Some S_base)). reflexivity. Qed.

(* ================================================ the walk ================================================ *)
(* the footprints: parse_file's lies in the block, cross_check's inside parse_file's *)
Lemma rc_parse_w_in : forall c a, inFP (seg_spec.RC_PARSE_W c) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof.
intros c a (r & Hr & Ha). unfold seg_spec.RC_PARSE_W in Hr.
unfold seg_spec.SEG_C_SIZE, seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING,
  seg_spec.RC_GEN in *.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
Lemma cc_w_in : forall c a, inFP (cross_check_W c) a -> inFP (seg_spec.RC_PARSE_W c) a.
Proof.
intros c a (r & Hr & Ha). unfold cross_check_W in Hr.
destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha.
- exists (c, c + seg_spec.RC_N + 4). split; [left; reflexivity|]. cbn [fst snd].
  unfold seg_spec.RSEG_SIZE, seg_spec.RC_N in *. lia.
- exists (c + seg_spec.RC_REFUSAL, c + seg_spec.RC_OVERFLOW + 4). split; [right; left; reflexivity|]. cbn [fst snd].
  lia.
Qed.
Lemma rcpw_closed : forall c, 0 < c -> ~ YI16.sink_open_fp (seg_spec.RC_PARSE_W c).
Proof.
intros c Hc. apply sink_closed_pos. unfold seg_spec.RC_PARSE_W, seg_spec.RC_REFUSAL, seg_spec.RC_READING.
repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a reader that agrees with another below the allocator's ceiling shows the same low objects *)
Lemma sa_str_low : forall (rd rd' : reader) p s, sa_str rd p s -> 0 <= p ->
  p + Z.of_nat (length s) < alloc_ceiling -> (forall a, 0 <= a < alloc_ceiling -> rd' a = rd a) -> sa_str rd' p s.
Proof.
intros rd rd' p s [[Hz Hn] Ht] Hp Hl K.
pose proof alloc_ceiling_value as [_ HM].
assert (HT : p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8 <= alloc_ceiling)
  by (apply tail_below; [lia | exact HM]).
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
  rewrite K by lia. exact (Hz i Hi).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
  rewrite K by lia. exact (Ht x Hx).
Qed.
Lemma rdword_low : forall (rd rd' : reader) a, 0 <= a -> a + 8 <= alloc_ceiling ->
  (forall x, 0 <= x < alloc_ceiling -> rd' x = rd x) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H0 H1 K. unfold rdword.
rewrite (K a), (K (a + 1)), (K (a + 2)), (K (a + 3)), (K (a + 4)), (K (a + 5)), (K (a + 6)), (K (a + 7)) by lia.
reflexivity.
Qed.
Lemma sa_rconf_low : forall (rd rd' : reader) c rcs, sa_rconf rd c rcs -> 0 <= c ->
  c + seg_spec.SEG_C_SIZE <= alloc_ceiling -> (forall a, 0 <= a < alloc_ceiling -> rd' a = rd a) -> sa_rconf rd' c rcs.
Proof.
intros rd rd' c rcs (bs & Hb & Henc) H0 H1 K. exists bs. split; [|exact Henc].
intros i Hi. destruct Henc as [Hl _]. rewrite K by lia. exact (Hb i Hi).
Qed.
Lemma sa_ssp_low : forall (rd rd' : reader), sa_ssp rd gotwA guardA ->
  (forall x, 0 <= x < alloc_ceiling -> rd' x = rd x) -> sa_ssp rd' gotwA guardA.
Proof.
intros rd rd' (G1 & g & G2) K. pose proof asan_consts as (C1 & _).
split; [rewrite (rdword_low rd rd' gotwA); [exact G1 | unfold gotwA; lia | unfold gotwA; lia | exact K]|].
exists g. rewrite (rdword_low rd rd' guardA); [exact G2 | unfold guardA; lia | unfold guardA; lia | exact K].
Qed.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the callee contracts (reac_segconf_parse_c.v's head comment), at image B's numbers, at every FP state *)
Hypothesis PF : forall fx0 : YK11.FPState, reac_segconf_parse_file_contract (fx := fx0) SEGS B
  (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Hypothesis CC : forall fx0 : YK11.FPState, cross_check_contract (fx := fx0) SEGS B
  (BASE + AF_cross_check) STK_cross_check RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance (B's SegObj.v; the pinned instance gives each by
   computation): call targets, object atoms, the read-only range *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
(* SSPX (the image-A G3 walk owner's hypothesis of the same name, at image B's cells): the stack-protector cells at every AR
   state, which the allocator record pins (the GOT word a constant cell, the guard an image byte); image B's
   stage-2 SegRecCells gives it from SegBSyms, as SegRecCells.seg_rec_cells does on image A *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma relro_imgA : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof.
intros a Ha. destruct VRO as [Hlo Hhi]. apply pa_relro_img. rewrite Hlo, Hhi.
unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Ha. lia.
Qed.
Lemma in_roP_img : forall a, in_roP SEGS RLO_A RHI_A a -> in_img SEGS a.
Proof.
intros a [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (relro_imgA a Hr)].
Qed.
(* the label's atom: listing object 34 is .str.1 (0x21360) on image B as on image A *)
Lemma lbl_atom : forall E, img_env VAL A_LIM E -> ew E 275%nat = w64 (seg_litA_rc S_base).
Proof.
intros E HE. rewrite (img_env_atomP E 275%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 275%nat with (A_OBJ 34). rewrite (OBJ 34%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.
Lemma sa_lit_low : forall (rd rd' : reader) a s, sa_lit SEGS B rd a s ->
  (forall x, 0 <= x < alloc_ceiling -> rd' x = rd x) -> sa_lit SEGS B rd' a s.
Proof.
intros rd rd' a s (Ha & Hs & Hp & Hr & Hi) K.
pose proof (proj1 (Hi (a + Z.of_nat (length s)) ltac:(lia))) as Himg.
pose proof (pa_img_range _ Himg) as Hrg. pose proof asan_consts as (C1 & _). unfold kImgEnd in Hrg.
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
apply (sa_str_low rd rd' a s Hs); [lia | lia | exact K].
Qed.
Lemma sa_cat_low : forall (rd rd' : reader), sa_cat SEGS B rd catA ->
  (forall x, 0 <= x < alloc_ceiling -> rd' x = rd x) -> sa_cat SEGS B rd' catA.
Proof.
intros rd rd' (Hp & Hi & Hrows) K. pose proof asan_consts as (C1 & _).
split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (sa_lit_low rd rd' tp _ Hl K)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (rdword_low rd rd'); [exact Htp | | | exact K]; unfold pin_spec.row_addr, pin_spec.CAT_ROW, catA; lia.
Qed.
(* a range inside a live heap block is addressable, with its shadow words visible, at that state *)
Lemma sa_addr_of_heap : forall ly S (W : world SEGS) mem md q n, AR SEGS B ly S W mem md -> sa_heap B ly S q n ->
  0 <= q -> 0 < n -> sa_addr (rdW W mem) q n /\ q + n <= alloc_ceiling.
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hm) Hq Hn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4 & Hc & Happ & _ & _ & Hm0).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. pose proof asan_consts as (C1 & _).
split; [|lia].
split; [lia|]. split; [lia|].
split; [exact (amem_range_sub_app b (req_size m) q n Happ Hc ltac:(lia) ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin ltac:(lia) ltac:(lia))|].
intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin ltac:(lia) ltac:(lia) Hn).
Qed.
(* a literal outside a call's footprint keeps its bytes across the call: they are image bytes the runtime does
   not own (sa_img) and the journal's image clause keeps them; its tail is ROM (sa_romtail), its shadow is pinned
   at every state (sa_pinned) *)
Lemma sa_lit_journal : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k a s,
  ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> ~ YI16.sink_open_fp FP ->
  (forall x, a <= x < a + Z.of_nat (length s) + 1 -> ~ inFP FP x) ->
  sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k a s HJ HC HnF (Ha & ((Hz & Hn) & _) & Hp & Hr & Hi).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS _ _ _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Hm & Ho & He).
rewrite F3; [exact (Hz i Hi') | exact Hm | exact Ho | exact He | apply fp_spares_closed; [exact HC | apply HnF; lia]].
Qed.

Section s.
Context {fx : YK11.FPState}.
(* the edge reac_segconf_parse -> reac_segconf_parse_file at 0x897a4: the call's reader memc differs from the
   entry's only in this call's frame [lo, lo + 32), above the allocator's ceiling *)
Lemma reac_segconf_parse_file_site_ok : forall ly S (W : world SEGS) mem memc mdc c t rcs s lo,
  AR SEGS B ly S W memc mdc -> alloc_ceiling <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < lo + 32) -> rdW W memc a = rdW W mem a) ->
  arodata_okP SEGS RLO_A RHI_A B (rdW W mem) ->
  reader_pre SEGS B seg_litA_rc catA gotwA guardA ly S (rdW W mem) c t rcs s ->
  arodata_okP SEGS RLO_A RHI_A B (rdW W memc) /\
  reac_segconf_parse_file_pre SEGS B seg_litA_rc catA gotwA guardA ly S (rdW W memc) c t (seg_litA_rc S_base) rcs s
    (Some S_base).
Proof.
intros ly S W mem memc mdc c t rcs s lo HAR Hlo KEEP HROD HRP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (LK : forall a, 0 <= a < alloc_ceiling -> rdW W memc a = rdW W mem a) by (intros a Ha; apply KEEP; lia).
destruct HRP as (C0 & C16 & RC & Hc & Ac & G1 & R1 & O1 & T0 & ST & LS & Ht & At & DJ & FR & SSP & CAT & LITS).
assert (Hc0 : 0 <= c) by (destruct Ac; lia). assert (Ht0 : 0 <= t) by (destruct At; lia).
destruct (sa_addr_of_heap ly S W memc mdc c seg_spec.SEG_C_SIZE HAR Hc Hc0 ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as [Ac' Hce].
destruct (sa_addr_of_heap ly S W memc mdc t (Z.of_nat (length s) + 1) HAR Ht Ht0 ltac:(lia)) as [At' Hte].
assert (LB : sa_lit SEGS B (rdW W memc) (seg_litA_rc S_base) S_base).
{ apply (sa_lit_low (rdW W mem)); [|exact LK]. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. left.
  right. left. reflexivity. }
split.
- intros a Hro Ho He. pose proof (pa_img_range a (in_roP_img a Hro)) as Hrg. unfold kImgEnd in Hrg.
  rewrite LK by lia. exact (HROD a Hro Ho He).
- split; [|split].
  + split; [exact C0|]. split; [exact C16|].
    split; [exact (sa_rconf_low _ _ c rcs RC Hc0 Hce LK)|].
    split; [exact Hc|]. split; [exact Ac'|].
    split; [exact G1|]. split; [exact R1|]. split; [exact O1|]. split; [exact T0|].
    split; [apply (sa_str_low _ _ t s ST); [exact Ht0 | lia | exact LK]|].
    split; [exact LS|]. split; [exact Ht|]. split; [exact At'|]. split; [exact DJ|]. split; [exact FR|].
    split; [exact (sa_ssp_low _ _ SSP LK)|].
    split; [exact (sa_cat_low _ _ CAT LK)|].
    intros x Hx. exact (sa_lit_low _ _ _ _ (LITS x Hx) LK).
  + destruct LB as (Ha & Hs & _). cbn [sa_ostr]. split; [lia | exact Hs].
  + destruct LB as (Ha & Hs & Hp & Hr & Hi).
    split; [apply Nat.leb_le; vm_compute; reflexivity|].
    split; [right; right; split; [exact Hi | split; [exact Hp|]]|].
    { intros ly0 S0 W0 mem0 md0 _. apply sa_tail_of_romtail. exact Hr. }
    split; [exact (Hp ly S W memc mdc HAR)|].
    (* the label's read span [0x21360, 0x21370) is in the image, below the block, which is off the image *)
    destruct Hc as (b & m & Hin & Hb & Hm).
    pose proof (blk_off_imgP B ly S W memc mdc b m HAR Hin) as Hoff.
    pose proof (req_size_pos m ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & _ & _ & _ & _ & _ & H); lia))
      as [_ Hr'].
    rewrite seg_litA_rc_S_base. unfold sa_disj, seg_spec.cstr_span, off_img in *.
    replace (Z.of_nat (length S_base)) with 12 by (vm_compute; reflexivity).
    unfold seg_spec.SEG_C_SIZE, seg_spec.RC_READING in *. destruct Hoff as [Hoff | Hoff].
    * right. lia.
    * left. change ((- (136032 + 12 + 1)) mod 8) with 3. lia.
Qed.
(* the edge reac_segconf_parse -> cross_check at 0x897b0: the journal from the entry to the call state (the
   frame's stores and parse_file, footprint RC_PARSE_W c inside the block) and parse_file's post give
   cross_check's premise *)
Lemma cross_check_site_ok : forall STK sp0 ly S (W : world SEGS) mem md ly2 S2 (W2 : world SEGS) mem2 md2 k c
  rcs1,
  ajournal SEGS B STK sp0 (seg_spec.RC_PARSE_W c) ly S W mem md [] ly2 S2 W2 mem2 md2 k ->
  arodata_okP SEGS RLO_A RHI_A B (rdW W mem) ->
  c <> 0 -> 0 <= c -> c mod 16 = 0 -> sa_heap B ly S c seg_spec.SEG_C_SIZE ->
  (forall x, In x CROSS_CHECK_LITS -> sa_lit SEGS B (rdW W mem) (seg_litA_rc x) x) ->
  sa_room_n 2 S -> st_nev S + k <= EV_MAX ->
  sa_rconf (rdW W2 mem2) c rcs1 -> rc_refused rcs1 + 64 < 2 ^ 32 ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  sa_frm0 ->
  arodata_okP SEGS RLO_A RHI_A B (rdW W2 mem2) /\
  cross_check_pre SEGS B seg_litA_rc gotwA guardA ly2 S2 (rdW W2 mem2) c rcs1 /\
  sa_room S2 /\ st_nev S2 + EV_cross_check <= EV_MAX.
Proof.
intros STK sp0 ly S W mem md ly2 S2 W2 mem2 md2 k c rcs1 HJ HROD C0 Hc00 C16 Hc HCCL HROOM HEV HRC1 HREF1 HPERM
  HFRM.
pose proof (proj1 HJ) as HAR2.
pose proof HJ as (_ & _ & _ & _ & _ & Hfr & Hnev & _ & _ & _ & F3 & _).
assert (Hc0 : 0 < c) by lia.
assert (Hc2 : sa_heap B ly2 S2 c seg_spec.SEG_C_SIZE).
{ destruct Hc as (b & m & Hin & H1 & H2). exists b, m.
  split; [exact (Permutation_in _ (Permutation_sym HPERM) Hin) | lia]. }
destruct (sa_addr_of_heap ly2 S2 W2 mem2 md2 c seg_spec.SEG_C_SIZE HAR2 Hc2 ltac:(lia)
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [Ac2 _].
assert (HC : ~ YI16.sink_open_fp (seg_spec.RC_PARSE_W c)) by (apply rcpw_closed; exact Hc0).
(* no image byte is in the footprint: the footprint is in the block, whose bytes are client bytes *)
assert (NF : forall x, in_img SEGS x -> ~ inFP (seg_spec.RC_PARSE_W c) x).
{ intros x Hx Hf. apply rc_parse_w_in in Hf. destruct Hc2 as (b & m & Hin & H1 & H2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
  destruct (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 x HAR2) as [_ Hn].
  { left. exists b, m. split; [exact Hin | lia]. }
  exact (Hn Hx). }
split.
- intros a Hro Ho He. pose proof (in_roP_img a Hro) as Hia.
  rewrite F3; [exact (HROD a Hro Ho He) | exact Hia | exact Ho | exact He | apply fp_spares_closed; [exact HC | exact (NF a Hia)]].
- split; [|split].
  + split; [lia|]. split; [exact C16|]. split; [exact HRC1|]. split; [exact Hc2|]. split; [exact Ac2|].
    split; [exact HREF1|]. split; [exact HFRM|]. split; [exact (SSPX ly2 S2 W2 mem2 md2 HAR2)|].
    intros x Hx. pose proof (HCCL x Hx) as HL.
    eapply sa_lit_journal; [exact HJ | exact HC | | exact HL].
    intros y Hy. destruct HL as (_ & _ & _ & _ & Hi). exact (NF y (proj1 (Hi y ltac:(lia)))).
  + unfold sa_room. unfold sa_room_n in HROOM. rewrite Hfr. cbn [app]. lia.
  + unfold EV_cross_check. lia.
Qed.
End s.

Section w.
Context {fx : YK11.FPState}.
Theorem reac_segconf_parse_walk : reac_segconf_parse_contract SEGS B (BASE + AF_reac_segconf_parse)
  STK_reac_segconf_parse RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Proof.
unfold reac_segconf_parse_contract.
intros ly S W regs mem md ch c t rcs s HPRE HROD H10 Hc64 H11 Ht64 HRP HCCL HROOM HEV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & SCC & SPF & SPA & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HRP as (C0 & C16 & RC & Hc & Ac & G1 & RF1 & O1 & T0 & ST & LS & Ht & At & DJ & FR & SSP & CAT & LITS).
destruct Hc as (bc & mc & Hinc & Hbc & Hcm).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR Hinc) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hmc).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hreq].
assert (Hcl : 0 < c /\ c + seg_spec.SEG_C_SIZE <= alloc_ceiling) by (unfold seg_spec.SEG_C_SIZE in *; lia).
assert (Hclt : c < alloc_ceiling) by (unfold seg_spec.SEG_C_SIZE in *; lia).
destruct ST as [[_ NUL] _].
pose proof (ajournal_init SEGS B STK_reac_segconf_parse (seg_spec.RC_PARSE_W c) ly S W regs mem md ch HPRE) as HJ.
set (sp0 := spZ regs) in *.
set (E := Eimg (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok_pi SEGS VAL E (mkSS AF_reac_segconf_parse sr_atoms [stack_region 32] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_parse)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, stack_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
unfold cfg_at. change (w64 (BASE + AF_reac_segconf_parse)) with (Z_to_bv 64 (BASE + AF_reac_segconf_parse)).
(* 0x89784 .. 0x897a4: the frame, the spills of ra, s0, s1, s0 = c, a2 = the label, a0 = c, the call *)
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | cbn; lia | cbn; lia | apply awr_ok_nil]. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 32 <= a < sp0) HFr
  ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin'; destruct Hin' as [Hq | []]; injection Hq as <- <- <-;
        cbn [base_val] in Hrr; rewrite Usp in Hrr; lia)) as UN1.
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Qsp : spZ (ms_regs ms) = sp0 + -32) by (unfold spZ; rewrite Q2, Usp; rewrite unsigned_lit_small by lia; lia).
assert (Q8' : getr (ms_regs ms) 8 = w64 c) by (rewrite Q8, (EE 10%nat 10%bv eq_refl); exact H10).
assert (Q10' : getr (ms_regs ms) 10 = w64 c) by (rewrite Q10, (EE 10%nat 10%bv eq_refl); exact H10).
assert (Q11' : getr (ms_regs ms) 11 = w64 t) by (rewrite Q11, (EE 11%nat 11%bv eq_refl); exact H11).
assert (Q12' : getr (ms_regs ms) 12 = w64 (seg_litA_rc S_base)) by (rewrite Q12; apply lbl_atom; exact HEI).
pmkst HS.
assert (Hlo32 : alloc_ceiling <= sp0 - 32) by lia.
destruct (reac_segconf_parse_file_site_ok (fx := fx) ly S W mem (ms_mem ms) _ c t rcs s (sp0 - 32) (proj1 HJ)
  Hlo32 ltac:(intros a Ha Hn; apply UN1; [exact Ha | lia]) HROD HRP) as [HROD1 HPF1].
rewrite (SIGP SS_reac_segconf_parse_file ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_parse_file) with AF_reac_segconf_parse_file by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callSF (fx := fx) B LAWS W (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_parse sp0
    (seg_spec.RC_PARSE_W c) ly S W mem md [] ly S _ 0 STK_reac_segconf_parse_file (seg_spec.RC_PARSE_W c)
    EV_reac_segconf_parse_file (-32) (Z_to_bv 64 (BASE + 0x49e8)) []
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       getr regs2 10 = w64 (snd (r_parse_file rcs s (Some S_base))) /\
       sa_rconf (rdW W2 mem2) c (fst (r_parse_file rcs s (Some S_base))) /\
       sa_noalloc B ly S ly2 S2) HJ).
  - exact Qsp.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite Q8'. unfold w64. rewrite unsigned_lit_small by lia. exact Hclt.
  - intros HPRE1. eapply SRr_mono.
    { apply (PF fx ly S W (ms_regs ms) (ms_mem ms) _ [] c t (seg_litA_rc S_base) rcs s (Some S_base) HPRE1 HROD1
        Q10' ltac:(lia) Q11' ltac:(lia) Q12' ltac:(pose proof (seg_litA_rc_S_base); lia) HPF1 HROOM).
      unfold EV_reac_segconf_parse_file. unfold EV_reac_segconf_parse in HEV. lia. }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite Q1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact Ha|]. apply rc_parse_w_in in Ha. exists bc, mc.
    split; [exact Hinc | lia]. }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (Ha02 & HRC2 & HNA2)).
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
(* back at 0x897a8, at the FP state fx1 parse_file returned *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0%nat] HS2.
lazymatch type of HS2 with ?P -> _ => assert (HQ : P); [| specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJc2 | exact HJ2 | exact Usp | lia | lia | lia | lia | lia |].
  intros a Ha Hf. apply rc_parse_w_in in Hf. lia. }
rewrite <- restrict_mkst_fx in HS2.
apply (st_ok_pi_restrict_xfx fx fx1) in HS2.
pose proof (img_env_havoc_hi E 1024 (map (getr regs2) CLOB) HEI ltac:(unfold A_LIM; lia)) as HEI2.
clear HS Q1 Q2 Q3 Q4 Q8 Q10 Q11 Q12 Q8' Q10' Q11' Q12' Qsp UN1.
(* 0x897a8 .. 0x897b0: s1 = n, a0 = c, the call *)
rename ms into ms1.
paj_run_shc (SRr_run_pi_AJ (fx := fx1) B LAWS) (SRr_run_pi_AJ_call (fx := fx1) B LAWS) HS2 HJ2.
{ eapply awr_ok_cons_stack with (n := 2%nat);
    [reflexivity | rewrite ew_havoc_old by (cbn; lia); exact Usp | cbn; lia | cbn; lia | apply awr_ok_nil]. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 32 <= a < sp0) HFr
  ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin'; destruct Hin' as [Hq | []]; injection Hq as <- <- <-;
        cbn [base_val] in Hrr; rewrite ew_havoc_old, Usp in Hrr by (cbn; lia); lia)) as UN2.
clear HF HFr HG.
prreg HS2 (1%bv : bv 5) R1. prreg HS2 (2%bv : bv 5) R2. prreg HS2 (3%bv : bv 5) R3. prreg HS2 (4%bv : bv 5) R4.
prreg HS2 (8%bv : bv 5) R8. prreg HS2 (10%bv : bv 5) R10.
assert (Rsp : spZ (ms_regs ms) = sp0 + -32).
{ unfold spZ. rewrite R2. rewrite ?ew_havoc_old by (cbn; lia). rewrite Usp.
  rewrite unsigned_lit_small by lia. lia. }
assert (R8' : getr (ms_regs ms) 8 = w64 c) by (rewrite R8, (EE 10%nat 10%bv eq_refl); exact H10).
assert (R10' : getr (ms_regs ms) 10 = w64 c) by (rewrite R10, (EE 10%nat 10%bv eq_refl); exact H10).
pmkst HS2.
destruct HNA2 as (HPERM2 & Hly2 & (f2 & HS2e)).
assert (HRC2' : sa_rconf (rdW W2 (ms_mem ms)) c (fst (r_parse_file rcs s (Some S_base))))
  by (apply (sa_rconf_low (rdW W2 mem2)); [exact HRC2 | lia | lia | intros a Ha; apply UN2; lia]).
destruct (cross_check_site_ok (fx := fx1) _ _ ly S W mem md ly2 S2 W2 (ms_mem ms) _ _ c _ HJ2 HROD C0 ltac:(lia) C16
  ltac:(exists bc, mc; split; [exact Hinc | lia]) HCCL
  HROOM ltac:(unfold EV_reac_segconf_parse_file; unfold EV_reac_segconf_parse in HEV; lia) HRC2'
  ltac:(apply r_parse_file_refused_bound; [exact NUL | exact LS | exact RF1])
  HPERM2 ltac:(apply (fxrel_frm0 fx fx1); [exact FR | exact Hfx1]))
  as (HROD2 & HCC2 & HROOM2 & HEV2).
rewrite (SIGP SS_cross_check ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_cross_check) with AF_cross_check by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callSF (fx := fx1) B LAWS W2 (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_parse sp0
    (seg_spec.RC_PARSE_W c) ly S W mem md [] ly2 S2 _ _ STK_cross_check (cross_check_W c) EV_cross_check (-32)
    (Z_to_bv 64 (BASE + 0x49f4)) []
    (fun ly3 S3 W3 regs3 mem3 md3 =>
       sa_rconf (rdW W3 mem3) c (cross_check (fst (r_parse_file rcs s (Some S_base)))) /\
       sa_noalloc B ly2 S2 ly3 S3) HJ2).
  - exact Rsp.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite R3. rewrite ?ew_havoc_old by (cbn; lia). rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4. rewrite ?ew_havoc_old by (cbn; lia). rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite R8'. unfold w64. rewrite unsigned_lit_small by lia. exact Hclt.
  - intros HPRE2. eapply SRr_mono.
    { apply (CC fx1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ [] c (fst (r_parse_file rcs s (Some S_base))) HPRE2 HROD2
        R10' ltac:(lia) HCC2 HROOM2 HEV2). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite R1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (cc_w_in c a Ha)|]. apply cc_w_in, rc_parse_w_in in Ha. exists bc, mc.
    split; [exact (Permutation_in _ (Permutation_sym HPERM2) Hinc) | lia]. }
cbv beta. intros W3 c3 _ (fx2 & ly3 & S3 & regs3 & mem3 & md3 & Hfx2 & -> & HJ3 & HJc3 & HP3 & (HRC3 & HNA3)).
eapply (srr_apost_base_liftF (fx := fx1) SEGS fx2); [exact Hfx2|].
(* back at 0x897b4, at the FP state fx2 cross_check returned *)
jafter_call_keep_hi HS2 1040%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0%nat] HS3.
lazymatch type of HS3 with ?P -> _ => assert (HQ : P); [| specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
    [exact HJc3 | exact HJ3 | rewrite ew_havoc_old by (cbn; lia); exact Usp | lia | lia | lia | lia | lia |].
  intros a Ha Hf. apply cc_w_in, rc_parse_w_in in Hf. lia. }
rewrite <- restrict_mkst_fx in HS3.
apply (st_ok_pi_restrict_xfx fx1 fx2) in HS3.
pose proof (img_env_havoc_hi _ 1040 (map (getr regs3) CLOB) HEI2 ltac:(unfold A_LIM; lia)) as HEI3.
clear HS2 R1 R2 R3 R4 R8 R10 R8' R10' Rsp UN2.
(* 0x897b4 .. 0x897c8: a0 = n, ra / s0 / s1 restored, the frame popped, ret *)
rename ms into ms2.
paj_run_shc (SRr_run_pi_AJ (fx := fx2) B LAWS) (SRr_run_pi_AJ_call (fx := fx2) B LAWS) HS3 HJ3.
{ eapply awr_ok_cons_stack with (n := 2%nat);
    [reflexivity | rewrite !ew_havoc_old by (cbn; lia); exact Usp | cbn; lia | cbn; lia | apply awr_ok_nil]. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 32 <= a < sp0) HFr
  ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin'; destruct Hin' as [Hq | []]; injection Hq as <- <- <-;
        cbn [base_val] in Hrr; rewrite !ew_havoc_old, Usp in Hrr by (cbn; lia); lia)) as UN3.
clear HF HFr HG.
prreg HS3 (1%bv : bv 5) F1. prreg HS3 (10%bv : bv 5) F10.
assert (HAE : env_agree 32 (Ereg regs []) (havoc (havoc E 1024 (map (getr regs2) CLOB)) 1040 (map (getr regs3) CLOB))).
{ split; [|reflexivity]. intros n Hn. rewrite !ew_havoc_old by lia. subst E. apply Eimg_low. unfold A_TEXT. lia. }
eapply (paj_ret_at (fx := fx2) (PL := PL_seg) (PI := PI) W3 _ _ _ _ _ HS3 eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly3, S3, r, m, d end.
split; [rewrite F1; rewrite ?ew_havoc_old by (cbn; lia); rewrite (EE 1%nat 1%bv eq_refl);
        unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [eapply ajournal_mono_k; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3 |];
        unfold EV_reac_segconf_parse, EV_reac_segconf_parse_file, EV_cross_check; lia|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS3); [exact HAE | vm_compute; reflexivity]|].
destruct HNA3 as (HPERM3 & Hly3 & (f3 & HS3e)).
split; [rewrite r_parse_snd, F10; rewrite ?ew_havoc_old by (cbn; lia);
        change (nth 4 (map (getr regs2) CLOB) (ew E 1028)) with (getr regs2 10); exact Ha02|].
split; [rewrite r_parse_fst; apply (sa_rconf_low (rdW W3 mem3)); [exact HRC3 | lia | lia | intros a Ha; apply UN3; lia]|].
split; [exact (Permutation_trans HPERM3 HPERM2)|].
split; [rewrite Hly3; exact Hly2|].
exists f3. rewrite HS3e, HS2e. reflexivity.
Qed.
End w.
End e.
End f.
End d.
