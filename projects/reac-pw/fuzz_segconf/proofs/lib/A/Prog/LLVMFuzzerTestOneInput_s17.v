(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 837 of its 889 lines of code are new or changed and 401 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): file group _s17, the segments S07 and
   S08 of the test harness's entry function LLVMFuzzerTestOneInput (0x84d34), cuts K853bc -> K85414 -> K85024 (f + 1)
   or K854a0:
   - S07 0x853bc .. 0x85410 (lt_seg_S07): the last turn's reac_segconf_parse(c, text) (0x853c4, its contract at the
     segment's FP state, returning at some FP state fx1), check 18 (m->n's shadow byte, 0 since m's block is
     addressable), returned &= (answer == m->n), the next cut's registers from the slots, and free(text) (0x85410,
     afree04_rule); its model facts (the last turn's states, conf_rel) are LLVMFuzzerTestOneInput_s17k.v's;
   - S08 0x85414 .. 0x85430 (lt_seg_S08): the label out of scope (five shadow bytes := 0xf8) and the file loop's
     latch beq s2, s9, to K85024 (f + 1) or, on the last turn, to K854a0 (seg_after = SegModel.run, s17_after_last).
   Each lemma proves its statement lt_seg_S<k>_stmt of LLVMFuzzerTestOneInput_defs.v exactly; the callee contract
   and the free wrapper's rule are Section hypotheses at every FP state, as fuzz_command's walk files take them.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; output pasted verbatim in
   the walk's shared brief; checker (fresh, read-only): CONFIRM; none: written new) *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c cross_check_c
reac_segconf_parse_file_c reac_segconf_parse_c m_file_c SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c
LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s02 LLVMFuzzerTestOneInput_s10k
LLVMFuzzerTestOneInput_s17k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= reader facts ======================================= *)
Lemma s17_rdword_rng : forall segs H mem a v, rdword (aview segs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros segs H mem a v Hw. unfold rdword in Hw.
destruct (aview segs H mem a) as [b0|] eqn:E0; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 1)) as [b1|] eqn:E1; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 2)) as [b2|] eqn:E2; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 3)) as [b3|] eqn:E3; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 4)) as [b4|] eqn:E4; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 5)) as [b5|] eqn:E5; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 6)) as [b6|] eqn:E6; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 7)) as [b7|] eqn:E7; [|cbn in Hw; discriminate Hw].
cbn in Hw. injection Hw as <-.
apply sa_aview_rng in E0, E1, E2, E3, E4, E5, E6, E7.
lia.
Qed.

(* the frame's 36 shadow bytes: S08's five stores turn the label's out of scope, nothing else changes *)
Lemma s17_fsh_same : forall i, (i < 36)%nat -> ~ (12 <= i < 17)%nat -> nth i (lt_fsh LFO0) 0 = nth i (lt_fsh LFO_L) 0.
Proof. intros i Hi Hn. do 36 (destruct i as [|i]; [first [reflexivity | lia] |]). lia. Qed.
Lemma s17_fsh_f8 : forall i, (12 <= i < 17)%nat -> nth i (lt_fsh LFO0) 0 = 248.
Proof. intros i Hi. do 17 (destruct i as [|i]; [first [reflexivity | lia] |]). lia. Qed.

(* ---- the model of the file loop's latch: the plain / UBSan owner's plain lib/Prog/Seg/L03.v:57-97 (commit 440d61eaa8c8, its lemmas l03_after_next, l03_skipn_nth, l03_run_skip, l03_after_last), copied with seg_spec's
   names qualified ---- *)
(* a turn that is not the last is the drop-in step of seg_run *)
Lemma s17_after_next : forall inp f, Z.of_nat (S f) <> seg_spec.seg_nfiles inp ->
  seg_spec.seg_after inp f = seg_spec.seg_run inp (S f).
Proof. intros inp f H. unfold seg_spec.seg_after. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.
Lemma s17_skipn_nth : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros A l. induction l as [|x l IH]; intros k d Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn [length] in Hk. lia.
Qed.
(* the run of the payload is the run of the files after k turns, from the state after k drop-in turns *)
Lemma s17_run_skip : forall inp k, (k < length (seg_spec.seg_files inp))%nat ->
  SegModel.run (seg_spec.seg_pay inp) = run_files (skipn k (seg_spec.seg_files inp))
    (seg_spec.seg_rc (seg_spec.seg_run inp k)) (seg_spec.seg_mc (seg_spec.seg_run inp k))
    (seg_spec.seg_ret (seg_spec.seg_run inp k)).
Proof.
  intros inp k. induction k as [|k IH]; intros Hk; [reflexivity|].
  rewrite IH by lia.
  rewrite (s17_skipn_nth (seg_spec.seg_files inp) k (SegModel.File 0 [])) by lia.
  assert (Hne : skipn (S k) (seg_spec.seg_files inp) <> []).
  { intros E. pose proof (f_equal (@length SegModel.file) E) as E'. rewrite length_skipn in E'. cbn [length] in E'. lia. }
  destruct (skipn (S k) (seg_spec.seg_files inp)) as [|y r] eqn:Es; [congruence|].
  cbn [seg_spec.seg_run]. unfold seg_spec.seg_turn_step, seg_spec.seg_txt, seg_spec.seg_label, seg_spec.seg_lb,
    seg_spec.seg_file.
  destruct (seg_spec.seg_run inp k) as [[c0 m0] r0].
  cbn [seg_spec.seg_rc seg_spec.seg_mc seg_spec.seg_ret fst snd run_files].
  destruct (r_parse_file c0 _ _) as [c1 n]. reflexivity.
Qed.
(* the last turn ends the run of the payload (the model obligation of S08 in the cut statements) *)
Lemma s17_after_last : forall inp f, Z.of_nat (S f) = seg_spec.seg_nfiles inp ->
  seg_spec.seg_after inp f = SegModel.run (seg_spec.seg_pay inp).
Proof.
  intros inp f H.
  assert (Hl : length (seg_spec.seg_files inp) = S f) by (unfold seg_spec.seg_nfiles in H; lia).
  rewrite (s17_run_skip inp f) by lia.
  rewrite (s17_skipn_nth (seg_spec.seg_files inp) f (SegModel.File 0 [])) by lia.
  replace (skipn (S f) (seg_spec.seg_files inp)) with (@nil SegModel.file) by (symmetry; apply skipn_all2; lia).
  unfold seg_spec.seg_after. rewrite H, Z.eqb_refl.
  unfold seg_spec.seg_turn_step, seg_spec.seg_txt, seg_spec.seg_file.
  destruct (seg_spec.seg_run inp f) as [[c0 m0] r0].
  cbn [seg_spec.seg_rc seg_spec.seg_mc seg_spec.seg_ret fst snd run_files].
  reflexivity.
Qed.

(* ---- facts carried from one reader to another that agrees on their bytes ---- *)
Lemma s17_bytes_xfer : forall (rd rd' : reader) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> rd' (a + i) = rd (a + i)) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs K H i Hi. rewrite K by lia. exact (H i Hi). Qed.
Lemma s17_rconf_xfer : forall (rd rd' : reader) c rc,
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd' (c + i) = rd (c + i)) -> sa_rconf rd c rc -> sa_rconf rd' c rc.
Proof.
intros rd rd' c rc K (bs & Hb & He). exists bs. split; [|exact He].
apply (s17_bytes_xfer rd rd' c bs); [|exact Hb]. destruct He as [Hl _]. intros i Hi. apply K. lia.
Qed.
Lemma s17_mconf_xfer : forall (rd rd' : reader) a mc,
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd' (a + i) = rd (a + i)) -> sa_mconf rd a mc -> sa_mconf rd' a mc.
Proof.
intros rd rd' a mc K (bs & Hb & He). exists bs. split; [|exact He].
apply (s17_bytes_xfer rd rd' a bs); [|exact Hb]. destruct He as [Hl _]. intros i Hi. apply K. lia.
Qed.
Lemma s17_rdword_xfer : forall (rd rd' : reader) a v,
  (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v K H. rewrite (rdword_ext rd rd'); [exact H | exact K]. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma s17_word_chunk : forall (W : world SEGS) mem E (n : nat) base off v,
  rdword (rdW W mem) (base + off) = Some v -> ew E n = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros W mem E n base off v Hw He.
pose proof (s17_rdword_rng _ _ _ _ _ Hw) as Hr.
apply (chunk_ok_val SEGS E _ base off 8 (SOff n 0) v);
  [cbn [sv_denot]; rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
exact (val_mem_of_rdword SEGS _ _ _ _ Hw).
Qed.
Lemma s17_slots_xfer : forall cx (rd rd' : reader) L,
  (forall o v, In (o, v) L -> forall k, 0 <= k < 8 -> rd' (x_s1 cx + o + k) = rd (x_s1 cx + o + k)) ->
  lt_slots cx rd L -> lt_slots cx rd' L.
Proof.
intros cx rd rd' L K H o v Hin. rewrite (rdword_ext rd rd'); [exact (H o v Hin)|]. intros k Hk. exact (K o v Hin k Hk).
Qed.
Lemma s17_saved_xfer : forall cx (rd rd' : reader),
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> rd' a = rd a) -> lt_saved cx rd -> lt_saved cx rd'.
Proof.
intros cx rd rd' K H i r Hn.
pose proof (proj1 (nth_error_Some LT_SAVED i) ltac:(rewrite Hn; discriminate)) as Hi. cbn [length LT_SAVED] in Hi.
rewrite (rdword_ext rd rd'); [exact (H i r Hn)|]. intros k Hk. apply K. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HPARSE : forall fx0 : YK11.FPState, reac_segconf_parse_contract (fx := fx0) SEGS B
  (BASE + AF_reac_segconf_parse) STK_reac_segconf_parse RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog (PI := PI).
(* the two image facts lt_img needs at a later reader (_s10's bundle, LLVMFuzzerTestOneInput_s10k.v) and the
   record's symbols (AR's stack-protector cells) *)
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ---------------- the image facts, kept by any step that keeps the program's image bytes ---------------- *)
Definition s17_ikeep (rd rd' : reader) : Prop :=
  forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  rd' a = rd a.
(* _s10's transport (s10_lt_img_kept) at this file's reader pair, the later one at an AR state *)
Lemma s17_img_keep : forall cx (W W' : world SEGS) mem mem' {ly' S' md'}, AR SEGS B ly' S' W' mem' md' ->
  s17_ikeep (rdW W mem) (rdW W' mem') -> lt_img B cx (rdW W mem) -> lt_img B cx (rdW W' mem').
Proof. intros cx W W' mem mem' ly' S' md' HAR K H. exact (s10_lt_img_kept B IMGS BSYM cx W' mem' (rdW W mem) HAR K H). Qed.

(* a range inside a live heap block is addressable, with its shadow words visible, at that state (the parse walk's
   sa_addr_of_heap, lib/A/Prog/reac_segconf_parse.v on the parser group's branch) *)
Lemma s17_addr_of_heap : forall ly S (W : world SEGS) mem md q n, AR SEGS B ly S W mem md -> sa_heap B ly S q n ->
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
Lemma s17_hblk_of : forall ly S (W : world SEGS) mem md rd q n, AR SEGS B ly S W mem md ->
  lt_hblk B ly S rd q n -> 0 < n -> lt_hblk B ly S (rdW W mem) q n.
Proof.
intros ly S W mem md rd q n HAR (Hin & H4 & H16 & _) Hn.
split; [exact Hin|]. split; [exact H4|]. split; [exact H16|].
exact (proj1 (s17_addr_of_heap ly S W mem md q n HAR ltac:(exists q, n; split; [exact Hin | lia]) ltac:(lia) Hn)).
Qed.

(* ---------------- the frame at a cut: where the side-stack frame and its shadow lie ---------------- *)
Lemma s17_frame_at : forall cx ly S (W : world SEGS) mem md k,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  frames S = [(3, x_fpos cx)] /\ frame_addr ly 3 (x_fpos cx) = x_fr cx /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512 /\ x_fr cx mod 32 = 0 /\
  x_sh cx = 2147450880 + x_fr cx / 8 /\
  (forall i, 0 <= i < 64 -> apresent (w_H W) mem (x_sh cx + i)) /\
  alloc_ceiling <= x_s1 cx /\ x_s1 cx + 320 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\
  x_s1 cx mod 32 = 0 /\ ly_stk_lo ly + STK_LLVMFuzzerTestOneInput <= x_sp0 cx.
Proof.
intros cx ly S W mem md k HBASE HJ.
pose proof HBASE as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & HFR0 & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _ & _ & _ & Hlo & _).
assert (Hfr : frames S = [(3, x_fpos cx)]) by (rewrite Hfrs, HFR0; reflexivity).
assert (HF : frame_addr ly 3 (x_fpos cx) = x_fr cx) by (unfold x_fr, frame_addr; rewrite HlyF; reflexivity).
assert (Hin : In (3, x_fpos cx) (frames S)) by (rewrite Hfr; left; reflexivity).
destruct (al_frames _ _ LAWS ly S W mem md 3 (x_fpos cx) HAR Hin) as (Hal32 & Happ & _ & Hsh).
rewrite HF in Hal32, Happ, Hsh.
change (fs_frame_bytes 3) with 512 in Happ, Hsh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold x_s1, x_sp0, STK_LLVMFuzzerTestOneInput in *.
pose proof (Z.mod_pos_bound (spZ (x_regs cx) - LT_FRAME) 32 ltac:(lia)) as M32.
split; [exact Hfr|]. split; [exact HF|].
split; [lia|]. split; [lia|]. split; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; lia|].
split; [exact Hal32|].
split; [unfold x_sh, shadow_addr, SHADOW_OFF; reflexivity|].
split; [intros i Hi; unfold x_sh; exact (proj1 (Hsh i ltac:(lia)))|].
unfold LT_FRAME. rewrite Hlo.
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hal16|].
split; [|lia].
rewrite Zminus_mod, Zmod_mod, Z.sub_diag. reflexivity.
Qed.

(* the s1 slots of the file loop lie at 8(s1) .. 184(s1) *)
Lemma s17_LT_L_off : forall cx c m o v, In (o, v) (LT_L cx c m) -> 8 <= o <= 184.
Proof.
intros cx c m o v Hin. unfold LT_L in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.
(* a 1-byte chunk whose value is the word -8 reads 0xf8 *)
Lemma s17_rd_f8 : forall (W : world SEGS) mem E base off e,
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 e)) ->
  sv_denot E e = Z_to_bv 64 (-8) -> rdW W mem (base + off) = Some 248.
Proof.
intros W mem E base off e Hc He. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2. rewrite He in Hb1. injection Hb1 as <-.
unfold aview. rewrite Z.add_0_r in Hb2. rewrite Hb2. cbn [option_map].
vm_compute. reflexivity.
Qed.
(* a window inside the frame's shadow is the walk's to write: its own class-3 frame *)
Lemma s17_awr_lbl : forall E cx ly r rs STK sp0 FP bl0 blc fr0,
  YP09.r_base r = Some 21%nat -> YP09.r_wlo r = 12 -> YP09.r_whi r = 17 -> bv_unsigned (ew E 21) = x_sh cx ->
  frame_addr ly 3 (x_fpos cx) = x_fr cx ->
  awr_ok SEGS B E rs STK sp0 FP bl0 blc fr0 ly [(LT_FCLS, x_fpos cx)] ->
  awr_ok SEGS B E (r :: rs) STK sp0 FP bl0 blc fr0 ly [(LT_FCLS, x_fpos cx)].
Proof.
intros E cx ly r rs STK sp0 FP bl0 blc fr0 Hb Hlo Hhi U21 HFA Hrs.
eapply awr_ok_cons_gen; [exact Hb | exact U21 | | exact Hrs].
intros a Ha. rewrite Hlo, Hhi in Ha.
right; right; right; left. exists 3, (x_fpos cx). split; [left; reflexivity|]. right.
unfold in_zr. cbn [fst snd]. rewrite HFA. change (fs_frame_bytes 3 / 8) with 64. unfold x_sh in Ha. lia.
Qed.

(* S08's cut facts: the label's five shadow bytes SH(FR) + 12 .. 16 are now 0xf8 and every other byte is as at
   K85414, so the frame holds the entry pattern LFO0 and the rest of the cut is carried *)
Lemma s17_core_label_out : forall cx ly S (W : world SEGS) regs mem md regs2 mem2 md2 k acc rem c m,
  lt_base B MT cx ->
  lt_core B MT cx ly S W regs mem md k acc rem LFO_L [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 12 <= a < x_sh cx + 17) -> rdW W mem2 a = rdW W mem a) ->
  (forall o, 12 <= o < 17 -> rdW W mem2 (x_sh cx + o) = Some 248) ->
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  forall st, lt_slots cx (rdW W mem) (LT_L cx c m) -> lt_cm (rdW W mem) c m st ->
  lt_core B MT cx ly S W regs2 mem2 md2 k acc rem LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem2) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem2) m seg_spec.SEG_M_SIZE /\
  lt_slots cx (rdW W mem2) (LT_L cx c m) /\ lt_cm (rdW W mem2) c m st.
Proof.
intros cx ly S W regs mem md regs2 mem2 md2 k acc rem c m HBASE HCORE HJ2 P2 P3 P4 P8 P9 KK W5 Hc Hm st SLOTS HCM.
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & SAVED & HD0 & HD8 & HD16 & HFLW & S176 & FSH) & HIMG & HBL & HBUD).
destruct (s17_frame_at cx ly S W mem md k HBASE HJ)
  as (Hfrs & HFA & F4096 & Fceil & Fapp & F32 & Esh & SHP & S1c & S1sp & SP47 & SP16 & S132 & STKlo).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ2) as HAR2.
(* the window lies in the frame's shadow: no stack, image, frame or heap byte is in it *)
assert (NWs : forall a, x_s1 cx <= a -> ~ (x_sh cx + 12 <= a < x_sh cx + 17)) by (intros a Ha; rewrite Esh; lia).
assert (NWi : forall a, a < kImgEnd -> ~ (x_sh cx + 12 <= a < x_sh cx + 17))
  by (intros a Ha; rewrite Esh; unfold kImgEnd in Ha; lia).
assert (NWa : forall p n a, in_app p n -> p <= a < p + n -> ~ (x_sh cx + 12 <= a < x_sh cx + 17)).
{ intros p n a Hin Ha Hw. rewrite Esh in Hw.
  exact (fshadow_not_app (x_fr cx) 64 p n a ltac:(lia) ltac:(lia) Hin ltac:(lia) Ha). }
assert (Kst : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W mem2 a = rdW W mem a)
  by (intros a Ha; apply KK; [lia | apply NWs; lia]).
assert (Kfr : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W mem2 a = rdW W mem a)
  by (intros a Ha; apply KK; [lia | exact (NWa _ _ a Fapp Ha)]).
assert (Kim : s17_ikeep (rdW W mem) (rdW W mem2)).
{ intros a Hia _ _. pose proof (pa_img_range a Hia) as Hr. apply KK; [unfold kImgEnd in Hr; lia | apply NWi; lia]. }
pose proof Hc as (Hinc & _ & _ & _). pose proof Hm as (Hinm & _ & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ c _ (proj1 HJ) Hinc) as (_ & Hc4 & Hcc & Hcapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ m _ (proj1 HJ) Hinm) as (_ & Hm4 & Hmc & Hmapp & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc, Hcapp.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc, Hmapp.
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in Hcc, Hmc.
split; [|split; [|split; [|split]]].
- split; [|split; [exact (s17_img_keep cx W W mem mem2 HAR2 Kim HIMG) | split; [exact HBL | exact HBUD]]].
  split; [exact HJ2|].
  split; [rewrite P2; exact Rsp|]. split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|].
  split; [rewrite P8; exact Rs0|]. split; [rewrite P9; exact Rs1|].
  split; [apply (s17_saved_xfer cx (rdW W mem)); [intros a Ha; apply Kst; lia | exact SAVED]|].
  split; [apply (s17_rdword_xfer (rdW W mem)); [intros q Hq; apply Kfr; lia | exact HD0]|].
  split; [apply (s17_rdword_xfer (rdW W mem)); [intros q Hq; apply Kfr; lia | exact HD8]|].
  split; [apply (s17_rdword_xfer (rdW W mem)); [intros q Hq; apply Kfr; lia | exact HD16]|].
  split; [apply (s17_rdword_xfer (rdW W mem)); [intros q Hq; apply Kfr; unfold LT_FLAGW; lia | exact HFLW]|].
  split; [apply (s17_rdword_xfer (rdW W mem)); [intros q Hq; apply Kst; lia | exact S176]|].
  intros i Hi. rewrite lt_fsh_len in Hi.
  destruct (Nat.ltb_spec i 12) as [Hlo|Hlo]; [|destruct (Nat.ltb_spec i 17) as [Hhi|Hhi]].
  + rewrite KK by (rewrite ?Esh; lia). rewrite (s17_fsh_same i Hi ltac:(lia)). apply FSH. rewrite lt_fsh_len. exact Hi.
  + rewrite (s17_fsh_f8 i ltac:(lia)). apply W5. lia.
  + rewrite KK by (rewrite ?Esh; lia). rewrite (s17_fsh_same i Hi ltac:(lia)). apply FSH. rewrite lt_fsh_len. exact Hi.
- exact (s17_hblk_of ly S W mem2 md2 _ c _ HAR2 Hc ltac:(unfold seg_spec.SEG_C_SIZE; lia)).
- exact (s17_hblk_of ly S W mem2 md2 _ m _ HAR2 Hm ltac:(unfold seg_spec.SEG_M_SIZE; lia)).
- apply (s17_slots_xfer cx (rdW W mem)); [|exact SLOTS].
  intros o v Hin q Hq. pose proof (s17_LT_L_off cx c m o v Hin). apply Kst. lia.
- destruct HCM as [HRC HMC]. split.
  + apply (s17_rconf_xfer (rdW W mem)); [|exact HRC].
    intros i Hi. unfold seg_spec.SEG_C_SIZE in Hi.
    apply KK; [lia | exact (NWa c seg_spec.SEG_C_SIZE (c + i) Hcapp ltac:(unfold seg_spec.SEG_C_SIZE; lia))].
  + apply (s17_mconf_xfer (rdW W mem)); [|exact HMC].
    intros i Hi. unfold seg_spec.SEG_M_SIZE in Hi.
    apply KK; [lia | exact (NWa m seg_spec.SEG_M_SIZE (m + i) Hmapp ltac:(unfold seg_spec.SEG_M_SIZE; lia))].
Qed.

Section s.
Context {fx : YK11.FPState}.
(* S08's seed at 0x85414: the five label shadow bytes SH(FR) + 12 .. 16 as a write window, the slot 168(s1) = m *)
Definition s8_rsh : YP09.region := YP09.mkRegion (Some 21%nat) 12 17 12 17 [].
Definition s8_rsl : YP09.region := YP09.mkRegion (Some 9%nat) 168 176 0 0 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))].
Definition s8_ss : sstate := mkSS LO_K85414 sr_atoms [s8_rsh; s8_rsl] None (mkFacts [] [] []).

(* what a plain run of S08 keeps: every byte outside the label's shadow window *)
Ltac s8_keep cx HFr U21 U9 K :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => x_sh cx + 12 <= a < x_sh cx + 17) HFr
    ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin';
          repeat (destruct Hin' as [Hq | Hin'];
                  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U21, ?U9 in Hrr; cbv beta; lia |]);
          destruct Hin')) as K.

Lemma lt_seg_S08 : lt_seg_S08_stmt (fx := fx) B MT.
Proof.
intros f HN HX. unfold LT_K85414_stmt.
intros cx ly S W regs mem md k acc c m HBASE HFRM Hf HCORE HBc HBm R18 R19 R20 R21 R22 R24 R25 R26 SLOTS HCM HCNT.
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & _) & _).
destruct (s17_frame_at cx ly S W mem md k HBASE HJ)
  as (Hfrs & HFA & F4096 & Fceil & Fapp & F32 & Esh & SHP & S1c & S1sp & SP47 & SP16 & S132 & STKlo).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (lt_nfiles_range (x_pl cx) : 1 <= x_nf cx <= 4) as NF.
pose proof (SLOTS 168 m ltac:(unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right]))) as SL168.
set (E := Eimg (Ereg regs [Z_to_bv 64 m])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 m)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), Rs1; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = x_sh cx)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; rewrite Esh; lia).
assert (D19 : sv_denot E (SOff 19 0) = Z_to_bv 64 (-8)).
{ cbn [sv_denot]. rewrite (EE 19%nat 19%bv eq_refl), R19, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (HS : st_ok_pi SEGS VAL E s8_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85414)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [s8_rsh s8_rsl YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U21. split; [lia|]. split; [rewrite Esh; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply SHP. lia.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. exact (s17_word_chunk W mem E 32 (x_s1 cx) 168 m SL168 E32).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map s8_rsh s8_rsl YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U21.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite Esh. repeat split; lia.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
assert (AWR0 : awr_ok SEGS B E (ss_mem s8_ss) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
  (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly S) (frames (x_S cx)) ly [(LT_FCLS, x_fpos cx)]).
{ unfold s8_ss. cbn [ss_mem].
  apply (s17_awr_lbl E cx ly s8_rsh [s8_rsl]); [reflexivity | reflexivity | reflexivity | exact U21 | exact HFA |].
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
unfold cfg_at. change (w64 (BASE + LO_K85414)) with (Z_to_bv 64 (BASE + LO_K85414)).
(* 0x85414 .. 0x8542c: the label's five shadow bytes := 0xf8 (sb s3 with s3 = -8), a1 := 168(s1) = m; it stops at
   the latch beq s2, s9 (0x8542c) *)
paj_run_sh (SRr_run_pi_AJ (fx := fx) B LAWS) HS HJ.
{ exact AWR0. }
cbn [ms_mem mkst] in HF, HFr, HG.
s8_keep cx HFr U21 U9 K1.
clear HF HFr HG. rename ms into ms1.
psrr_branch_pi (SRr_run_pi_AJ (fx := fx) B LAWS) (paj_branch (fx := fx) (PI := PI)) HS.
- (* taken: f + 1 = nfiles, out of the loop to 0x854a0 *)
  assert (Hlast : Z.of_nat (Datatypes.S f) = x_nf cx).
  { rewrite branch_eq_U in Hc.
    rewrite (U_atom E 18 (Z.of_nat (Datatypes.S f))), (U_atom E 25 (x_nf cx)) in Hc
      by first [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | rewrite (EE 25%nat 25%bv eq_refl); exact R25 | lia].
    apply Z.eqb_eq in Hc. exact Hc. }
  paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS HJ LO_K854a0.
  { apply (s10_awr_skel SEGS B E (ss_mem s8_ss)); [vm_compute; reflexivity | exact AWR0]. }
  s8_keep cx HFr U21 U9 K2.
  clear HF HFr HG.
  pose proof (st_ok_pi_region_nth E _ _ 0 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
  assert (W5 : forall o, 12 <= o < 17 -> rdW W (ms_mem ms) (x_sh cx + o) = Some 248).
  { destruct RG as (_ & _ & _ & RGc). cbn [YP09.r_base base_val YP09.r_chunks] in RGc. rewrite U21 in RGc.
    intros o Ho. assert (Ho' : o = 12 \/ o = 13 \/ o = 14 \/ o = 15 \/ o = 16) by lia.
    destruct Ho' as [-> | [-> | [-> | [-> | ->]]]];
      (eapply s17_rd_f8; [apply (proj1 (Forall_forall _ _) RGc); cbn [In]; repeat (first [left; reflexivity | right])
                         | exact D19]). }
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (11%bv : bv 5) P11. prreg HS (22%bv : bv 5) P22. prreg HS (26%bv : bv 5) P26.
  rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  rewrite (EE 22%nat 22%bv eq_refl) in P22. rewrite (EE 26%nat 26%bv eq_refl) in P26. rewrite E32 in P11.
  pmkst HS.
  destruct (s17_core_label_out cx ly S W regs mem md (ms_regs ms) (ms_mem ms) _ k acc _ c m HBASE HCORE HJ
    P2 P3 P4 P8 P9 ltac:(intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha Hn)) W5 HBc HBm _ SLOTS HCM)
    as (HCORE2 & Hc2 & Hm2 & SLOTS2 & HCM2).
  assert (EAF : x_af cx f = x_run cx) by (unfold x_af, x_run; apply s17_after_last; exact Hlast).
  rewrite EAF in HCM2, R22.
  assert (E6 : 6 + 2 * (x_nf cx - Z.of_nat (Datatypes.S f)) = 6) by lia. rewrite E6 in HCORE2.
  exact (HX fx cx ly S W _ _ _ k acc c m HBASE HFRM HCORE2 Hc2 Hm2 P11 ltac:(rewrite P22; exact R22)
    ltac:(rewrite P26; exact R26) SLOTS2 HCM2).
- (* not taken: the next turn f + 1 at 0x85024 (j at 0x85430) *)
  assert (Hnl : Z.of_nat (Datatypes.S f) <> x_nf cx).
  { rewrite branch_eq_U in Hc.
    rewrite (U_atom E 18 (Z.of_nat (Datatypes.S f))), (U_atom E 25 (x_nf cx)) in Hc
      by first [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | rewrite (EE 25%nat 25%bv eq_refl); exact R25 | lia].
    apply Z.eqb_neq in Hc. exact Hc. }
  paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS HJ LO_K85024.
  { apply (s10_awr_skel SEGS B E (ss_mem s8_ss)); [vm_compute; reflexivity | exact AWR0]. }
  s8_keep cx HFr U21 U9 K2.
  clear HF HFr HG.
  pose proof (st_ok_pi_region_nth E _ _ 0 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
  assert (W5 : forall o, 12 <= o < 17 -> rdW W (ms_mem ms) (x_sh cx + o) = Some 248).
  { destruct RG as (_ & _ & _ & RGc). cbn [YP09.r_base base_val YP09.r_chunks] in RGc. rewrite U21 in RGc.
    intros o Ho. assert (Ho' : o = 12 \/ o = 13 \/ o = 14 \/ o = 15 \/ o = 16) by lia.
    destruct Ho' as [-> | [-> | [-> | [-> | ->]]]];
      (eapply s17_rd_f8; [apply (proj1 (Forall_forall _ _) RGc); cbn [In]; repeat (first [left; reflexivity | right])
                         | exact D19]). }
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25.
  rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  rewrite (EE 18%nat 18%bv eq_refl) in P18. rewrite (EE 19%nat 19%bv eq_refl) in P19.
  rewrite (EE 20%nat 20%bv eq_refl) in P20. rewrite (EE 21%nat 21%bv eq_refl) in P21.
  rewrite (EE 22%nat 22%bv eq_refl) in P22. rewrite (EE 24%nat 24%bv eq_refl) in P24.
  rewrite (EE 25%nat 25%bv eq_refl) in P25.
  pmkst HS.
  destruct (s17_core_label_out cx ly S W regs mem md (ms_regs ms) (ms_mem ms) _ k acc _ c m HBASE HCORE HJ
    P2 P3 P4 P8 P9 ltac:(intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha Hn)) W5 HBc HBm _ SLOTS HCM)
    as (HCORE2 & Hc2 & Hm2 & SLOTS2 & HCM2).
  assert (EAF : x_af cx f = x_st cx (Datatypes.S f)) by (unfold x_af, x_st; apply s17_after_next; exact Hnl).
  rewrite EAF in HCM2, R22, HCNT.
  exact (HN fx cx ly S W _ _ _ k acc c m HBASE HFRM ltac:(lia) HCORE2 Hc2 Hm2
    ltac:(rewrite P18; exact R18) ltac:(rewrite P19; exact R19) ltac:(rewrite P20; exact R20)
    ltac:(rewrite P21; exact R21) ltac:(rewrite P22; exact R22) ltac:(rewrite P24; exact R24)
    ltac:(rewrite P25; exact R25) SLOTS2 HCM2 HCNT).
Qed.
End s.

(* ---- the values of the registers S07's run computes ---- *)
Lemma s17_den : forall E e v, U E e = v mod 2 ^ 64 -> sv_denot E e = w64 v.
Proof.
intros E e v H. apply bv_eq. unfold U in H. rewrite H. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
(* s6 := (a0 == sext32 (lw m->n)) & returned, with a0 = m->n = len *)
Lemma s17_s6 : forall E (b : bool) len,
  ew E 10 = Z_to_bv 64 len -> ew E 40 = Z_to_bv 64 len -> ew E 34 = Z_to_bv 64 (seg_spec.b2z b) ->
  0 <= len < 2 ^ 31 ->
  sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_XOR (SOff 10 0) (SExt true 32 (SOff 40 0))) (SLit 1))
    (SOff 34 0)) = w64 (seg_spec.b2z b).
Proof.
intros E b len H10 H40 H34 Hl. apply s17_den.
assert (Hb : 0 <= seg_spec.b2z b < 2 ^ 64) by (destruct b; cbn; lia).
rewrite !U_SAlu, U_SExt, U_SLit, (U_atom E 10 len H10 ltac:(lia)), (U_atom E 40 len H40 ltac:(lia)),
  (U_atom E 34 _ H34 Hb).
change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small len (2 ^ 32)) by lia. rewrite swrap32_id by lia. rewrite (zcanon_id len) by (unfold M64; lia).
cbn [zalu_raw]. rewrite Z.lxor_nilpotent.
destruct b; vm_compute; reflexivity.
Qed.
(* s4 := a0 - s11 (the mul by -1 and the add the compiler emits) *)
Lemma s17_s4 : forall E a b, ew E 27 = Z_to_bv 64 a -> ew E 38 = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 27 0) (SLit (-1))) (SOff 38 0)) = w64 (b - a).
Proof.
intros E a b H27 H38 Ha Hb. apply s17_den.
rewrite U_SAlu, U_SMd, U_SLit, (U_atom E 27 a H27 Ha), (U_atom E 38 b H38 Hb).
cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
rewrite Z.add_mod_idemp_l by lia.
change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (a * (2 ^ 64 - 1) + b) with ((b - a) + a * 2 ^ 64) by ring.
apply Z_mod_plus_full.
Qed.
(* s8 := s8 + s11 *)
Lemma s17_s8 : forall E a b, ew E 27 = Z_to_bv 64 a -> ew E 36 = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff 27 0) (SOff 36 0)) = w64 (b + a).
Proof.
intros E a b H27 H36 Ha Hb. apply s17_den.
rewrite U_SAlu, (U_atom E 27 a H27 Ha), (U_atom E 36 b H36 Hb).
cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.add_comm. reflexivity.
Qed.

(* ============================== S07 after the parse: 0x853c8 .. 0x85410 ============================== *)
(* a word chunk at an atom plus a constant *)
Lemma s17_word_chunk_off : forall (W : world SEGS) mem E (n : nat) base off d v,
  rdword (rdW W mem) (base + off) = Some v -> bv_unsigned (ew E n) + d = v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff n d))).
Proof.
intros W mem E n base off d v Hw He.
pose proof (s17_rdword_rng _ _ _ _ _ Hw) as Hr.
apply (chunk_ok_val SEGS E _ base off 8 (SOff n d) v);
  [cbn [sv_denot]; rewrite He; reflexivity | cbn; lia | cbn; lia |].
exact (val_mem_of_rdword SEGS _ _ _ _ Hw).
Qed.
(* the shadow byte of m + 0x2000 (m 16-aligned, its block 9236 bytes) is 0 *)
Lemma s17_sh_mn : forall (rd : reader) m, m mod 16 = 0 -> 0 <= m ->
  range_addressable rd SHADOW_OFF (m + 0x2007) 1 -> rd (shadow_addr (m + seg_spec.MC_N)) = Some 0.
Proof.
intros rd m Hm Hm0 HRA. destruct (HRA (m + 0x2007) ltac:(lia)) as (s0 & Hs0 & Hok).
pose proof (Z.div_mod m 16 ltac:(lia)) as D16. pose proof (Z.div_mod (m + 0x2007) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (m + 0x2007) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (m + 0x2000) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (m + 0x2000) 8 ltac:(lia)) as M2.
assert (E7 : (m + 0x2007) mod 8 = 7) by lia.
assert (Es : shadow_of_addr SHADOW_OFF (m + 0x2007) = shadow_addr (m + seg_spec.MC_N))
  by (unfold shadow_of_addr, shadow_addr, SHADOW_OFF, seg_spec.MC_N; lia).
rewrite Es in Hs0. rewrite Hs0. f_equal. destruct Hok as [Hok | Hok]; [exact Hok | lia].
Qed.

(* S07's seed at 0x853c8: the shadow byte SH(m + 0x2000) (base s2), the slots 88 .. 184 of s1, and m->n (base m) *)
Definition s7_rsh : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition s7_rsl : YP09.region := YP09.mkRegion (Some 9%nat) 88 192 0 0
  [YP09.mkChunk 88 (CVal 8 (SOff 32 0)); YP09.mkChunk 112 (CVal 8 (SOff 33 0)); YP09.mkChunk 120 (CVal 8 (SOff 34 0));
   YP09.mkChunk 128 (CVal 8 (SOff 35 0)); YP09.mkChunk 136 (CVal 8 (SOff 36 0)); YP09.mkChunk 144 (CVal 8 (SOff 37 0));
   YP09.mkChunk 152 (CVal 8 (SOff 38 0)); YP09.mkChunk 184 (CVal 8 (SOff 39 0x2000))].
Definition s7_rmn : YP09.region := YP09.mkRegion (Some 39%nat) 0x2000 0x2004 0 0
  [YP09.mkChunk 0x2000 (CVal 4 (SOff 40 0))].
Definition s7_ss : sstate := mkSS S17_PRA sr_atoms [s7_rsh; s7_rsl; s7_rmn] None (mkFacts [] [] []).

(* prreg without its normalization: the register as sv_denot of the run's symbolic value *)
Ltac s17_prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

Section s7a.
Context {fx : YK11.FPState}.
(* from the return of reac_segconf_parse (0x853c8) to K85414: check 18 (m->n's shadow byte, decided 0), returned
   &= (a0 == m->n), the registers of the next cut from the slots, and free(text) *)
Lemma s17_tail : forall f, LTA_K85414 B MT f ->
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f + 1 = x_nf cx ->
  lt_core B MT cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) -> getr regs 23 = w64 t ->
  getr regs 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f) ->
  getr regs 10 = w64 (Z.of_nat (length (mc_seg (seg_spec.seg_mc (x_af cx f))))) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++
    [(112, (m + seg_spec.MC_N) / 8); (120, seg_spec.b2z (seg_spec.seg_ret (x_st cx f))); (128, Z.of_nat f + 1);
     (136, seg_spec.seg_turn_at (x_pl cx) (x_p cx) f);
     (152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))]) ->
  lt_cm (rdW W mem) c m (x_af cx f) ->
  lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_af cx f)) (seg_spec.seg_mc (x_af cx f)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + S17_PRA)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros f HN cx ly S W regs mem md k acc c m t HBASE HFRM Hf HCORE R18 R23 R27 R10 SLOTS HCM HCNT.
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & _).
pose proof (proj1 HJ) as HAR.
pose proof (s17k_nums B MT cx HBASE) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (lt_nfiles_range (x_pl cx)) as NF.
destruct (s17k_blk_head B cx ly S W mem md t (x_tn cx f) _ HAR HBL) as (Htin & Ht0 & _).
destruct (s17k_blk_of B cx ly S W mem md (m, seg_spec.SEG_M_SIZE) _ HAR HBL ltac:(right; left; reflexivity))
  as (Hmin & Hm0).
destruct (s17k_blk B ly S W mem md m seg_spec.SEG_M_SIZE HAR Hmin ltac:(unfold seg_spec.SEG_M_SIZE; lia))
  as (Hm4 & Hm16 & Hmc & HmA & _).
destruct (s17k_frame_at B cx ly S W mem md k HJ) as (_ & _ & F4 & Fc & Fapp & _).
pose proof HCM as [HRC HMC].
destruct (s17k_rd_n _ m _ HMC) as (HRDN & HLEN32).
set (len := Z.of_nat (length (mc_seg (seg_spec.seg_mc (x_af cx f))))) in *.
assert (HSH0 : rdW W mem (shadow_addr (m + seg_spec.MC_N)) = Some 0).
{ pose proof (HmA (m + 0x2007) 1 ltac:(lia) ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as (_ & _ & _ & HRA & _).
  exact (s17_sh_mn _ m Hm16 ltac:(lia) HRA). }
assert (Esh : shadow_addr (m + seg_spec.MC_N) = 2147450880 + (m + 0x2000) / 8)
  by (unfold shadow_addr, seg_spec.MC_N; reflexivity).
pose proof (Z.div_pos (m + 0x2000) 8 ltac:(lia) ltac:(lia)) as Hdv.
pose proof (Z.div_le_upper_bound (m + 0x2000) 8 (m + 0x2000) ltac:(lia) ltac:(lia)) as Hdv2.
(* the slots the run loads *)
assert (SL : forall o v, In (o, v) (LT_L cx c m ++
    [(112, (m + seg_spec.MC_N) / 8); (120, seg_spec.b2z (seg_spec.seg_ret (x_st cx f))); (128, Z.of_nat f + 1);
     (136, seg_spec.seg_turn_at (x_pl cx) (x_p cx) f);
     (152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))]) -> rdword (rdW W mem) (x_s1 cx + o) = Some v)
  by exact SLOTS.
assert (SL88 : rdword (rdW W mem) (x_s1 cx + 88) = Some (x_nf cx))
  by (apply SL; apply in_or_app; left; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])).
assert (SL144 : rdword (rdW W mem) (x_s1 cx + 144) = Some (x_sh cx))
  by (apply SL; apply in_or_app; left; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])).
assert (SL184 : rdword (rdW W mem) (x_s1 cx + 184) = Some (m + seg_spec.MC_N))
  by (apply SL; apply in_or_app; left; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])).
assert (SL112 : rdword (rdW W mem) (x_s1 cx + 112) = Some ((m + seg_spec.MC_N) / 8))
  by (apply SL; apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right])).
assert (SL120 : rdword (rdW W mem) (x_s1 cx + 120) = Some (seg_spec.b2z (seg_spec.seg_ret (x_st cx f))))
  by (apply SL; apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right])).
assert (SL128 : rdword (rdW W mem) (x_s1 cx + 128) = Some (Z.of_nat f + 1))
  by (apply SL; apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right])).
assert (SL136 : rdword (rdW W mem) (x_s1 cx + 136) = Some (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f))
  by (apply SL; apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right])).
assert (SL152 : rdword (rdW W mem) (x_s1 cx + 152) = Some (Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f))))
  by (apply SL; apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right])).
pose proof (s17_rdword_rng _ _ _ _ _ SL88) as V88. pose proof (s17_rdword_rng _ _ _ _ _ SL112) as V112.
pose proof (s17_rdword_rng _ _ _ _ _ SL120) as V120. pose proof (s17_rdword_rng _ _ _ _ _ SL128) as V128.
pose proof (s17_rdword_rng _ _ _ _ _ SL136) as V136. pose proof (s17_rdword_rng _ _ _ _ _ SL144) as V144.
pose proof (s17_rdword_rng _ _ _ _ _ SL152) as V152.
set (vl := [x_nf cx; (m + seg_spec.MC_N) / 8; seg_spec.b2z (seg_spec.seg_ret (x_st cx f)); Z.of_nat f + 1;
  seg_spec.seg_turn_at (x_pl cx) (x_p cx) f; x_sh cx; Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)); m; len]).
set (E := Eimg (Ereg regs (map (Z_to_bv 64) vl))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EAx : forall j, (j < 9)%nat -> ew E (32 + j) = nth j (map (Z_to_bv 64) vl) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
pose proof (EAx 0%nat ltac:(lia)) as E32. pose proof (EAx 1%nat ltac:(lia)) as E33.
pose proof (EAx 2%nat ltac:(lia)) as E34. pose proof (EAx 3%nat ltac:(lia)) as E35.
pose proof (EAx 4%nat ltac:(lia)) as E36. pose proof (EAx 5%nat ltac:(lia)) as E37.
pose proof (EAx 6%nat ltac:(lia)) as E38. pose proof (EAx 7%nat ltac:(lia)) as E39.
pose proof (EAx 8%nat ltac:(lia)) as E40.
unfold vl in E32, E33, E34, E35, E36, E37, E38, E39, E40.
cbn [Nat.add nth map] in E32, E33, E34, E35, E36, E37, E38, E39, E40. clear EAx.
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
unfold seg_spec.SEG_M_SIZE in Hmc.
assert (U18 : bv_unsigned (ew E 18) = shadow_addr (m + seg_spec.MC_N))
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; rewrite Esh; lia).
assert (U39 : bv_unsigned (ew E 39) = m) by (rewrite E39; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E s7_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S17_PRA)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold region_ok;
      cbn [s7_rsh s7_rsl s7_rmn YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U18. split; [rewrite Esh; lia|]. split; [rewrite Esh; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (shadow_addr (m + seg_spec.MC_N)) 0 1 (SLit 0) 0);
        [reflexivity | cbn; lia | cbn; lia |].
      intros kk Hk. assert (kk = 0%nat) as -> by lia. rewrite !Z.add_0_r.
      destruct (aview_byte SEGS (w_H W) mem (shadow_addr (m + seg_spec.MC_N)) 0 HSH0) as (b & Hb & Hv & _).
      rewrite Hb. f_equal. apply bv_eq. rewrite <- Hv. vm_compute. reflexivity.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat (apply Forall_cons); try apply Forall_nil.
      * exact (s17_word_chunk W mem E 32 (x_s1 cx) 88 _ SL88 E32).
      * exact (s17_word_chunk W mem E 33 (x_s1 cx) 112 _ SL112 E33).
      * exact (s17_word_chunk W mem E 34 (x_s1 cx) 120 _ SL120 E34).
      * exact (s17_word_chunk W mem E 35 (x_s1 cx) 128 _ SL128 E35).
      * exact (s17_word_chunk W mem E 36 (x_s1 cx) 136 _ SL136 E36).
      * exact (s17_word_chunk W mem E 37 (x_s1 cx) 144 _ SL144 E37).
      * exact (s17_word_chunk W mem E 38 (x_s1 cx) 152 _ SL152 E38).
      * exact (s17_word_chunk_off W mem E 39 (x_s1 cx) 184 0x2000 _ SL184 ltac:(rewrite U39; reflexivity)).
    + rewrite U39. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ m 0x2000 4 (SOff 40 0) len);
        [cbn [sv_denot]; rewrite E40, Z.add_0_r; rewrite unsigned_lit_small by (unfold len; lia); reflexivity
        | cbn; unfold len; lia | cbn; lia |].
      exact (val_mem_of_rd32 SEGS _ _ _ _ HRDN).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map s7_rsh s7_rsl s7_rmn YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18, U39.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite Esh.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
(* 0x853c8 .. 0x85408: check 18 (lb SH(m + 0x2000) = 0, bnez not taken), a0 ^= lw m->n, seqz, s6 := that & 120(s1),
   s5 / s8 / s9 / s2 / a0 / s10 := the slots, s3 := -8, s8 += s11, s4 := a0 - s11; it stops at mv a0, s7 *)
paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS HJ S17_FREE.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_nil. }
cbn [ms_mem mkst] in HF, HFr, HG.
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr
  ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin';
        repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
        destruct Hin')) as KEEP0.
clear HF HFr HG.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
assert (KEEP : forall a, rdW W (ms_mem ms) a = rdW W mem a)
  by exact (s17k_keep_all (w_H W) mem (ms_mem ms) (fun a Ha => KEEP0 a Ha (fun Hff => Hff))).
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. s17_prreg_raw HS (20%bv : bv 5) P20.
prreg HS (21%bv : bv 5) P21. s17_prreg_raw HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. s17_prreg_raw HS (24%bv : bv 5) P24.
prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
(* the model: returned after the last turn, the cursor after it *)
destruct (s17k_last (x_pl cx) f ltac:(unfold x_nf in Hf; lia)) as (_ & _ & EM3 & _ & _).
change (seg_spec.seg_after (x_pl cx) f) with (x_af cx f) in EM3.
change (seg_spec.seg_run (x_pl cx) f) with (x_st cx f) in EM3.
destruct (s17k_cur_next (x_pl cx) (x_p cx) f) as (ECN & ECA).
change (seg_spec.seg_cur_n (x_pl cx) (Datatypes.S f)) with (x_curn cx (Datatypes.S f)) in ECN.
change (seg_spec.seg_cur_at (x_pl cx) (x_p cx) (Datatypes.S f)) with (x_cur cx (Datatypes.S f)) in ECA.
assert (Hnp : 0 <= seg_spec.seg_turn_np (x_pl cx) f <= Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f))).
{ split; [unfold seg_spec.seg_turn_np; lia|]. pose proof (Zle_0_nat (length (seg_spec.seg_cur (x_pl cx) (Datatypes.S f)))).
  unfold x_curn, seg_spec.seg_cur_n in ECN. lia. }
(* the registers of the free call and of K85414 *)
assert (Q2 : getr (ms_regs ms) 2 = w64 (x_s1 cx)) by (rewrite P2, (EE 2%nat 2%bv eq_refl); exact R2).
assert (Q3 : getr (ms_regs ms) 3 = getr (x_regs cx) 3) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact R3).
assert (Q4 : getr (ms_regs ms) 4 = getr (x_regs cx) 4) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact R4).
assert (Q8 : getr (ms_regs ms) 8 = w64 (x_sp0 cx)) by (rewrite P8, (EE 8%nat 8%bv eq_refl); exact R8).
assert (Q9 : getr (ms_regs ms) 9 = w64 (x_s1 cx)) by (rewrite P9, (EE 9%nat 9%bv eq_refl); exact R9).
assert (Q23 : getr (ms_regs ms) 23 = w64 t) by (rewrite P23, (EE 23%nat 23%bv eq_refl); exact R23).
assert (E27 : ew E 27 = Z_to_bv 64 (seg_spec.seg_turn_np (x_pl cx) f)) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (E10 : ew E 10 = Z_to_bv 64 len) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (Q18 : getr (ms_regs ms) 18 = w64 (Z.of_nat (Datatypes.S f)))
  by (rewrite P18, E35; unfold w64; f_equal; lia).
assert (Q19 : getr (ms_regs ms) 19 = w64 (-8)) by (rewrite P19; apply bv_eq; vm_compute; reflexivity).
assert (Q20 : getr (ms_regs ms) 20 = w64 (x_curn cx (Datatypes.S f))).
{ rewrite P20, ECN. exact (s17_s4 E _ _ E27 E38 ltac:(lia) ltac:(lia)). }
assert (Q21 : getr (ms_regs ms) 21 = w64 (x_sh cx)) by (rewrite P21, E37; reflexivity).
assert (Q22 : getr (ms_regs ms) 22 = w64 (seg_spec.b2z (seg_spec.seg_ret (x_af cx f)))).
{ rewrite P22, EM3. exact (s17_s6 E _ len E10 E40 E34 ltac:(unfold len; lia)). }
assert (Q24 : getr (ms_regs ms) 24 = w64 (x_cur cx (Datatypes.S f))).
{ rewrite P24, ECA. exact (s17_s8 E _ _ E27 E36 ltac:(lia) ltac:(lia)). }
assert (Q25 : getr (ms_regs ms) 25 = w64 (x_nf cx)) by (rewrite P25, E32; reflexivity).
assert (Q26 : getr (ms_regs ms) 26 = w64 ((m + seg_spec.MC_N) / 8)) by (rewrite P26, E33; reflexivity).
(* free(text) *)
destruct (s17k_bud_free B MT MTL cx ly S W (ms_mem ms) md1 k acc _ HBASE HJ HBUD ltac:(lia)) as (Hnev & MOK & HBUD').
destruct (s17k_blk_head B cx ly S W mem md t (x_tn cx f) _ HAR HBL) as (_ & _ & Htn).
destruct (s17k_blk_of B cx ly S W mem md (c, seg_spec.SEG_C_SIZE) _ HAR HBL ltac:(right; right; left; reflexivity))
  as (Hcin & Hc0).
apply (s17k_free (fx := fx) B MT (AFREE4 fx) TL cx ly S W (ms_regs ms) (ms_mem ms) md1 k t (x_tn cx f) _ HBASE HJ
  Q2 Q3 Q4 Q8 (s17_saved_xfer cx (rdW W mem) _ (fun a _ => KEEP a) HSV) Q23 Htin Ht0 Hnev MOK).
intros ly2 S2 W2 regs2 mem2 md2 HJ2 HP2 Hbl Hfr2 HK2 MLE HKB.
pose proof (proj1 HJ2) as HAR2.
assert (HBL2 : lt_blocks B cx ly2 S2 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)])
  by exact (s17k_perm_free _ _ _ _ _ HBL Hbl).
pose proof (HBUD' S2 MLE) as HBUD2.
replace (5 + 2 * (x_nf cx - Z.of_nat f) - 1) with (6 + 2 * (x_nf cx - Z.of_nat (Datatypes.S f))) in HBUD2 by lia.
assert (KALL : s17k_kept B cx W mem W2 mem2)
  by exact (s17k_kept_trans B cx W W W2 mem (ms_mem ms) mem2 (s17k_kept_all B cx W W mem (ms_mem ms) KEEP) HK2).
assert (FREGS : s17k_fregs regs regs2).
{ intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)).
  destruct Hr as [-> | [-> | [-> | [-> | ->]]]].
  - exact (eq_trans P2 (EE 2%nat 2%bv eq_refl)). - exact (eq_trans P3 (EE 3%nat 3%bv eq_refl)).
  - exact (eq_trans P4 (EE 4%nat 4%bv eq_refl)). - exact (eq_trans P8 (EE 8%nat 8%bv eq_refl)).
  - exact (eq_trans P9 (EE 9%nat 9%bv eq_refl)). }
assert (HCORE2 : lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT)
  (6 + 2 * (x_nf cx - Z.of_nat (Datatypes.S f))) LFO_L [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)])
  by exact (s17k_core_step B MT IMGS BSYM cx ly S W regs mem md k acc _ LFO_L _ ly2 S2 W2 regs2 mem2 md2 _ _ _ _
    HBASE HCORE HJ2 FREGS KALL HBL2 HBUD2).
assert (Hne_c : (c, seg_spec.SEG_C_SIZE) <> (t, x_tn cx f))
  by (intros E0; apply Htn; rewrite <- E0; right; left; reflexivity).
assert (Hne_m : (m, seg_spec.SEG_M_SIZE) <> (t, x_tn cx f))
  by (intros E0; apply Htn; rewrite <- E0; left; reflexivity).
assert (HCM2 : lt_cm (rdW W2 mem2) c m (x_af cx f)).
{ split.
  - apply (s17_rconf_xfer (rdW W mem)); [|exact HRC]. intros i Hi.
    rewrite (HKB c _ i Hcin Hne_c ltac:(rewrite (s17k_req seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)); lia)). apply KEEP.
  - apply (s17_mconf_xfer (rdW W mem)); [|exact HMC]. intros i Hi.
    rewrite (HKB m _ i Hmin Hne_m ltac:(rewrite (s17k_req seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)); lia)). apply KEEP. }
assert (HBIN : forall b, In b [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] -> In b (ablocks B ly2 S2))
  by (intros b Hb; exact (proj1 (s17k_blk_of B cx ly2 S2 W2 mem2 md2 b _ HAR2 HBL2 Hb))).
replace (S17_FREE + 8) with LO_K85414 by reflexivity.
exact (HN fx cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) c m HBASE HFRM ltac:(lia) HCORE2
  (s17k_hblk B ly2 S2 W2 mem2 md2 c _ HAR2 (HBIN _ ltac:(right; left; reflexivity)) ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  (s17k_hblk B ly2 S2 W2 mem2 md2 m _ HAR2 (HBIN _ ltac:(left; reflexivity)) ltac:(unfold seg_spec.SEG_M_SIZE; lia))
  (eq_trans (HP2 18 ltac:(unfold acallee_saved; lia)) Q18) (eq_trans (HP2 19 ltac:(unfold acallee_saved; lia)) Q19)
  (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) Q20) (eq_trans (HP2 21 ltac:(unfold acallee_saved; lia)) Q21)
  (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) Q22) (eq_trans (HP2 24 ltac:(unfold acallee_saved; lia)) Q24)
  (eq_trans (HP2 25 ltac:(unfold acallee_saved; lia)) Q25) (eq_trans (HP2 26 ltac:(unfold acallee_saved; lia)) Q26)
  (s17k_slots_kept B MT cx W W2 mem mem2 _ HBASE (fun o v Hin => SLOTS o v ltac:(apply in_or_app; left; exact Hin))
    (fun o v Hin => ltac:(pose proof (s17_LT_L_off cx c m o v Hin); lia)) KALL)
  HCM2 HCNT).
Qed.
End s7a.

(* S07's seed at 0x853bc: the slot 160(s1) = c *)
Definition s7_rc : YP09.region := YP09.mkRegion (Some 9%nat) 160 168 0 0 [YP09.mkChunk 160 (CVal 8 (SOff 32 0))].
Definition s7_ss0 : sstate := mkSS LO_K853bc sr_atoms [s7_rc] None (mkFacts [] [] []).
(* the slots of K853bc lie at 8(s1) .. 184(s1) *)
Lemma s17_L7_off : forall cx c m f o v, In (o, v) (LT_L cx c m ++
    [(112, (m + seg_spec.MC_N) / 8); (120, seg_spec.b2z (seg_spec.seg_ret (x_st cx f))); (128, Z.of_nat f + 1);
     (136, seg_spec.seg_turn_at (x_pl cx) (x_p cx) f);
     (152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))]) -> 0 <= o <= 312.
Proof.
intros cx c m f o v Hin. apply in_app_or in Hin as [Hin | Hin]; [pose proof (s17_LT_L_off cx c m o v Hin); lia|].
cbn [In] in Hin. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.

Section s7b.
Context {fx : YK11.FPState}.
Lemma lt_seg_S07 : lt_seg_S07_stmt (fx := fx) B MT.
Proof.
intros f HN. unfold LT_K853bc_stmt.
intros cx ly S W regs mem md k acc c m t HBASE HFRM Hf HCORE HBc HBm HBt R18 R23 R27 SLOTS HRC HMC HTXT HCNT.
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ0 & R2 & R3 & R4 & R8 & R9 & HSV & _).
pose proof (s17k_nums B MT cx HBASE) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (lt_nfiles_range (x_pl cx)) as NF.
pose proof (SLOTS 160 c ltac:(apply in_or_app; left; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])))
  as SL160.
set (E := Eimg (Ereg regs [Z_to_bv 64 c])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 c)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E s7_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K853bc)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [s7_rc YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. exact (s17_word_chunk W mem E 32 (x_s1 cx) 160 c SL160 E32).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map s7_rc YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
pose proof HJ0 as HJ.
unfold cfg_at. change (w64 (BASE + LO_K853bc)) with (Z_to_bv 64 (BASE + LO_K853bc)).
(* 0x853bc .. 0x853c4: a0 := 160(s1) = c, a1 := s7 = t, jal reac_segconf_parse *)
assert (SHOK : sh_ok SEGS S17x [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
pose proof (paj_run B LAWS) as RUN.
paj_run_tok RUN HS HJ SHOK s17k_span.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with
| HFr : frame_of ?E0 _ (mrestrict _ _) (mrestrict _ ?m1) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr
    ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin';
          repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
          destruct Hin')) as KEEP0
end.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
rewrite (SIGP SS_reac_segconf_parse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_parse) with AF_reac_segconf_parse by (vm_compute; reflexivity).
assert (KEEP : forall a, rdW W (ms_mem ms) a = rdW W mem a)
  by exact (s17k_keep_all (w_H W) mem (ms_mem ms) (fun a Ha => KEEP0 a Ha (fun Hff => Hff))).
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18. prreg HS (23%bv : bv 5) P23. prreg HS (27%bv : bv 5) P27.
assert (FREGSA : s17k_fregs regs (ms_regs ms)).
{ intros r Hr. destruct Hr as [-> | [-> | [-> | [-> | ->]]]].
  - exact (eq_trans P2 (EE 2%nat 2%bv eq_refl)). - exact (eq_trans P3 (EE 3%nat 3%bv eq_refl)).
  - exact (eq_trans P4 (EE 4%nat 4%bv eq_refl)). - exact (eq_trans P8 (EE 8%nat 8%bv eq_refl)).
  - exact (eq_trans P9 (EE 9%nat 9%bv eq_refl)). }
(* the cut at the call's state *)
assert (HCOREA : lt_core B MT cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
  [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)])
  by exact (s17k_core_step B MT IMGS BSYM cx ly S W regs mem md k acc _ LFO_L _ ly S W (ms_regs ms) (ms_mem ms) md1 _ _ _ _
    HBASE HCORE HJ FREGSA (s17k_kept_all B cx W W mem (ms_mem ms) KEEP) HBL HBUD).
pose proof HCOREA as ((_ & _ & _ & _ & _ & _ & HSVA & _) & (HROA & HHIA & _) & _ & _).
pose proof (proj1 HJ) as HARA.
assert (HRCA : sa_rconf (rdW W (ms_mem ms)) c (seg_spec.seg_rc (x_st cx f))) by exact (s17k_rconf_ext _ _ c _ KEEP HRC).
assert (HTXTA : sa_str (rdW W (ms_mem ms)) t (seg_spec.seg_txt (x_pl cx) f)) by exact (s17k_str_ext _ _ t _ KEEP HTXT).
destruct (s17k_blk_head B cx ly S W (ms_mem ms) md1 t (x_tn cx f) _ HARA HBL) as (Htin & Ht0 & Htn).
destruct (s17k_blk_of B cx ly S W (ms_mem ms) md1 (c, seg_spec.SEG_C_SIZE) _ HARA HBL ltac:(right; right; left; reflexivity))
  as (Hcin & Hc0).
destruct (s17k_blk_of B cx ly S W (ms_mem ms) md1 (m, seg_spec.SEG_M_SIZE) _ HARA HBL ltac:(right; left; reflexivity))
  as (Hmin & Hm0).
assert (Htn0 : 0 < x_tn cx f) by (unfold x_tn, seg_spec.seg_txt_n; lia).
destruct (s17k_blk B ly S W (ms_mem ms) md1 c seg_spec.SEG_C_SIZE HARA Hcin ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as (Hc4 & Hc16 & Hcc & HcA & _).
destruct (s17k_blk B ly S W (ms_mem ms) md1 t (x_tn cx f) HARA Htin Htn0) as (Ht4 & Ht16 & Htc & HtA & _).
assert (Hne_tc : (t, x_tn cx f) <> (c, seg_spec.SEG_C_SIZE)) by (intros E0; apply Htn; rewrite E0; right; left; reflexivity).
assert (Hne_mc : (m, seg_spec.SEG_M_SIZE) <> (c, seg_spec.SEG_C_SIZE)).
{ intros E0. injection E0 as _ E1. unfold seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE in E1. lia. }
pose proof (sep_blocks SEGS B LAWS ly S W (ms_mem ms) md1 t (x_tn cx f) c seg_spec.SEG_C_SIZE HARA Htin Hcin Hne_tc) as Dtc.
unfold zdisjoint in Dtc. cbn [fst snd] in Dtc.
rewrite (s17k_req _ Htn0), (s17k_req seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)) in Dtc.
assert (Etn : x_tn cx f = Z.of_nat (length (seg_spec.seg_txt (x_pl cx) f)) + 1) by reflexivity.
assert (Hc8 : c mod 8 = 0).
{ pose proof (Z.div_mod c 16 ltac:(lia)). pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)). lia. }
(* reac_segconf_parse's pre: reader_pre, the read-only view, cross_check's literals, the events *)
destruct HHIA as (_ & _ & _ & HLRC & HCAT & _ & _ & _ & HSSP & _).
pose proof (s17k_txt_len (x_pl cx) f) as HTL.
pose proof HCNT as (G1 & G2 & G3 & _).
assert (HRP : reader_pre SEGS B seg_litA_rc catA gotwA guardA ly S (rdW W (ms_mem ms)) c t
  (seg_spec.seg_rc (x_st cx f)) (seg_spec.seg_txt (x_pl cx) f)).
{ change (2 ^ 20) with 1048576 in G2, G3.
  assert (Hf4 : Z.of_nat f + 1 <= 4) by (unfold x_nf in Hf; lia).
  split; [lia|]. split; [exact Hc16|]. split; [exact HRCA|].
  split; [exists c, seg_spec.SEG_C_SIZE; split; [exact Hcin | lia]|].
  split; [apply HcA; lia|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [exact HTXTA|]. split; [apply Nat2Z.inj_le; exact HTL|].
  split; [exists t, (x_tn cx f); split; [exact Htin | lia]|].
  split; [apply HtA; lia|].
  split.
  { unfold sa_disj, seg_spec.cstr_span. rewrite Etn in Dtc. destruct Dtc as [D | D]; [left | right; lia].
    pose proof (s17k_up8 (t + Z.of_nat (length (seg_spec.seg_txt (x_pl cx) f)) + 1) c ltac:(lia) Hc8). lia. }
  split; [exact HFRM|]. split; [exact HSSP|]. split; [exact HCAT|].
  intros x Hx. exact (proj1 (HLRC x ltac:(apply in_or_app; left; exact Hx))). }
assert (HXL : forall x, In x CROSS_CHECK_LITS -> sa_lit SEGS B (rdW W (ms_mem ms)) (seg_litA_rc x) x)
  by (intros x Hx; exact (proj1 (HLRC x ltac:(apply in_or_app; right; exact Hx)))).
pose proof (s17k_nev B MT cx ly S W (ms_mem ms) md1 k acc _ HBASE HJ HBUD) as Hnev.
pose proof (s17_rdword_rng _ _ _ _ _ SL160) as Vc.
apply (s17k_parse (fx := fx) B MT HPARSE cx ly S W (ms_regs ms) (ms_mem ms) md1 k c t _ _ HBASE HJ
  (eq_trans P2 (eq_trans (EE 2%nat 2%bv eq_refl) R2)) (eq_trans P3 (eq_trans (EE 3%nat 3%bv eq_refl) R3))
  (eq_trans P4 (eq_trans (EE 4%nat 4%bv eq_refl) R4)) (eq_trans P8 (eq_trans (EE 8%nat 8%bv eq_refl) R8))
  HSVA ltac:(rewrite P1; reflexivity) ltac:(rewrite P10, E32; reflexivity)
  ltac:(rewrite P11, (EE 23%nat 23%bv eq_refl); exact R23) ltac:(lia) ltac:(lia) Hcin Hc0 HROA HRP HXL Hnev).
intros fx1 ly2 S2 W2 regs2 mem2 md2 H01 HJ2 HP2 HK2 HKB R10' HRC2 HNA.
destruct HNA as (HPm & -> & (fsf & ->)).
(* the model after the parse *)
destruct (s17k_last (x_pl cx) f ltac:(unfold x_nf in Hf; lia)) as (EM1 & EM2 & _ & EM4 & EM5).
change (seg_spec.seg_after (x_pl cx) f) with (x_af cx f) in EM1, EM2, EM4, EM5.
change (seg_spec.seg_run (x_pl cx) f) with (x_st cx f) in EM1, EM2, EM4.
rewrite EM4 in R10'.
assert (HCORE2 : lt_core B MT cx ly (set_fs fsf S) W2 regs2 mem2 md2 k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
  [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)])
  by exact (s17k_core_step B MT IMGS BSYM cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc _ LFO_L _ ly (set_fs fsf S) W2 regs2
    mem2 md2 _ _ _ _ HBASE HCOREA HJ2 (s17k_fregs_of_pres _ _ HP2) HK2 (Permutation_trans HPm HBL)
    (s17k_bud_noalloc MT MTFL cx S k acc _ fsf HBUD)).
assert (SLOTSA : lt_slots cx (rdW W (ms_mem ms)) (LT_L cx c m ++
    [(112, (m + seg_spec.MC_N) / 8); (120, seg_spec.b2z (seg_spec.seg_ret (x_st cx f))); (128, Z.of_nat f + 1);
     (136, seg_spec.seg_turn_at (x_pl cx) (x_p cx) f);
     (152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))]))
  by exact (s17k_slots_kept B MT cx W W mem (ms_mem ms) _ HBASE SLOTS (s17_L7_off cx c m f)
    (s17k_kept_all B cx W W mem (ms_mem ms) KEEP)).
assert (HCM2 : lt_cm (rdW W2 mem2) c m (x_af cx f)).
{ split; [rewrite EM1; exact HRC2|]. rewrite EM2.
  apply (s17_mconf_xfer (rdW W mem)); [|exact HMC]. intros i Hi.
  rewrite (HKB m _ i Hmin Hne_mc ltac:(rewrite (s17k_req seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)); lia)).
  apply KEEP. }
rewrite <- EM2 in HCNT.
exact (s17_tail (fx := fx1) f HN cx ly (set_fs fsf S) W2 regs2 mem2 md2 k acc c m t HBASE
  (fxrel_frm0 fx fx1 HFRM H01) Hf HCORE2
  (eq_trans (HP2 18 ltac:(unfold acallee_saved; lia)) (eq_trans P18 (eq_trans (EE 18%nat 18%bv eq_refl) R18)))
  (eq_trans (HP2 23 ltac:(unfold acallee_saved; lia)) (eq_trans P23 (eq_trans (EE 23%nat 23%bv eq_refl) R23)))
  (eq_trans (HP2 27 ltac:(unfold acallee_saved; lia)) (eq_trans P27 (eq_trans (EE 27%nat 27%bv eq_refl) R27)))
  R10' (s17k_slots_kept B MT cx W W2 (ms_mem ms) mem2 _ HBASE SLOTSA (s17_L7_off cx c m f) HK2)
  HCM2 (s17k_cnt _ _ _ _ EM5 HCNT)).
Qed.
End s7b.
End e.
End f.
End d.
