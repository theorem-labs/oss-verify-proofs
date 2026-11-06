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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 685 of its 735 lines of code are new or changed and 403 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the kit of the walk
   of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0), segments S07 (0x854d4 .. 0x8552c:
   reac_segconf_parse, check 17, free(text)) and S08 (0x85530 .. 0x85554: the label out of scope and the latch).
   The segment lemmas are in LLVMFuzzerTestOneInput_s17.v.

   proves function LLVMFuzzerTestOneInput (reuse search, rule 24: released units, the earlier proof delivery and working
   heads; the result is recorded with the commissioning brief; none: written new)

   This file holds:
   - the model's part (no machine): the reader's and the model's states after f turns are related by SegModel's
     conf_rel (SegModel.file_rel turn by turn), the last turn's state (SegModel.r_parse against m_cross, so the
     reader's count equals m->n and `returned` is kept), the next turn's state, SegModel.run as the state after the
     last turn, and the next turn's cursor;
   - the facts of a point of the walk carried across a call or a run (the image facts from image B's record
     SegRecBase.seg_img_facts, one Section hypothesis, the frame part, the blocks), in the form of image A's
     S01 / S02 kit (image A's S01 / S02 commit 119b28fad68f, LLVMFuzzerTestOneInput_s12k.v lk_* lemmas) and its
     S00 kit (image A's S00 commit 52ff1753c784, LLVMFuzzerTestOneInput_s10k.v s10_lt_img_kept);
   - the readers of a symbolic state at a cut (the S00 walk's s10_rd_chunk8 / s10_zs_ok).
   Statement text and proofs only about the walk's own points: no other function of the binary is proved here. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa
  SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require m_file_c SegRecBase SegRecCells.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ===================================== the model's part (no machine) ===================================== *)
(* every input byte is a byte value *)
Lemma s17_in_ok : forall pl, Forall SegModel.byte_ok (seg_spec.seg_in pl).
Proof.
intros pl. unfold seg_spec.seg_in, seg_spec.zs. apply Forall_forall. intros z Hz.
apply in_map_iff in Hz as (b & <- & _). unfold SegModel.byte_ok.
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.
(* every file record a turn reads, and the default record past the last one, is well formed *)
Lemma s17_file_ok : forall pl k, SegModel.file_ok (seg_spec.seg_file pl k).
Proof.
intros pl k. unfold seg_spec.seg_file.
destruct (Nat.lt_ge_cases k (length (seg_spec.seg_files pl))) as [H|H].
- apply (proj1 (Forall_forall _ _) (proj1 (SegModel.decode_ok _ (s17_in_ok pl)))). apply nth_In. exact H.
- rewrite nth_overflow by exact H. unfold SegModel.file_ok. cbn [SegModel.f_text SegModel.f_lb length].
  split; [apply SegModel.nulfree_nil | split; lia].
Qed.
Lemma s17_txt_ok : forall pl k,
  SegModel.nulfree (seg_spec.seg_txt pl k) /\ Z.of_nat (length (seg_spec.seg_txt pl k)) <= 65535 /\
  0 <= seg_spec.seg_lb pl k < 256.
Proof. intros pl k. exact (s17_file_ok pl k). Qed.
(* decode builds as many files as its count byte asks: 1 + in[2] % 4, between 1 and 4 (the base's
   LLVMFuzzerTestOneInput_s02.v dec_files_length / lt_nfiles_range, restated here) *)
Lemma s17_dec_files_length : forall k i, length (SegModel.dec_files k i) = k.
Proof.
induction k as [|k IH]; intros i; cbn [SegModel.dec_files]; [reflexivity|].
destruct (SegModel.fuzz_u8 i) as [lb i1]. destruct (SegModel.fuzz_u16 i1) as [len i2].
destruct (SegModel.fuzz_take i2 len) as [p i3]. cbn [length]. rewrite IH. reflexivity.
Qed.
Lemma s17_nfiles_range : forall pl, 1 <= seg_spec.seg_nfiles pl <= 4.
Proof.
intros pl. unfold seg_spec.seg_nfiles, seg_spec.seg_files, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_files]. rewrite s17_dec_files_length.
pose proof (Z.mod_pos_bound b2 4 ltac:(lia)) as H. rewrite Z2Nat.id by lia. lia.
Qed.

(* the reader's state and the model's state after k turns are related (SegModel.file_rel per turn) *)
Lemma s17_run_rel : forall pl k,
  SegModel.conf_rel (seg_spec.seg_rc (seg_spec.seg_run pl k)) (seg_spec.seg_mc (seg_spec.seg_run pl k)).
Proof.
intros pl k. induction k as [|k IH]; cbn [seg_spec.seg_run].
- exact SegModel.conf_rel0.
- unfold seg_spec.seg_turn_step.
  destruct (seg_spec.seg_run pl k) as [[c mc] ret]. cbn [seg_spec.seg_rc seg_spec.seg_mc fst snd] in IH.
  destruct (s17_txt_ok pl k) as (Hn & Hl & Hlb).
  pose proof (SegModel.file_rel c mc (seg_spec.seg_txt pl k) (seg_spec.seg_label pl k) (seg_spec.seg_label pl k)
    IH Hn Hl eq_refl (SegModel.rd_label_ok _ Hlb)) as H.
  cbv zeta iota beta.
  revert H. destruct (SegModel.r_parse_file c (seg_spec.seg_txt pl k) (seg_spec.seg_label pl k)) as [c1 n].
  cbn [fst snd seg_spec.seg_rc seg_spec.seg_mc]. intros (H1 & _ & _). exact H1.
Qed.

(* the last turn (f + 1 = nfiles): the reader's parse (reac_segconf_parse = parse_file under "reac-pw.conf", then
   cross_check) against m_cross of m_file; its count is m->n, so `returned` is kept *)
Lemma s17_last : forall pl f, Z.of_nat (Datatypes.S f) = seg_spec.seg_nfiles pl ->
  seg_spec.seg_after pl f =
    (fst (SegModel.r_parse (seg_spec.seg_rc (seg_spec.seg_run pl f)) (seg_spec.seg_txt pl f)),
     SegModel.m_cross (SegModel.m_file (seg_spec.seg_mc (seg_spec.seg_run pl f)) (seg_spec.seg_txt pl f) None),
     seg_spec.seg_ret (seg_spec.seg_run pl f)) /\
  snd (SegModel.r_parse (seg_spec.seg_rc (seg_spec.seg_run pl f)) (seg_spec.seg_txt pl f)) =
    Z.of_nat (length (SegModel.mc_seg
      (SegModel.m_cross (SegModel.m_file (seg_spec.seg_mc (seg_spec.seg_run pl f)) (seg_spec.seg_txt pl f) None)))) /\
  SegModel.conf_rel (fst (SegModel.r_parse (seg_spec.seg_rc (seg_spec.seg_run pl f)) (seg_spec.seg_txt pl f)))
    (SegModel.m_cross (SegModel.m_file (seg_spec.seg_mc (seg_spec.seg_run pl f)) (seg_spec.seg_txt pl f) None)).
Proof.
intros pl f Hf. pose proof (s17_run_rel pl f) as IH.
destruct (s17_txt_ok pl f) as (Hn & Hl & _).
unfold seg_spec.seg_after. rewrite Hf, Z.eqb_refl. unfold seg_spec.seg_turn_step.
destruct (seg_spec.seg_run pl f) as [[c mc] ret]. cbn [seg_spec.seg_rc seg_spec.seg_mc seg_spec.seg_ret fst snd] in *.
pose proof (SegModel.file_rel c mc (seg_spec.seg_txt pl f) (Some SegModel.S_base) None IH Hn Hl eq_refl
  ltac:(rewrite SegModel.rd_base; exact SegModel.rd_base_ok)) as (H1 & H2 & H3).
cbv zeta iota beta. unfold SegModel.r_parse.
revert H1 H2. destruct (SegModel.r_parse_file c (seg_spec.seg_txt pl f) (Some SegModel.S_base)) as [c1 n].
cbv beta iota. cbn [fst snd]. intros H1 H2.
rewrite SegModel.m_cross_len.
split; [rewrite <- H2, Z.eqb_refl, andb_true_r; reflexivity|]. split; [exact H2|].
apply SegModel.cross_rel; [exact H1 | rewrite H3; exact SegModel.rd_base].
Qed.

(* a turn that is not the last: the state after it is the state the next turn starts from *)
Lemma s17_next : forall pl f, Z.of_nat (Datatypes.S f) < seg_spec.seg_nfiles pl ->
  seg_spec.seg_run pl (Datatypes.S f) = seg_spec.seg_after pl f.
Proof.
intros pl f Hf. unfold seg_spec.seg_after. cbn [seg_spec.seg_run].
replace (Z.of_nat (Datatypes.S f) =? seg_spec.seg_nfiles pl) with false by (symmetry; apply Z.eqb_neq; lia).
reflexivity.
Qed.

(* SegModel.run walks the files as the turns do: the whole run is the state after the last turn *)
Lemma s17_run_files_step : forall pl k (c : SegModel.rconf) mc ret,
  (Datatypes.S k < length (seg_spec.seg_files pl))%nat ->
  SegModel.run_files (skipn k (seg_spec.seg_files pl)) c mc ret =
  let '(c', mc', ret') := seg_spec.seg_turn_step pl k false (c, mc, ret) in
  SegModel.run_files (skipn (Datatypes.S k) (seg_spec.seg_files pl)) c' mc' ret'.
Proof.
intros pl k c mc ret Hk.
assert (E1 : skipn k (seg_spec.seg_files pl) =
  nth k (seg_spec.seg_files pl) (SegModel.File 0 []) :: skipn (Datatypes.S k) (seg_spec.seg_files pl)).
{ revert Hk. generalize (seg_spec.seg_files pl) as L. clear. intros L. revert k.
  induction L as [|x l IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth length] in *. apply IH. lia. }
assert (E2 : exists x l, skipn (Datatypes.S k) (seg_spec.seg_files pl) = x :: l).
{ destruct (skipn (Datatypes.S k) (seg_spec.seg_files pl)) as [|x l] eqn:E.
  - exfalso. pose proof (length_skipn (Datatypes.S k) (seg_spec.seg_files pl)) as L. rewrite E in L. cbn in L. lia.
  - exists x, l. reflexivity. }
rewrite E1. destruct E2 as (x & l & E2). rewrite E2.
unfold seg_spec.seg_turn_step, seg_spec.seg_txt, seg_spec.seg_label, seg_spec.seg_lb, seg_spec.seg_file.
cbn [SegModel.run_files]. cbv beta iota zeta.
lazymatch goal with |- context [SegModel.r_parse_file ?a ?b ?cc] => destruct (SegModel.r_parse_file a b cc) end.
reflexivity.
Qed.
Lemma s17_run_files_at : forall pl k, (k < length (seg_spec.seg_files pl))%nat ->
  SegModel.run (seg_spec.seg_pay pl) =
  SegModel.run_files (skipn k (seg_spec.seg_files pl)) (seg_spec.seg_rc (seg_spec.seg_run pl k))
    (seg_spec.seg_mc (seg_spec.seg_run pl k)) (seg_spec.seg_ret (seg_spec.seg_run pl k)).
Proof.
intros pl k. induction k as [|k IH]; intros Hk; [reflexivity|].
rewrite IH by lia. cbn [seg_spec.seg_run].
destruct (seg_spec.seg_run pl k) as [[c mc] ret] eqn:Er. cbn [seg_spec.seg_rc seg_spec.seg_mc seg_spec.seg_ret fst snd].
rewrite (s17_run_files_step pl k c mc ret Hk).
destruct (seg_spec.seg_turn_step pl k false (c, mc, ret)) as [[c' mc'] ret']. reflexivity.
Qed.
Lemma s17_run_end : forall pl f, Z.of_nat (Datatypes.S f) = seg_spec.seg_nfiles pl ->
  SegModel.run (seg_spec.seg_pay pl) = seg_spec.seg_after pl f.
Proof.
intros pl f Hf. unfold seg_spec.seg_nfiles in Hf.
assert (Hk : (f < length (seg_spec.seg_files pl))%nat) by lia.
rewrite (s17_run_files_at pl f Hk).
assert (E1 : skipn f (seg_spec.seg_files pl) = [nth f (seg_spec.seg_files pl) (SegModel.File 0 [])]).
{ assert (Hl : length (seg_spec.seg_files pl) = Datatypes.S f) by lia. clear Hk Hf. revert f Hl.
  induction (seg_spec.seg_files pl) as [|x l IH]; intros f Hl; [cbn in Hl; lia|].
  destruct f as [|f]; cbn [length] in Hl.
  - destruct l; [reflexivity | cbn in Hl; lia].
  - cbn [skipn nth]. apply IH. lia. }
rewrite E1. unfold seg_spec.seg_after. replace (Z.of_nat (Datatypes.S f) =? seg_spec.seg_nfiles pl) with true
  by (symmetry; apply Z.eqb_eq; unfold seg_spec.seg_nfiles; lia).
unfold seg_spec.seg_turn_step, seg_spec.seg_txt, seg_spec.seg_file.
destruct (seg_spec.seg_run pl f) as [[c mc] ret]. cbn [seg_spec.seg_rc seg_spec.seg_mc seg_spec.seg_ret fst snd].
cbn [SegModel.run_files]. cbv zeta. reflexivity.
Qed.

(* the counters' bounds of a reader state related to a model state follow from the model state's *)
Lemma s17_cnt_rel : forall f (rc rc' : SegModel.rconf) (mc : SegModel.mconf),
  SegModel.conf_rel rc' mc -> lt_cnt f rc mc -> lt_cnt f rc' mc.
Proof.
intros f rc rc' mc (_ & _ & _ & Hov & Href & _ & _ & Hgen) (C1 & C2 & C3 & C4 & C5 & C6).
unfold lt_cnt. rewrite Hov, Href, Hgen. repeat split; assumption.
Qed.

(* ---- the next turn's cursor (image A's S05 kit, LLVMFuzzerTestOneInput_s15k.v s5_cur_S and its lemmas) ---- *)
Definition s17_next_cur (l : list Z) : list Z :=
  snd (SegModel.fuzz_take
    (snd (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 l))))
    (fst (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 l))))).
Lemma s17_take_fst : forall l n, fst (SegModel.fuzz_take l n) = firstn (Nat.min (Z.to_nat n) (length l)) l.
Proof. intros l n. reflexivity. Qed.
Lemma s17_take_snd : forall l n, snd (SegModel.fuzz_take l n) = skipn (Nat.min (Z.to_nat n) (length l)) l.
Proof. intros l n. reflexivity. Qed.
Lemma s17_skip_S : forall k l, seg_spec.seg_skip (Datatypes.S k) l = seg_spec.seg_skip k (s17_next_cur l).
Proof.
intros k l. cbn [seg_spec.seg_skip]. unfold s17_next_cur.
destruct (SegModel.fuzz_u8 l) as [b i1]. cbn [fst snd].
destruct (SegModel.fuzz_u16 i1) as [len i2]. cbn [fst snd].
destruct (SegModel.fuzz_take i2 len) as [p i3]. cbn [fst snd]. reflexivity.
Qed.
Lemma s17_skip_S' : forall f h, seg_spec.seg_skip (Datatypes.S f) h = s17_next_cur (seg_spec.seg_skip f h).
Proof.
induction f as [|f IH]; intros h.
- rewrite (s17_skip_S 0 h). cbn [seg_spec.seg_skip]. reflexivity.
- rewrite (s17_skip_S (Datatypes.S f) h), (IH (s17_next_cur h)), <- (s17_skip_S f h). reflexivity.
Qed.
Lemma s17_cur_S : forall pl f,
  seg_spec.seg_cur pl (Datatypes.S f) =
  skipn (Z.to_nat (seg_spec.seg_turn_np pl f)) (seg_spec.seg_turn_tail pl f) /\
  (Z.to_nat (seg_spec.seg_turn_np pl f) <= length (seg_spec.seg_turn_tail pl f))%nat.
Proof.
intros pl f.
unfold seg_spec.seg_turn_np, seg_spec.seg_turn_tail, seg_spec.seg_turn_len, seg_spec.seg_cur.
rewrite s17_skip_S'. unfold s17_next_cur.
rewrite s17_take_snd, s17_take_fst, length_firstn, Nat2Z.id. split; [f_equal; lia | lia].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the cursor after turn f + 1, against the slots the last turn keeps (144: P1 + NP, 160: N1, 152: NP) *)
Lemma s17_x_cur_S : forall cx f,
  x_cur cx (Datatypes.S f) = x_at cx f + x_np cx f /\ x_curn cx (Datatypes.S f) = x_n1 cx f - x_np cx f.
Proof.
intros cx f. destruct (s17_cur_S (x_pl cx) f) as [E L].
unfold x_cur, x_curn, x_at, x_np, x_n1, seg_spec.seg_cur_at, seg_spec.seg_cur_n, seg_spec.seg_turn_at.
rewrite E, length_skipn.
assert (Hnp : 0 <= seg_spec.seg_turn_np (x_pl cx) f)
  by (unfold seg_spec.seg_turn_np; lia).
split; lia.
Qed.

(* ===================================== readers of a symbolic state ===================================== *)
(* a register that holds an atom (the S00 walk's s10_reg_atom) *)
Lemma s17_reg_atom : forall (H : word -> bool) E ss ms (r : bv 5) n,
st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros H E ss ms r n HS Hr. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* an 8-byte chunk of a region (the S00 walk's s10_rd_chunk8) *)
Lemma s17_rd_chunk8 : forall E H mem base off a e v cs,
Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> In (YP09.mkChunk off (CVal 8 e)) cs ->
a = base + off -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros E H mem base off a e v cs Hc Hin -> He Hv. rewrite Forall_forall in Hc. specialize (Hc _ Hin).
apply rdword_of_val_mem; [|exact Hv].
apply (val_of_chunk_ok SEGS E _ base off 8 e v Hc He); [exact Hv | cbn; lia].
Qed.
(* 1-byte literal chunks, found by a boolean check (the S00 walk's s10_c1 / s10_lit1 / s10_zs_b / s10_zs_ok) *)
Definition s17_c1 (c : YP09.chunk) (off : Z) : option Z :=
match c with
| YP09.mkChunk o (CVal w (SLit z)) =>
  if (Z.eqb o off && N.eqb w 1)%bool then Some (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0)) else None
| _ => None
end.
Fixpoint s17_lit1 (cs : list YP09.chunk) (off : Z) : option Z :=
match cs with
| [] => None
| c :: cs' => match s17_c1 c off with Some v => Some v | None => s17_lit1 cs' off end
end.
Fixpoint s17_zs_b (cs : list YP09.chunk) (off : Z) (l : list Z) : bool :=
match l with
| [] => true
| x :: l' => match s17_lit1 cs off with Some v => Z.eqb v x && s17_zs_b cs (off + 1) l' | None => false end
end.
Lemma s17_lit1_in : forall cs off v, s17_lit1 cs off = Some v ->
exists z, In (YP09.mkChunk off (CVal 1 (SLit z))) cs /\ v = bv_unsigned (byte_of_word (Z_to_bv 64 z) 0).
Proof.
induction cs as [|c cs IH]; intros off v H; cbn [s17_lit1] in H; [discriminate H|].
destruct (s17_c1 c off) as [v'|] eqn:Ec.
- injection H as <-. destruct c as [o cv]. destruct cv as [w e| len | len | d s len]; cbn [s17_c1] in Ec;
  try discriminate Ec.
  destruct e; try discriminate Ec.
  destruct ((o =? off) && (w =? 1)%N)%bool eqn:Eb; [|discriminate Ec].
  apply andb_prop in Eb as [E1 E2]. apply Z.eqb_eq in E1. apply N.eqb_eq in E2. subst o w.
  injection Ec as <-. exists z. split; [left; reflexivity | reflexivity].
- destruct (IH off v H) as (z & Hin & Hv). exists z. split; [right; exact Hin | exact Hv].
Qed.
Lemma s17_zs_one : forall E H mem base cs off v,
Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> s17_lit1 cs off = Some v ->
aview SEGS H mem (base + off) = Some v.
Proof.
intros E H mem base cs off v Hc Ev.
destruct (s17_lit1_in cs off v Ev) as (z & Hin & ->).
rewrite Forall_forall in Hc. destruct (Hc _ Hin 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val YP09.cbyte sv_denot] in Hb1, Hb2. injection Hb1 as <-.
rewrite Z.add_0_r in Hb2. unfold aview. rewrite Hb2. reflexivity.
Qed.

(* ===================================== the kit's machine lemmas ===================================== *)
(* blocks_bytes is the sum of the live blocks' sizes (image A's S01 / S02 kit lk_bsum) *)
Fixpoint s17_bsum (bl : list (Z * Z)) : Z := match bl with [] => 0 | b :: l => snd b + s17_bsum l end.
Lemma s17_bsum_app : forall l1 l2, s17_bsum (l1 ++ l2) = s17_bsum l1 + s17_bsum l2.
Proof. induction l1 as [|b l IH]; intros l2; cbn [s17_bsum app]; [reflexivity | rewrite IH; ring]. Qed.
Lemma s17_bsum_perm : forall l1 l2, Permutation l1 l2 -> s17_bsum l1 = s17_bsum l2.
Proof. intros l1 l2 H. induction H; cbn [s17_bsum]; [reflexivity | rewrite IHPermutation; reflexivity | ring | congruence]. Qed.
Lemma s17_blocks_bytes : forall B ly S, blocks_bytes S = s17_bsum (ablocks B ly S).
Proof.
intros B ly S. unfold blocks_bytes, ablocks, blocks. induction (st_chunks S) as [|c cs IH]; [reflexivity|].
cbn [fold_right List.filter]. destruct (is_alloc c); cbn [map s17_bsum snd fst]; [rewrite IH; reflexivity | exact IH].
Qed.
(* a callee-saved register a call keeps *)
Lemma s17_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
(* a word every byte of which two readers agree on *)
Lemma s17_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
(* the frame address of a journal's target layout is the entry's *)
Lemma s17_frame_addr : forall B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof.
intros B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.
(* no block is live twice: the blocks are pairwise apart (AR_sep_law) and each has a byte *)
Lemma s17_pairwise_nodup : forall (l : list (Z * Z)),
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> (forall x, In x l -> 0 <= snd x) -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hp Hn; [constructor|]. cbn [map pairwise] in Hp. destruct Hp as [Hf Hp].
constructor.
- intros Hin. rewrite Forall_forall in Hf.
  specialize (Hf (fst x, req_size (snd x)) ltac:(apply in_map_iff; exists x; split; [reflexivity | exact Hin])).
  pose proof (req_size_pos (snd x) (Hn x ltac:(left; reflexivity))) as [H1 _].
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
- apply IH; [exact Hp | intros y Hy; apply Hn; right; exact Hy].
Qed.
Lemma s17_nodup : forall B ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros B ly S W mem md HAR. pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
apply s17_pairwise_nodup; [exact Hp|]. intros [p n] Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn). cbn [snd]. lia.
Qed.
Lemma s17_nodup_app_disj : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros A l1. induction l1 as [|a l1 IH]; intros l2 x H Hin Hx; [destruct Hin|].
cbn [app] in H. apply NoDup_cons_iff in H as [Hn Hd]. destruct Hin as [<- | Hin].
- apply Hn, in_or_app. right. exact Hx.
- exact (IH l2 x Hd Hin Hx).
Qed.

(* a byte a reader shows is the memory's byte (PaLibF's val_mem_of_rd32 for one byte) *)
Lemma s17_val_mem1 : forall H mem a v, aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hb k Hk. assert (k = 0%nat) as -> by lia.
destruct (aview_byte SEGS H mem _ _ Hb) as (b & Hm & Hbv & Hrange).
assert (Hle : YO0f.le_byte v 1 0 = v).
{ unfold YO0f.le_byte. rewrite Nat2Z.inj_0, Z.mul_0_r, Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite !Z.mod_small by lia. reflexivity. }
change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Hm. f_equal. apply bv_eq.
rewrite Hle, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia.
symmetry. exact Hbv.
Qed.
Lemma s17_firstn_nth : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros A l. induction l as [|x l IH]; intros n i d Hi.
- destruct n; cbn [firstn]; reflexivity.
- destruct n as [|n]; [lia|]. cbn [firstn]. destruct i as [|i]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
(* m->n: the 4 bytes at m + 0x2000 hold the number of segments, at most 32 (mconf_encp's u32 at MC_N) *)
Lemma s17_mn : forall (rd : reader) m mc, sa_mconf rd m mc ->
  rd32 rd (m + seg_spec.MC_N) (Z.of_nat (length (SegModel.mc_seg mc))) /\ (length (SegModel.mc_seg mc) <= 32)%nat.
Proof.
intros rd m mc (bs & Hb & Henc). destruct Henc as (Hlen & H32 & _ & (_ & Hn) & _).
split; [|exact H32].
intros k Hk.
assert (Ej : Z.of_nat (8192 + k) = 8192 + Z.of_nat k) by (rewrite Nat2Z.inj_add; reflexivity).
assert (Hk2 : (8192 + k < length bs)%nat).
{ apply Nat2Z.inj_lt. rewrite Ej. unfold seg_spec.SEG_M_SIZE in Hlen. rewrite Hlen. clear - Hk. lia. }
pose proof (Hb (8192 + k)%nat Hk2) as E.
replace (m + seg_spec.MC_N + Z.of_nat k) with (m + Z.of_nat (8192 + k)) by (rewrite Ej; unfold seg_spec.MC_N; ring).
rewrite E. f_equal.
assert (E2 : nth (8192 + k) bs ZB0 = nth k (seg_spec.fldz seg_spec.MC_N 4 bs) ZB0).
{ unfold seg_spec.fldz, seg_spec.fld. change (Z.to_nat seg_spec.MC_N) with 8192%nat. change (Z.to_nat 4) with 4%nat.
  rewrite s17_firstn_nth by exact Hk. rewrite nth_skipn. reflexivity. }
rewrite E2, Hn. clear - H32 Hk. revert H32.
generalize (length (SegModel.mc_seg mc)) as L. intros L HL.
do 33 (destruct L as [|L]; [do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|]). lia.
Qed.
(* m->n's shadow byte (check 17): 0, the 8 bytes m + 0x2000 .. + 7 lie in m's 16-aligned block *)
Lemma s17_mn_shadow : forall B ly S (rd : reader) m, lt_hblk B ly S rd m seg_spec.SEG_M_SIZE ->
  rd (shadow_addr (m + seg_spec.MC_N)) = Some 0.
Proof.
intros B ly S rd m (_ & _ & H16 & (_ & _ & _ & HRA & _)).
pose proof (Z.div_mod m 16 ltac:(lia)) as D. rewrite H16, Z.add_0_r in D.
set (q := m / 16) in *.
destruct (HRA (m + seg_spec.MC_N + 7) ltac:(unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE; lia)) as (s & Hs & Hok).
assert (Ex : m + seg_spec.MC_N + 7 = (2 * q + 1024) * 8 + 7) by (unfold seg_spec.MC_N; lia).
assert (Ey : m + seg_spec.MC_N = (2 * q + 1024) * 8 + 0) by (unfold seg_spec.MC_N; lia).
assert (E : shadow_of_addr SHADOW_OFF (m + seg_spec.MC_N + 7) = shadow_addr (m + seg_spec.MC_N)).
{ unfold shadow_of_addr, shadow_addr. rewrite Ex, Ey. rewrite !Z.div_add_l by lia. reflexivity. }
rewrite E in Hs. rewrite Hs. f_equal.
destruct Hok as [-> | (Hlt & Hs8)]; [reflexivity|].
exfalso. rewrite Ex, Z.add_comm, Z_mod_plus_full in Hlt. change (7 mod 8) with 7 in Hlt. lia.
Qed.
(* the reader's and the model's blocks keep their states on their kept bytes *)
Lemma s17_rconf_kept : forall (rd rd' : reader) c rcs, sa_rconf rd c rcs ->
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd' (c + i) = rd (c + i)) -> sa_rconf rd' c rcs.
Proof.
intros rd rd' c rcs (bs & Hb & Henc) K. exists bs. split; [|exact Henc].
intros i Hi. pose proof Henc as [Hl _]. rewrite K by lia. exact (Hb i Hi).
Qed.
Lemma s17_mconf_kept : forall (rd rd' : reader) m mc, sa_mconf rd m mc ->
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd' (m + i) = rd (m + i)) -> sa_mconf rd' m mc.
Proof.
intros rd rd' m mc (bs & Hb & Henc) K. exists bs. split; [|exact Henc].
intros i Hi. pose proof Henc as [Hl _]. rewrite K by lia. exact (Hb i Hi).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
(* the image facts lt_img needs at a later reader (image B's record, lib/B/Prog/SegRecBase.v) *)
Hypothesis IMGF : SegRecBase.seg_img_facts SEGS B.
(* the runtime's record of image B (lib/B/YF0m.v): with IMGF it gives the stack-protector cells at every AR state
   (SegRecCells.seg_rec_cells), the route the .got word gotwA takes since it is a runtime-owned word *)
Hypothesis HBS : SegBSyms B.
(* the free wrapper is the listing's trampoline, and its rule *)
Hypothesis TL : PALib B.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.

(* the entry sp and the realigned base S1 (`addi sp,sp,-352` at 0x84dc0, `andi sp,sp,-32` at 0x84e00) *)
Lemma s17_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 368 <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 352.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME, LTOI_FRAME_MAX, STK_LLVMFuzzerTestOneInput in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.

(* a live block of a state is a harness block of that state: at or above 4096, 16-aligned, addressable *)
Lemma s17_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.

(* ---- lt_img at a later reader ---- *)
(* a literal kept on its bytes (its tail is ROM, its shadow pinned) *)
Lemma s17_lit_kept : forall (rd rd' : reader) a s,
  (forall x, a <= x < a + (Z.of_nat (length s) + 1) -> rd' x = rd x) ->
  (forall x, a + Z.of_nat (length s) < x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 -> rd' x <> None) ->
  sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros rd rd' a s HK HT (Ha & ((Hzs & Hn0) & _) & Hpin & Hrt & Himg).
split; [exact Ha|]. split; [split; [split; [|exact Hn0] | exact HT]|].
- intros i Hi. rewrite HK; [exact (Hzs i Hi)|]. rewrite length_app in Hi. cbn [length] in Hi. lia.
- split; [exact Hpin|]. split; [exact Hrt | exact Himg].
Qed.
(* lt_img at a reader that agrees on every address below the shadow (all of lt_img's objects are image addresses
   or the RELRO window, all below 0x7fff8000) *)
Lemma s17_img_low : forall cx (W' : world SEGS) mem' (rd : reader),
  (forall a, 0 <= a < SHADOW_OFF -> rdW W' mem' a = rd a) ->
  lt_img B cx rd -> lt_img B cx (rdW W' mem').
Proof.
intros cx W' mem' rd K (HRO & HIM & HGI).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KI : forall q n, sa_img SEGS B q n -> forall a, q <= a < q + n -> rdW W' mem' a = rd a).
{ intros q n0 Hq a Ha. destruct (Hq a Ha) as (H1 & _ & _). pose proof (pa_img_range a H1) as R.
  unfold kImgEnd in R. apply K. unfold SHADOW_OFF. lia. }
assert (KW : forall q n a, sa_img SEGS B q n -> q <= a -> a + 8 <= q + n -> rdword (rdW W' mem') a = rdword rd a).
{ intros q n0 a Hq H1 H2. apply rdword_ext. intros k Hk. apply (KI q n0 Hq). lia. }
assert (KL : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s Hl. pose proof Hl as (_ & _ & _ & Hr & Hi). apply (s17_lit_kept rd); [exact (KI _ _ Hi) | | exact Hl].
  intros x Hx. exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hr x Hx). }
split; [|split].
- intros a Hro Ho He. rewrite <- (HRO a Hro Ho He). apply K.
  destruct Hro as [(s & Hs & _ & Hr) | Hr].
  + assert (Hi : in_img SEGS a) by (exists s; split; [exact Hs | exact Hr]).
    pose proof (pa_img_range a Hi) as R. unfold kImgEnd in R. unfold SHADOW_OFF. lia.
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. unfold SHADOW_OFF. lia.
- destruct HIM as (Hm40 & Hm40i & HLF & HLR & (Hcp & Hci & Hcr) & HCa & (Hwp & Hwi & Hwr) & (Hrp & Hri & Hrr)
    & (Hg1 & Hg2) & HLP & HLT & HLI & HD1 & HD2 & HD3).
  split; [|split; [exact Hm40i|]].
  { intros k Hk. rewrite (KI _ _ Hm40i); [exact (Hm40 k Hk) | lia]. }
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
  { split; [exact Hrp|]. split; [exact Hri|]. intros i Hi k Hk. rewrite (KI _ _ Hri); [exact (Hrr i Hi k Hk) | lia]. }
  split.
  { split.
    - rewrite <- Hg1. apply rdword_ext. intros k Hk. apply K. unfold gotwA, SHADOW_OFF. lia.
    - destruct Hg2 as (g & Hg). exists g. rewrite <- Hg. apply rdword_ext. intros k Hk. apply K.
      unfold guardA, SHADOW_OFF. lia. }
  split; [exact HLP|]. split; [exact HLT|]. split; [exact HLI|]. split; [exact HD1|]. split; [exact HD2 | exact HD3].
- destruct HIM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLI & _).
  intros i Hi. rewrite (KI _ _ HLI).
  + exact (HGI i Hi).
  + unfold LONGL_W, LONGL_N. lia.
Qed.

(* ---- the image facts lt_img needs at a later reader: RELRO in the image (image B's record, cif_relro_img), and
   the stack-protector cells re-derived from AR at the later state (SegRecCells.seg_rec_cells) ---- *)
Lemma s17_relro : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof. intros a Ha. exact (@SegRecBase.cif_relro_img _ _ _ IMGF a Ha). Qed.
Lemma s17_ssp : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Proof. intros ly S W mem md HAR. exact (proj1 (proj2 (SegRecCells.seg_rec_cells SEGS B LAWS HBS IMGF ly S W mem md HAR))). Qed.
(* lt_img reads only image bytes the runtime does not own and the stack-protector cells: a reader that keeps
   those bytes and shows the cells keeps lt_img (image A's S00 kit s10_lt_img_kept) *)
Lemma s17_img_kept : forall cx (W' : world SEGS) mem' (rd : reader),
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   rdW W' mem' a = rd a) ->
  sa_ssp (rdW W' mem') gotwA guardA ->
  lt_img B cx rd -> lt_img B cx (rdW W' mem').
Proof.
intros cx W' mem' rd K HSSP (HRO & HIM & HGI).
assert (KI : forall q n, sa_img SEGS B q n -> forall a, q <= a < q + n -> rdW W' mem' a = rd a).
{ intros q n0 Hq a Ha. destruct (Hq a Ha) as (H1 & H2 & H3). exact (K a H1 H2 H3). }
assert (KW : forall q n a, sa_img SEGS B q n -> q <= a -> a + 8 <= q + n -> rdword (rdW W' mem') a = rdword rd a).
{ intros q n0 a Hq H1 H2. apply rdword_ext. intros k Hk. apply (KI q n0 Hq). lia. }
assert (KL : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s Hl. pose proof Hl as (_ & _ & _ & Hr & Hi). apply (s17_lit_kept rd); [exact (KI _ _ Hi) | | exact Hl].
  intros x Hx. exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hr x Hx). }
split; [|split].
- intros a Hro Ho He. rewrite <- (HRO a Hro Ho He). apply K; [|exact Ho | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
  exact (s17_relro a Hr).
- destruct HIM as (Hm40 & Hm40i & HLF & HLR & (Hcp & Hci & Hcr) & HCa & (Hwp & Hwi & Hwr) & (Hrp & Hri & Hrr)
    & _ & HLP & HLT & HLI & HD1 & HD2 & HD3).
  split; [|split; [exact Hm40i|]].
  { intros k Hk. rewrite (KI _ _ Hm40i); [exact (Hm40 k Hk) | lia]. }
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
  { split; [exact Hrp|]. split; [exact Hri|]. intros i Hi k Hk. rewrite (KI _ _ Hri); [exact (Hrr i Hi k Hk) | lia]. }
  split; [exact HSSP|].
  split; [exact HLP|]. split; [exact HLT|]. split; [exact HLI|]. split; [exact HD1|]. split; [exact HD2 | exact HD3].
- destruct HIM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLI & _).
  intros i Hi. rewrite (KI _ _ HLI).
  + exact (HGI i Hi).
  + unfold LONGL_W, LONGL_N. lia.
Qed.

(* ---- the frame state carried to a later state ---- *)
(* what lt_frame and lt_img read of the memory: the real-stack frame from 184(s1) up (184, 200 and the 13 saved
   registers), the image's unowned bytes but errno, the side-stack frame's 512 bytes and its 64 shadow bytes *)
Definition s17_kept (cx : lcx) (W : world SEGS) mem (W2 : world SEGS) mem2 : Prop :=
  (forall a, x_s1 cx + 184 <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W mem a) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW W mem a) /\
  (forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W mem a) /\
  (forall i, 0 <= i < 64 -> rdW W2 mem2 (x_sh cx + i) = rdW W mem (x_sh cx + i)).
Lemma s17_core_carry : forall cx ly S (W : world SEGS) regs mem md k acc rem o O
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 k2 acc2 rem2 O2,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k2 ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  s17_kept cx W mem W2 mem2 -> lt_blocks B cx ly2 S2 O2 -> lt_bud MT cx S2 k2 acc2 rem2 ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 o O2.
Proof.
intros cx ly S W regs mem md k acc rem o O ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 O2 HB HC HJ2 P2 P3 P4 P8 P9
  (KS & KI & KF & KH) HBL HBUD.
pose proof (s17_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HC as (HF & HI & _ & _).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
split; [|split; [|split; [exact HBL | exact HBUD]]].
- split; [exact HJ2|]. rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s17_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply KS. lia. }
  split; [apply (s17_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KF; lia|].
  split; [apply (s17_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KF; lia|].
  split; [apply (s17_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KF; lia|].
  split; [apply (s17_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KF; unfold LT_FLAGW in *; lia|].
  split; [apply (s17_word_kept (rdW W mem)); [|exact H200]; intros x Hx; apply KS; lia|].
  split.
  { intros i Hi. pose proof Hi as Hi'. rewrite (lt_fsh_len o) in Hi'. rewrite KH by lia. exact (HSH i Hi). }
  apply (s17_word_kept (rdW W mem)); [|exact H184]. intros x Hx. apply KS. lia.
- exact (s17_img_kept cx W2 mem2 (rdW W mem) KI (s17_ssp _ _ W2 mem2 md2 (proj1 HJ2)) HI).
Qed.
(* what a call stepped through acall_kept keeps, when the bytes it may write lie off the side-stack frame, off
   its shadow and in the application's memory *)
Lemma s17_kept_of_acall : forall cx lyc Sc (W : world SEGS) memc mdc k (W2 : world SEGS) mem2 slo (Er : Z -> Prop),
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] lyc Sc W memc mdc k ->
  acall_kept SEGS B lyc Sc W memc W2 mem2 slo (x_s1 cx) Er ->
  (forall a, Er a -> (a < x_fr cx \/ x_fr cx + 512 <= a) /\ (a < kLowShadowBeg \/ kHighMemBeg <= a)) ->
  s17_kept cx W memc W2 mem2.
Proof.
intros cx lyc Sc W memc mdc k W2 mem2 slo Er HB HJ (K1 & _ & K3 & K4 & _ & _) HE.
pose proof (s17_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr lyc LT_FCLS (x_fpos cx) = x_fr cx) by exact (s17_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
unfold LTOI_FRAME_MAX, STK_LLVMFuzzerTestOneInput in *.
split; [|split; [|split]].
- intros a Ha. apply K1; [lia | lia].
- exact K3.
- intros a Ha. apply (K4 LT_FCLS (x_fpos cx) a HinF).
  + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, F512. lia.
  + intros Hr. destruct (HE a Hr) as [[Hq|Hq] _]; lia.
- intros i Hi. apply (K4 LT_FCLS (x_fpos cx) _ HinF).
  + right. unfold in_zr. cbn [fst snd]. rewrite EF, F512. unfold x_sh. lia.
  + intros Hr. destruct (HE _ Hr) as [_ [Hq|Hq]]; unfold x_sh, shadow_addr, SHADOW_OFF, kLowShadowBeg in *; lia.
Qed.
(* what a program call keeps (its own journal from the call, footprint FP1 inside one live block of the call) *)
Lemma s17_kept_of_sub : forall cx lyc Sc (W : world SEGS) memc mdc k ly2 S2 (W2 : world SEGS) mem2 md2 STK1 FP1 k1 b n,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] lyc Sc W memc mdc k ->
  ajournal SEGS B STK1 (x_s1 cx) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  In (b, n) (ablocks B lyc Sc) -> (forall a, inFP FP1 a -> b <= a < b + req_size n) -> ~ YI16.sink_open_fp FP1 ->
  s17_kept cx W memc W2 mem2.
Proof.
intros cx lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 STK1 FP1 k1 b n HB HJ HJc Hin NF HC.
pose proof (s17_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _ & F3 & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr lyc LT_FCLS (x_fpos cx) = x_fr cx) by exact (s17_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b n HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hn).
pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc b n LT_FCLS (x_fpos cx) HAR Hin HinF) as Hsep.
rewrite EF, F512 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
pose proof (req_size_pos n ltac:(lia)) as [Hq1 _].
unfold LTOI_FRAME_MAX, STK_LLVMFuzzerTestOneInput in *.
split; [|split; [|split]].
- intros a Ha. apply F1; [lia | lia | intros Hf; pose proof (NF a Hf); lia].
- intros a Hi Ho He. apply F3; [exact Hi | exact Ho | exact He |].
  apply fp_spares_closed; [exact HC|]. intros Hf. pose proof (NF a Hf) as Hab.
  destruct (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR) as [_ Hni].
  + left. exists b, n. split; [exact Hin | exact Hab].
  + exact (Hni Hi).
- intros a Ha. apply (F4 LT_FCLS (x_fpos cx) a HinF).
  + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, F512. lia.
  + intros Hf. pose proof (NF a Hf). lia.
- intros i Hi. apply (F4 LT_FCLS (x_fpos cx) _ HinF).
  + right. unfold in_zr. cbn [fst snd]. rewrite EF, F512. unfold x_sh. lia.
  + intros Hf. pose proof (NF _ Hf) as Hab.
    unfold in_app, kLowShadowBeg, ASAN_CEIL in Hbapp. unfold x_sh, shadow_addr, SHADOW_OFF in Hab. lia.
Qed.

(* ---- the stack a call from S1 finds: mapped from S1 up, and a frame chain from s0 = SP0 ---- *)
Lemma s17_stack_rd : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o -> astack_rd ly (rdW W mem) (x_s1 cx).
Proof.
intros cx ly S W regs mem md k o HB HF.
pose proof (s17_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HF as (HJ & _). pose proof HB as (_ & HPRES & _).
pose proof asan_consts as (C1 & _).
apply (astack_rd_mono ly _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput));
  [unfold LTOI_FRAME_MAX, STK_LLVMFuzzerTestOneInput in *; lia|].
apply astack_rd_of_pres.
apply (astack_pres_journal SEGS B pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
  (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k HJ HPRES).
intros a (r & Hr & Ha) Ha2. exfalso. unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
unfold longlA, A_LONGL, LONGL_N in Ha. lia.
Qed.
Lemma s17_chain : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o -> 4096 <= raZ regs ->
  exists ch, chain_pre ly (rdW W mem) regs ch.
Proof.
intros cx ly S W regs mem md k o HB HF Hra.
pose proof (s17_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof (s17_stack_rd cx ly S W regs mem md k o HB HF) as HR.
destruct HF as (HJ & R2 & _ & _ & R8 & _).
pose proof asan_consts as (C1 & _).
assert (Esp : spZ regs = x_s1 cx)
  by (unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
assert (Es0 : s0Z regs = x_sp0 cx)
  by (unfold s0Z; rewrite R8; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
apply chain_pre_any; [exact Hra | rewrite Esp; exact HR | rewrite Esp, Es0; lia].
Qed.
Lemma s17_achain : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o ->
  exists ch, achain ly (rdW W mem) (x_s1 cx) (x_sp0 cx) ch.
Proof.
intros cx ly S W regs mem md k o HB HF.
pose proof (s17_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
apply achain_any; [exact (s17_stack_rd cx ly S W regs mem md k o HB HF) | right; right; right; lia].
Qed.

(* ---- one call of the free wrapper (the trampoline the listing's PCall names) from a point where lt_core holds,
   the block freed the newest of the harness's (image A's S01 / S02 kit lt_malloc_at, for free) ---- *)
Lemma s17_free_at : forall cx ly S (W : world SEGS) regsT memT md k acc rem o t n O raw Q,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o ((t, n) :: O) ->
  1 <= rem -> getr regsT 10 = w64 t -> getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
     lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) (rem - 1) o O ->
     aregs_preserved regsT regs2 ->
     (forall b m i, In (b, m) O -> 0 <= i < req_size m -> rdW W2 mem2 (b + i) = rdW W memT (b + i)) ->
     (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) ->
     SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_free)) memT (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regsT memT md k acc rem o t n O raw Q HB HC Hrem H10 H1 Hraw Hra4 HK.
pose proof (s17_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HC as (HF & HI & HBL & HBUD).
pose proof HF as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _ & Hev & Hlive & Hmo).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR, Hs1lo.
pose proof (mo_free_nonneg MT MTL) as M3.
pose proof (mo_malloc_nonneg MT MTL 65536 ltac:(lia)) as M0.
assert (HU : mo_free MT <= LT_U MT) by (unfold LT_U; lia).
assert (HRU : LT_U MT <= rem * LT_U MT) by nia.
assert (Hin : In (t, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HBL)); left; reflexivity).
pose proof (s17_nodup B ly S W memT md HAR) as HND.
pose proof (Permutation_NoDup HBL HND) as HND2.
assert (Hnb0 : ~ In (t, n) (x_bl0 B cx))
  by exact (s17_nodup_app_disj ((t, n) :: O) (x_bl0 B cx) (t, n) HND2 ltac:(left; reflexivity)).
assert (HnO : ~ In (t, n) O) by (cbn [app] in HND2; apply NoDup_cons_iff in HND2 as [Hn _];
  intros Hx; apply Hn, in_or_app; left; exact Hx).
destruct (s17_chain cx ly S W regsT memT md k o HB HF ltac:(unfold raZ; rewrite H1; exact Hra4)) as (ch & Hch).
assert (Hsp : spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx))
  by (unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; lia).
rewrite (pal_free B TL).
eapply SRr_bind.
{ exact (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE4 fx) W regsT memT STK_LLVMFuzzerTestOneInput (x_sp0 cx)
    (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k t n
    (x_s1 cx - x_sp0 cx) raw ch HJ Hin H10 Hsp ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite R3; exact Hgp0) ltac:(rewrite R4; exact Htp0) H1 Hraw
    ltac:(unfold EV_LTOI in *; lia) Hch ltac:(intros Hb0; exfalso; exact (Hnb0 Hb0))
    ltac:(apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc (mo_free MT) MTL Hmo B4 M3); lia)). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPr & (l1 & l2 & E1 & E2) & Hfr2 & HKc & MLE & _).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HKc by ring.
pose proof HKc as (K1 & K2 & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS ly S W memT md t n HAR Hin) as (_ & Ht4096 & Htceil & Htapp & _ & _ & Htn).
assert (Hfin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS ly S W memT md t n LT_FCLS (x_fpos cx) HAR Hin Hfin) as Hsep.
rewrite (s17_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _) in Hsep.
change (fs_frame_bytes LT_FCLS) with 512 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
assert (KO : forall b m i, In (b, m) O -> 0 <= i < req_size m -> rdW W2 mem2 (b + i) = rdW W memT (b + i)).
{ intros b m i HbO Hi. apply (K2 b m i); [apply (Permutation_in _ (Permutation_sym HBL)); right; apply in_or_app; left; exact HbO
    | exact Hi |]. cbv beta.
  assert (Hne : (b, m) <> (t, n)) by (intros Heq; rewrite Heq in HbO; exact (HnO HbO)).
  pose proof (sep_blocks SEGS B LAWS ly S W memT md b m t n HAR
    ltac:(apply (Permutation_in _ (Permutation_sym HBL)); right; apply in_or_app; left; exact HbO) Hin Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (KHI : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. apply K1; [lia | lia]. }
apply (HK ly2 S2 W2 regs2 mem2 md2); [| exact HPr | exact KO | exact KHI].
apply (s17_core_carry cx ly S W regsT memT md k acc rem o ((t, n) :: O) ly2 S2 W2 regs2 mem2 md2 _ _ _ _ HB HC HJ2).
- exact (s17_pres_reg _ _ 2%bv 2 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
- exact (s17_pres_reg _ _ 3%bv 3 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
- exact (s17_pres_reg _ _ 4%bv 4 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
- exact (s17_pres_reg _ _ 8%bv 8 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
- exact (s17_pres_reg _ _ 9%bv 9 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
- apply (s17_kept_of_acall cx ly S W memT md k W2 mem2 _ _ HB HJ HKc).
  intros a Ha. cbv beta in Ha. unfold x_fr. split; [lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- unfold lt_blocks in *. rewrite E2. rewrite E1 in HBL.
  exact (Permutation_app_inv l1 l2 [] (O ++ x_bl0 B cx) (t, n) HBL).
- unfold lt_bud. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ B4 MLE)|]. split; [lia|].
  set (U := LT_U MT) in *. clearbody U. nia.
Qed.

End e.
End f.
End d.
