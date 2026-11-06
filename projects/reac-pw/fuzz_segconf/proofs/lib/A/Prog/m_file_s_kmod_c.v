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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 364 of its 416 lines of code are new or changed and 401 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc): the inner piece MK_CPY -> KDONE of segment S_MF_KMOD,
   mk_cpy_ok : forall n, MF_KDONE_stmt B n -> MK_CPY_stmt B n (lib/A/Prog/m_file_s_kmod_m.v, m_file_m.v CHANGE 3).
   The KMOD copy sub-lane of the G2 walk owner's G2.

   The code (listing m_file.fuzz_segconf.asan.s lines 627-640; the slow block 951-954 is not reached):
     0x86880 ld s7,136(s1)   s7 = cur = g = c + 256 gi (the 136(s1) slot, atom 37 of mf_seed)
     0x86884 addi a0,s7,36    0x86888 addi a2,s4,1    0x8688c mv a1,s5
     0x86890 jal __asan_memcpy (g->model, low, ln + 1), stepped by PaCall.v aj_intrin_atS
     0x86894 addi a0,s7,32 .. 0x868a0 lb: the instrumented check of g->model_set (a load of the shadow byte at
       ((g + 32) >> 3) + the shadow base and a compare); its shadow entry g + [0, 256) (mf_she_at, from the block's
       range_addressable) makes the byte 0, so the error path (the call of an errpath_* entry) is not reached
     0x868a4 ld s5,128(s1) (s5 = c)    0x868b0 sw a1,0(a0) (g->model_set = 1)    0x868b4 j 0x86cd0 (KDONE)
   The steps: mf_seed (m_file_sd.v) at 0x86880 with the slot region made read-only, so the run to the call leaves
   memory as it was; the memcpy's premises (mkc_cpy_pre: g->model inside the mconf block and the footprint, low.i in
   the frame with its shadow 0, the two apart); after the call every region of the seed kept
   (jafter_call_keep_pi), the fact and the 4-byte write region of atom 37 added; the token run to KDONE; then
   the KMOD model sub-lane's sa_mconf_with_model gives the block of m_upd mcc gi (ms_with_model (h_fold vv 24)), m_file_k.v's
   mf_keep_art carries every cut fact over the two changed sets (the memcpy's window below s1, g + [32, 60)), and
   mf_loop_next steps the line loop to the next line. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_kmod_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_sd m_file_s_kmod_t m_file_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the line before the first '\n' and the text after it are no longer than the text *)
Lemma mkc_line_len : forall l, (length (fst (break_nl l)) + length (snd (break_nl l)) <= length l)%nat.
Proof.
induction l as [|b r IH]; cbn [break_nl]; [cbn; lia|].
destruct (b =? NL); cbn [fst snd length]; [lia|].
destruct (break_nl r) as [l q]. cbn [fst snd length] in *. lia.
Qed.

(* the value cut from the line has its length *)
Lemma mkc_vv_len : forall rest ov vl vv, (ov + vl <= length (mf_line rest))%nat -> firstn vl (skipn ov rest) = vv ->
  length vv = vl.
Proof.
intros rest ov vl vv H1 H2. subst vv. rewrite length_firstn, length_skipn.
pose proof (mkc_line_len rest) as H. unfold mf_line in H1. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA SS___asan_memcpy).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* where the objects of the cut lie: the mconf block, the frame, the stack *)
Lemma mkc_where : forall n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv,
mk_base B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
exists bb bm, In (bb, bm) (ablocks B lyc Sc) /\ bb <= mv_c v /\ mv_c v + seg_spec.SEG_M_SIZE <= bb + req_size bm /\
4096 <= bb /\ bb + req_size bm <= alloc_ceiling /\ in_app bb (req_size bm) /\
(bb + req_size bm <= frame_addr lyc 1 pos \/ frame_addr lyc 1 pos + 128 <= bb) /\
(forall a, bb <= a < bb + req_size bm -> ~ in_img SEGS a) /\
In (1, pos) (frames Sc) /\ 4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling /\
in_app (frame_addr lyc 1 pos) 128 /\ frame_addr lyc 1 pos mod 64 = 0 /\
(gi < length (mc_seg mcc))%nat /\ (length (mc_seg mcc) <= 32)%nat /\
alloc_ceiling + 8560 <= mv_sp v /\ mv_sp v mod 16 = 0 /\ mv_sp v <= 2 ^ 47 /\
mf_s1 (mv_sp v) = mv_sp v - 288 - mv_sp v mod 32 /\ (mv_sp v mod 32 = 0 \/ mv_sp v mod 32 = 16) /\
mv_c v mod 16 = 0 /\ lyc = mv_ly v.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv HBASE.
pose proof HBASE as (CX & LS & FRM & CORE & CELLS & RA & Hlen & Hne & LOOP & Hovl & Hvv & NP & H24 & H22).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _ & Hheap & _).
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V112 & HMC & HADDR & HTAIL).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof LOOP as (_ & _ & _ & _ & _ & Hcur & _). cbn [mf_cur_ok] in Hcur.
destruct LS as [Hly _].
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1.
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (bb & bm & Hbin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HAR Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbm).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 1 pos HAR Hfin) as (HF64 & _ & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bb bm 1 pos HAR Hbin Hfin) as Hsep.
change (fs_frame_bytes 1) with 128 in *. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
destruct HMC as (bs & _ & (_ & Hn32 & _)).
assert (Hs1 : mf_s1 (mv_sp v) = mv_sp v - 288 - mv_sp v mod 32 /\ (mv_sp v mod 32 = 0 \/ mv_sp v mod 32 = 16)).
{ unfold mf_s1. replace ((mv_sp v - 288) mod 32) with (mv_sp v mod 32)
    by (rewrite Zminus_mod; change (288 mod 32) with 0; rewrite Z.sub_0_r, Z.mod_mod by lia; reflexivity).
  split; [reflexivity|]. pose proof (Z.mod_pos_bound (mv_sp v) 32 ltac:(lia)).
  pose proof (Z.div_mod (mv_sp v) 32 ltac:(lia)). pose proof (Z.div_mod (mv_sp v) 16 ltac:(lia)). lia. }
exists bb, bm.
split; [exact Hbin|]. split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Hb4096|]. split; [exact Hbceil|].
split; [exact Hbapp|]. split; [exact Hsep|].
split.
{ intros a Ha. apply (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR (or_introl (ex_intro _ bb (ex_intro _ bm (conj Hbin Ha)))))). }
split; [exact Hfin|]. split; [exact HF4096|]. split; [exact HFceil|]. split; [exact HFapp|]. split; [exact HF64|].
split; [exact Hcur|]. split; [exact Hn32|]. split; [exact S1|]. split; [exact S3|]. split; [exact S2|].
split; [exact (proj1 Hs1)|]. split; [exact (proj2 Hs1)|]. split; [exact Hc16 | exact Hly].
Qed.

(* the premises of the __asan_memcpy step at 0x86890 (PaCall.v aj_intrin_atS): the destination g->model is in
   the mconf block, in the footprint, live and addressable; the source low.i is in the walk's own frame, its 24
   bytes mapped and their shadow 0 (low.i in scope); the two are apart (block / frame) *)
Lemma mkc_cpy_pre : forall n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv memT mdT regsT d x nn,
mk_base B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (m_upd mcc gi (ms_with_model (h_fold vv 24)), Some gi) line rest = mf_final v ->
AR SEGS B lyc Sc Wc memT mdT ->
sa_zs (rdW Wc memT) (frame_addr lyc 1 pos + 32) (h_fold vv 24 ++ [0]) ->
(forall i, 4 <= i < 12 ->
 val_mem SEGS (mrestrict (w_H Wc) memT) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_ON) ->
spZ regsT = mf_s1 (mv_sp v) ->
d = seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL -> x = frame_addr lyc 1 pos + 32 ->
nn = Z.of_nat (mk_ln vl) + 1 ->
0 <= nn < 2 ^ 32 /\ 0 <= d /\ d + nn <= 2 ^ 63 /\
(forall a, d <= a < d + nn ->
 awr_byte SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v))
   (ablocks B (mv_ly v) (mv_S v)) (ablocks B lyc Sc) (frames (mv_S v)) lyc [(1, pos)] a /\
 ~ (mf_s1 (mv_sp v) - ESTACK <= a < mf_s1 (mv_sp v))) /\
(forall a, d <= a < d + nn -> inFP (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) a ->
 (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ mv_sp v <= a < ly_top lyc ->
 writable_at SEGS (mrestrict (w_H Wc) memT) a) /\
amem_range d nn /\ range_addressable (rdW Wc memT) SHADOW_OFF d nn /\ (0 < nn -> shadow_hull_vis (rdW Wc memT) d nn) /\
0 <= x /\ x + nn <= 2 ^ 63 /\ src_ok SEGS Wc regsT memT x nn /\ (d + nn <= x \/ x + nn <= d) /\ amem_range x nn /\
range_addressable (rdW Wc memT) SHADOW_OFF x nn /\ (0 < nn -> shadow_hull_vis (rdW Wc memT) x nn).
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv memT mdT regsT d x nn
  HBASE HFIN HART HZT HLT Hsp Hd Hx Hnn.
pose proof HBASE as (CX & LS & FRM & CORE & CELLS & RA & Hlen & Hne & LOOP & Hovl & Hvv & NP & H24 & H22).
destruct (mkc_where n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv HBASE)
  as (bb & bm & Hbin & Hb1 & Hb2 & Hb4096 & Hbceil & Hbapp & Hsep & Hnimg & Hfin & HF4096 & HFceil & HFapp & HF64 &
      Hgi & Hn32 & S1 & S3 & S2 & Hs1 & Hs1m & Hc16 & Hly).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hvl : length vv = vl) by (exact (mkc_vv_len rest ov vl vv Hovl Hvv)).
destruct (mk_ln_bound vl) as (Hln23 & _ & _).
assert (Hlowlen : length (h_fold vv 24) = mk_ln vl) by (rewrite hfold_len, Hvl; reflexivity).
assert (Hgif : (gi < length (mc_seg (mf_final v)))%nat).
{ rewrite <- HFIN. pose proof (mf_fin_segs_mono (m_upd mcc gi (ms_with_model (h_fold vv 24)), Some gi) line rest) as M.
  cbn [fst] in M. rewrite m_upd_segs_len in M. lia. }
assert (Hg : seg_spec.mseg_addr (mv_c v) gi = mv_c v + 256 * Z.of_nat gi)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
assert (HE : ESTACK = 4096) by reflexivity.
unfold seg_spec.MS_MODEL in Hd. unfold seg_spec.SEG_M_SIZE in Hb2.
set (F := frame_addr lyc 1 pos) in *.
assert (HF8 : F / 8 * 8 = F) by (pose proof (Z.div_mod F 64 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia));
  pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ intros a Ha. split; [|lia].
  right; left. split.
  - apply (mk_fp_seg (mv_c v) (mv_k0 v) (mf_final v) gi a Hgif). unfold seg_spec.MSEG_SIZE. lia.
  - exists bb, bm. split; [exact Hbin | lia]. }
split.
{ intros a Ha _ [[_ Himg] | Hsp0]; exfalso; [apply (Hnimg a); [lia | exact Himg] | lia]. }
split; [apply (amem_range_of_block SEGS B LAWS lyc Sc Wc memT mdT bb bm d nn HART Hbin); lia|].
split; [apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc memT mdT bb bm d nn HART Hbin); lia|].
split; [intros Hn0; apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memT mdT bb bm d nn HART Hbin); lia|].
split; [lia|]. split; [lia|].
split.
{ intros a Ha. split; [|rewrite Hsp; lia].
  replace a with (F + 32 + Z.of_nat (Z.to_nat (a - (F + 32)))) by lia.
  rewrite HZT; [discriminate|]. rewrite length_app, Hlowlen. cbn [length]. lia. }
split; [lia|].
split; [apply (amem_range_sub_app F 128 x nn HFapp HFceil); lia|].
split.
{ intros a Ha. exists 0. split; [|left; reflexivity].
  assert (Ha8 : F / 8 + 4 <= a / 8 < F / 8 + 7).
  { split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
  unfold shadow_of_addr. replace (SHADOW_OFF + a / 8) with (SHADOW_OFF + F / 8 + (a / 8 - F / 8)) by lia.
  apply (aview_of_val_mem1 SEGS); [apply HLT; lia | unfold MF_LOW_ON; lia]. }
intros Hn0. apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc memT mdT 1 pos x nn HART Hfin);
  change (fs_frame_bytes 1) with 128; lia.
Qed.

Lemma mk_cpy_ok : forall n, MF_KDONE_stmt B n -> MK_CPY_stmt B n.
Proof.
intros n KD. unfold MK_CPY_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv r HBASE HROW HFIN HZS H20 H21.
pose proof HBASE as (CX & LS & FRM & CORE & CELLS & RA & Hlen & Hne & LOOP & Hovl & Hvv & NP & H24 & H22).
destruct (mkc_where n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv HBASE)
  as (bb & bm & Hbin & Hb1 & Hb2 & Hb4096 & Hbceil & Hbapp & Hsep & Hnimg & Hfin & HF4096 & HFceil & HFapp & HF64 &
      Hgi & Hn32 & S1 & S3 & S2 & Hs1 & Hs1m & Hc16 & Hly).
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V112 & HMC & HADDR & HTAIL).
pose proof LOOP as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hvl : length vv = vl) by (exact (mkc_vv_len rest ov vl vv Hovl Hvv)).
destruct (mk_ln_bound vl) as (Hln23 & _ & _).
assert (Hg : seg_spec.mseg_addr (mv_c v) gi = mv_c v + 256 * Z.of_nat gi)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
assert (Hbrk : (length (mf_rest rest) < length rest)%nat) by (exact (proj1 (proj2 (mf_break_snd rest)) Hne)).
assert (Hcur : 0 <= mf_cur_ptr (mv_c v) (Some gi) < 2 ^ 64)
  by (cbn [mf_cur_ptr]; rewrite Hg; unfold seg_spec.SEG_M_SIZE in Hb2; lia).
assert (Hnp : 0 <= mf_next p rest < 2 ^ 64).
{ destruct L5 as (A1 & A2 & _). unfold mf_next. rewrite Nat2Z.inj_sub by lia. lia. }
unfold mf_at.
(* the seed at 0x86880: cur = Some gi, the next line's address in 144(s1), low.i's shadow 0 *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest) [] MK_CPY
  true true [] false false [] false CX CORE (mf_regs_base_of B v lyc pos regs1 RA) (fun _ => CELLS) Hcur
  (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
set (E := mfE regs1 v lyc pos (Some gi) (mf_next p rest) []) in HS0.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (EE : forall k (r0 : bv 5), Z.of_nat k = bv_unsigned r0 -> ew E k = getr regs1 r0)
  by (intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat ->
  ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) (mf_next p rest) []) (Z_to_bv 64 0))
  by (intros; apply mfE_extra; assumption).
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33.
pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (EX 5%nat ltac:(unfold A_TEXT; lia)) as E37.
cbn [Nat.add nth mf_extra map app mf_cur_ptr] in E32, E33, E34, E37.
(* the spill slots read-only for the runs of this piece (nothing below writes them) *)
pose proof (st_ok_pi_region_nth E _ _ 1 (mf_r_slots true true []) HS0 eq_refl) as HR1.
pose proof (ast_ok_pi_set_region E _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 0 0) HS0
  eq_refl eq_refl ltac:(vm_compute; reflexivity) (region_ok_rewindow SEGS E _ _ 0 0 HR1 ltac:(intros o Ho; lia)))
  as HS.
clear HS0 HR1.
pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36. cbn [Nat.add nth mf_extra map app] in E36.
assert (UBx : U E (SOff 32 0) = SHADOW_OFF) by (unfold E; apply mfE_U32).
clearbody E.
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hsp64 : 0 <= mv_sp v < 2 ^ 64) by lia.
assert (Hgr : 0 <= seg_spec.mseg_addr (mv_c v) gi < 2 ^ 64) by (cbn [mf_cur_ptr] in Hcur; exact Hcur).
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = mv_sp v)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8).
{ rewrite E36; apply unsigned_lit_small. pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia. }
assert (U37 : bv_unsigned (ew E 37) = seg_spec.mseg_addr (mv_c v) gi) by (rewrite E37; apply unsigned_lit_small; lia).
(* 0x86880-0x8688c: s7 = cur = g, a0 = g + 36, a2 = ln + 1, a1 = low; the run stops at the memcpy call *)
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
lazymatch type of HF with frame_of _ ?rs0 _ _ =>
  assert (HM1 : ms_mem ms = memc) by exact (frame_of_read_only E rs0 memc (ms_mem ms) ltac:(vm_compute; reflexivity) HF) end.
clear HF HFr HG.
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl). cbn [ss_pc setpc].
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
assert (Ra0 : getr (ms_regs ms) 10 = w64 (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL)).
{ rewrite P10, E37, unsigned_lit_small by lia. reflexivity. }
assert (Ra1 : getr (ms_regs ms) 11 = w64 (frame_addr lyc 1 pos + 32)).
{ rewrite P11, (EE 21%nat 21%bv eq_refl). exact H21. }
assert (Ra2 : getr (ms_regs ms) 12 = w64 (Z.of_nat (mk_ln vl) + 1)).
{ rewrite P12, (EE 20%nat 20%bv eq_refl), H20. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hspc : spZ (ms_regs ms) = mf_s1 (mv_sp v)) by (unfold spZ; rewrite P2; exact U2).
assert (Rgp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact R3).
assert (Rtp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact R4).
destruct (mkc_cpy_pre n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv (ms_mem ms) _ (ms_regs ms)
  (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL) (frame_addr lyc 1 pos + 32) (Z.of_nat (mk_ln vl) + 1)
  HBASE HFIN (proj1 HJ) ltac:(rewrite HM1; exact HZS) ltac:(rewrite HM1; exact VSH) Hspc eq_refl eq_refl eq_refl)
  as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
(* 0x86890: __asan_memcpy(g + 36, low, ln + 1); it returns to 0x86894 = BASE + 7008 (AF_m_file + 0x9d8) *)
eapply SRr_bind.
{ apply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA SS___asan_memcpy) (AMEMCPY fx) Wc (ms_regs ms) (ms_mem ms)
    SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v)
    (mv_md v) [(1, pos)] lyc Sc _ 0 (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL) (frame_addr lyc 1 pos + 32)
    (Z.of_nat (mk_ln vl) + 1) (mf_s1 (mv_sp v) - mv_sp v) (Z_to_bv 64 (BASE + 7008)) HJ Ra0 Ra1 Ra2 Q1 Q2 Q3).
  - rewrite Hspc. lia.
  - rewrite Hs1. destruct Hs1m as [Hm | Hm]; rewrite Hm;
      [replace (mv_sp v - 288 - 0 - mv_sp v) with (-288) by lia | replace (mv_sp v - 288 - 16 - mv_sp v) with (-304) by lia];
      reflexivity.
  - lia.
  - rewrite HES, HSTK. lia.
  - exact Rgp.
  - exact Rtp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. replace (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) with (mf_s1 (mv_sp v)) by lia. exact (Q4 a Ha).
  - exact Q5.
  - exact Q6.
  - exact Q7.
  - exact Q8.
  - exact (conj Q9 (conj Q10 (conj Q11 (conj Q12 (conj Q13 (conj Q14 Q15)))))). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr2 & Hpres2 & HSM2).
(* the arithmetic of the places: g = c + 256 gi inside the block, the frame and its shadow, the stack *)
assert (Hd : seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL = mv_c v + 256 * Z.of_nat gi + 36)
  by (rewrite Hg; unfold seg_spec.MS_MODEL; lia).
assert (HgB : mv_c v + 256 * Z.of_nat gi + 256 <= bb + req_size bm) by (unfold seg_spec.SEG_M_SIZE in Hb2; lia).
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as DF8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as MF8.
assert (HbA := Hbapp). assert (HFA := HFapp). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HbA, HFA.
(* 0x86894: the symbolic state after the call, every region kept (none meets g->model or the scratch window) *)
jafter_call_keep_pi HS 64%nat regs2 (mrestrict (w_H Wc) mem2) HP2 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (eapply (region_kept_aview (segs := SEGS) E (w_H Wc) (ms_mem ms) mem2);
   [ first [exact U8 | exact U2 | exact U34 | exact U36]
   | intros a Ha; apply Hfr2; unfold SHADOW_OFF in *; rewrite ?Hd, ?HES; lia
   | exact Hpres2 ]). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 64 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall k, (k < 64)%nat -> ew E2 k = ew E k) by (intros k Hk; rewrite HE2; apply YN3v.ew_havoc_old; exact Hk).
clear HE2.
assert (U2' : bv_unsigned (ew E2 2) = mf_s1 (mv_sp v)) by (rewrite OLD2 by lia; exact U2).
assert (U8' : bv_unsigned (ew E2 8) = mv_sp v) by (rewrite OLD2 by lia; exact U8).
assert (U34' : bv_unsigned (ew E2 34) = frame_addr lyc 1 pos) by (rewrite OLD2 by lia; exact U34).
assert (U36' : bv_unsigned (ew E2 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8) by (rewrite OLD2 by lia; exact U36).
assert (U37' : bv_unsigned (ew E2 37) = seg_spec.mseg_addr (mv_c v) gi) by (rewrite OLD2 by lia; exact U37).
(* g = atom 37: a fact (16-aligned, inside the heap band), the store's region g + [32, 36), the shadow entry of
   g + [0, 256) (the check of g->model_set at 0x868a0) *)
assert (Hg16 : seg_spec.mseg_addr (mv_c v) gi mod 16 = 0).
{ rewrite Hg. pose proof (Z.div_mod (mv_c v) 16 ltac:(lia)) as Dc.
  replace (mv_c v + 256 * Z.of_nat gi) with ((mv_c v / 16 + 16 * Z.of_nat gi) * 16) by lia. apply Z_mod_mult. }
pose proof (st_ok_pi_add_fact E2 _ _ 37 (HPTR 4) HS
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U37'; change (2 ^ 4) with 16; lia)) as HSf.
assert (HRst : region_ok SEGS E2 (mrestrict (w_H Wc) mem2) (YP09.mkRegion (Some 37%nat) 32 36 32 36 [])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U37'.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm (proj1 HJ2) Hbin) as (_ & _ & _ & _ & Hpb & _). apply Hpb. lia. }
lazymatch type of HSf with st_ok_pi _ _ _ ?ssf _ =>
  let rsf := eval vm_compute in (ss_mem ssf) in
  assert (HDst : all_disjoint E2 (YP09.mkRegion (Some 37%nat) 32 36 32 36 []) rsf) end.
{ apply all_disjoint_of_extents. cbn [map zall_disjoint]. unfold extent_of_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U37', ?U8', ?U2', ?U34', ?U36'.
  unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF in *. repeat split; lia. }
pose proof (st_ok_pi_add_region E2 _ _ (YP09.mkRegion (Some 37%nat) 32 36 32 36 []) HSf eq_refl HRst HDst) as HSr.
clear HS HSf HDst. rename HSr into HS.
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 37 0 256] E2 (mrestrict (w_H Wc) mem2)).
{ unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (mf_she_at E2 Wc mem2 37 (seg_spec.mseg_addr (mv_c v) gi) 256).
  - rewrite U_SOff, OLD2 by lia. rewrite <- U_SOff. exact UBx.
  - rewrite OLD2 by lia. exact E37.
  - exact Hgr.
  - lia.
  - apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc mem2 md2 bb bm _ _ (proj1 HJ2) Hbin); lia.
  - intros x Hx. apply (mf_blk_app B v CX x). unfold seg_spec.SEG_M_SIZE. lia. }
assert (Hgif : (gi < length (mc_seg (mf_final v)))%nat).
{ rewrite <- HFIN. pose proof (mf_fin_segs_mono (m_upd mcc gi (ms_with_model (h_fold vv 24)), Some gi) line rest) as M.
  cbn [fst] in M. rewrite m_upd_segs_len in M. lia. }
assert (Hst : forall a, seg_spec.mseg_addr (mv_c v) gi + 32 <= a < seg_spec.mseg_addr (mv_c v) gi + 36 ->
  awr_byte SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v))
    (ablocks B (mv_ly v) (mv_S v)) (ablocks B lyc Sc) (frames (mv_S v)) lyc [(1, pos)] a).
{ intros a Ha. right; left. split.
  - apply (mk_fp_seg (mv_c v) (mv_k0 v) (mf_final v) gi a Hgif). unfold seg_spec.MSEG_SIZE. lia.
  - exists bb, bm. split; [exact Hbin | rewrite Hg in Ha; lia]. }
(* 0x86894-0x868b4: a0 = g + 32, the check of its shadow byte (covered: 0), s5 = c from 128(s1), the store of 1
   (4 bytes) to g->model_set; the jump to KDONE *)
paj_run_to_tok RUNTO HS HJ2 SHOK Bspan MF_KDONE.
{ lazymatch goal with |- awr_ok ?sg ?bb0 ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb0 Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 37%nat (seg_spec.mseg_addr (mv_c v) gi));
    [ reflexivity | exact U37' | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; exact (Hst a Ha) |].
  awr_ok_tac. }
(* at 0x86cd0 (KDONE): the reader against the K-cut's, the stored flag, the copied model *)
lazymatch goal with
| HFr3 : frame_of E2 ?rs3 (mrestrict (w_H Wc) mem2) (mrestrict (w_H Wc) (ms_mem ms0)) |- _ =>
  assert (K3 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (seg_spec.mseg_addr (mv_c v) gi + 32 <= a < seg_spec.mseg_addr (mv_c v) gi + 36) ->
    rdW Wc (ms_mem ms0) a = rdW Wc mem2 a);
  [ intros a Ha HnS;
    refine (kept_of_frame E2 rs3 (w_H Wc) mem2 (ms_mem ms0)
      (fun x => seg_spec.mseg_addr (mv_c v) gi + 32 <= x < seg_spec.mseg_addr (mv_c v) gi + 36) HFr3 _ a Ha HnS);
    intros bb0 wlo whi x Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U37' in Hrr; lia|]);
    destruct Hin
  | ]
end.
pose proof (st_ok_pi_region_nth E2 _ _ 0 (YP09.mkRegion (Some 37%nat) 32 36 32 36 [YP09.mkChunk 32 (CVal 4 (SLit 1))])
  HS eq_refl) as HR0.
pose proof (field_of_region E2 _ 37%nat (seg_spec.mseg_addr (mv_c v) gi) _ _ _ _ _ 32 4%N (SLit 1) 1 HR0 U37'
  (or_introl eq_refl) eq_refl ltac:(zside) ltac:(zside)) as V32.
change (N.to_nat 4) with 4%nat in V32. cbn [ms_mem restrict] in V32.
set (low := h_fold vv 24) in *.
assert (Hlowlen : length low = mk_ln vl) by (unfold low; rewrite hfold_len, Hvl; reflexivity).
assert (Hnul : ~ In 0 low).
{ unfold low. apply hfold_nul. rewrite <- Hvv. intros Hin. destruct L4 as ((_ & Hn0) & _). apply Hn0.
  apply kmt_in_firstn in Hin. rewrite <- (firstn_skipn ov rest). apply in_or_app. right. exact Hin. }
assert (Hrng : Forall (fun b => 0 <= b < 256) low).
{ apply Forall_forall. intros z Iz. destruct (In_nth low z 0 Iz) as [i [Hi Hn]].
  assert (Hi' : (i < length (low ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (HZS i Hi') as Ez. rewrite app_nth1 in Ez by exact Hi. rewrite Hn in Ez.
  exact (sa_aview_rng _ _ _ _ _ Ez). }
(* the new block: m_upd mcc gi (ms_with_model low) (the KMOD model sub-lane's sa_mconf_with_model) *)
assert (MC3 : sa_mconf (rdW Wc (ms_mem ms0)) (mv_c v) (m_upd mcc gi (ms_with_model low))).
{ apply (sa_mconf_with_model (rdW Wc memc) (rdW Wc (ms_mem ms0)) (mv_c v) mcc gi low HMC Hgi
    ltac:(rewrite Hlowlen; lia) Hnul Hrng).
  - intros a Ha Hns Hnm. unfold seg_spec.MS_MODEL_SET, seg_spec.MS_MODEL in Hns, Hnm. rewrite Hlowlen in Hnm.
    rewrite K3 by lia. rewrite Hfr2; [rewrite HM1; reflexivity | lia | lia | rewrite HES; lia].
  - intros i Hi. rewrite length_app, Hlowlen in Hi. cbn [length] in Hi. unfold seg_spec.MS_MODEL.
    rewrite K3 by lia.
    replace (seg_spec.mseg_addr (mv_c v) gi + 36 + Z.of_nat i)
      with (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL + Z.of_nat i) by (unfold seg_spec.MS_MODEL; lia).
    rewrite Heff by lia. rewrite HM1.
    apply HZS. rewrite length_app, Hlowlen. cbn [length]. lia.
  - intros k Hk. specialize (V32 k Hk). unfold aview. unfold seg_spec.MS_MODEL_SET.
    rewrite V32. cbn [option_map]. f_equal. do 4 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. }
(* every cut fact at the new memory (the memcpy's scratch window below s1 and g + [32, 60) changed) *)
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) - ESTACK <= a < mf_s1 (mv_sp v)) ->
  ~ (seg_spec.mseg_addr (mv_c v) gi + 32 <= a < seg_spec.mseg_addr (mv_c v) gi + 60) ->
  rdW Wc (ms_mem ms0) a = rdW Wc memc a).
{ intros a Ha Hw Hb. rewrite K3 by lia. rewrite Hfr2; [rewrite HM1; reflexivity | lia | lia |].
  replace (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) with (mf_s1 (mv_sp v)) by lia. exact Hw. }
assert (KE : forall a, seg_spec.mseg_addr (mv_c v) gi + 32 <= a < seg_spec.mseg_addr (mv_c v) gi + 60 ->
  mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE) by (intros a Ha; rewrite Hg in Ha; unfold seg_spec.SEG_M_SIZE; lia).
destruct (mf_keep_art B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) regs1 (ms_mem ms0) _
  (mf_s1 (mv_sp v) - ESTACK) (mf_s1 (mv_sp v))
  (fun a => seg_spec.mseg_addr (mv_c v) gi + 32 <= a < seg_spec.mseg_addr (mv_c v) gi + 60)
  (m_upd mcc gi (ms_with_model low)) CX CORE CELLS RA HJ2 ltac:(intros r0 _; reflexivity)
  ltac:(rewrite HSTK, HES; lia) ltac:(lia) KW KE MC3) as (KC1 & KC2 & _ & KC4 & KC5).
(* the registers at KDONE *)
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19. prreg HS (21%bv : bv 5) F21.
  prreg HS (22%bv : bv 5) F22. prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25.
  prreg HS (26%bv : bv 5) F26.
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
  apply (KD v lyc Sc Wc (ms_regs ms0) (ms_mem ms0) _ pos (m_upd mcc gi (ms_with_model low)) (Some gi) (line + 1)
    (mf_next p rest) (mf_rest rest) CX LS FRM KC1 KC2).
  + apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms0) RA);
      first [ rewrite F2, OLD2 by lia; apply EE; reflexivity | rewrite F3, OLD2 by lia; apply EE; reflexivity
            | rewrite F4, OLD2 by lia; apply EE; reflexivity | rewrite F8, OLD2 by lia; apply EE; reflexivity
            | rewrite F9, OLD2 by lia; rewrite (EE 2%nat 2%bv eq_refl), R2, R9; reflexivity
            | rewrite F18, OLD2 by lia; rewrite E32, R18; reflexivity
            | rewrite F19, OLD2 by lia; apply EE; reflexivity | rewrite F25, OLD2 by lia; apply EE; reflexivity
            | rewrite F26, OLD2 by lia; apply EE; reflexivity ].
  + rewrite F24, OLD2 by lia. rewrite (EE 24%nat 24%bv eq_refl). exact H24.
  + lia.
  + destruct (m_upd_model_counters mcc gi low) as (M1 & M2 & M3 & _).
    apply (mf_loop_next v Wc (ms_mem ms0) mcc (Some gi) line p rest); [exact (KC5 _ _ _ _ _ LOOP) | exact Hne | lia | lia
      | rewrite M3; lia | cbn [mf_cur_ok]; rewrite m_upd_segs_len; exact Hgi].
  + exact HFIN.
  + exact (KC4 _ NP).
  + rewrite F21, OLD2 by lia. rewrite E33. reflexivity.
  + rewrite F22, OLD2 by lia. rewrite (EE 22%nat 22%bv eq_refl). exact H22.
Qed.

End e.
End f.
End d.
About mk_cpy_ok.
Print Assumptions mk_cpy_ok.
