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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 696 of its 746 lines of code are new or changed and 403 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc), the segment S_MF_HDRB: the join and the three short returns, each
   a run of a few instructions with no call in it, from an inner cut of m_file_s_hdrb_2.v to the next cut. Lane
   the HDRB segment lane of the G2 walk owner's G2 (the HDRB join sub-lane). Each lemma is `<the next statement's _F> -> <this statement's
   _F>`; no piece changes the FP state, so each is proved at one FP state fx0 and the next statement is taken there.
     hb5_join  : MF_TAIL_F n  -> MFH_JOIN_F n    JOIN  0x86c50 .. 0x86c80, then the tail 0x86cf8
     hb5_rref1 : MFH_JOIN_F n -> MFH_RREF1_F n   RREF1 0x86b18 `ld a3,48(s1)`, 0x86b1c `j 0x86c50`
     hb5_rref2 : MF_TAIL_F n  -> MFH_RREF2_F n   RREF2 0x86bd8 `sd zero,136(s1)`, `ld a7,144(s1)`, `j 0x86cf8`
     hb5_rmcpy : MFH_JOIN_F n -> MFH_RMCPY_F n   RMCPY 0x86c48 `ld a3,48(s1)`, `mv s6,s7`, into 0x86c50
   THE JOIN (listing dis/m_file.fuzz_segconf.asan.s): a7 := 144(s1) (the next line); the instrumented check of the
   4-byte load of c->gen (a load of the shadow byte whose address 56(s1) holds, (c + 0x23b0 >> 3) + the shadow base,
   and a compare; its slow path 0x86dc0 and the error path 0x87014-0x87018, a call of errpath_load4, which the proof
   shows is not reached); a0 := 136(s1) + 252 = &cur->gen; the check of the 4-byte store there (the shadow byte at
   (a0 >> 3) + s2 and a compare; slow path 0x86dd0; the error path 0x8701c, a call of errpath_store4, not reached);
   `lw a1,0(a3)` with a3 = c + 0x23b0 (c->gen); `sw a1,0(a0)` (cur->gen = c->gen); `j 0x86cf8`.
   THE SYMBOLIC STATE (m_file_sd.v's mf_seed, atoms there): JOIN pins a3 to SOff 33 0x23b0 and adds two regions, the
   gen cell of the block (atom 33, [0x23b0, 0x23b4), read-only, its chunk atom 52 = mc_gen mcc) and the entry's gen
   field (atom 37 = 136(s1) = &c->seg[i], [252, 256), written, no chunk), and the fact HPTR 4 on atom 37. Its two
   shadow entries are mkSHE 33 0 9144 (mf_she_blk) and mkSHE 37 0 260 (mf_she_at): the token executor's `covered x 8`
   asks 252 + 8 <= she_hi of the entry at atom 37, so the entry's range is [cur, cur + 260), inside the block because
   i < 32 (256 * 31 + 260 <= 9236). Both checks are then decided with no obligation. RREF1 / RMCPY run the seed
   alone. RREF2 runs the seed with the cell chunks taken as the caller's slot chunks (hb5_slx: every mf_cells slot
   but 136(s1)), because the statement does not bound the cursor cur0 the 136(s1) cell holds (mf_cur_ok of the start
   model mc0 only), and the seed's cells = true form asks mf_cur_ptr c cur0 < 2 ^ 64; 136(s1) is overwritten with 0.
   AFTER THE RUN: the bytes outside the run's write windows are kept (kept_of_frame), so m_file_k.v's mf_keep_run
   carries mf_core and mf_loop; mf_cells, 112(s1) and 144(s1) are read off the final slot region (hb5_slots); the
   JOIN's block holds m_upd mcc i (ms_with_gen (mc_gen mcc)) (m_file_s_hdrb_1.v's mconf_enc_seg / mseg_enc_gen
   through hb_bytes_upd, the stored word read off the final entry region). At the tail the line loop's facts step to
   the next line: the text half from m_file_k.v's mf_loop_next at the start model, the model half from
   m_file_s_hdrb_4.v's hb4_tail_model. Section hypothesis: VOBJS (the seed's literal bridge) only. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_find_c m_refuse_c m_file_m m_file_mdl
  m_file_sd m_file_k m_file_s_hdrb_1 m_file_s_hdrb_2 m_file_s_hdrb_3 m_file_s_hdrb_4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ===================================== the JOIN's state ===================================== *)
(* the gen cell of the block (atom 33): c->gen, read by `lw a1,0(a3)`, its value atom 52 = the first extra value *)
Definition hb5_r33 : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0x23b0 0x23b4 0 0 [YP09.mkChunk 0x23b0 (CVal 4 (SOff 52 0))].
(* the gen field of the entry cur = &c->seg[i] (atom 37): cur->gen, written by `sw a1,0(a0)` *)
Definition hb5_r37 : YP09.region := YP09.mkRegion (Some 37%nat) 252 256 252 256 [].
Definition hb5_ss_join : sstate :=
  add_atom (mkSS MFH_JOIN (sr_set sr_mf (13%bv : bv 5) (SOff 33 seg_spec.MC_GEN))
    (hb5_r37 :: hb5_r33 :: mf_regions true true [] false false [] false MF_LOW_OFF) None mf_facts) 37 (HPTR 4).
(* the two checks' shadow entries: the block up to c + 9144 (c->gen's granule), the entry up to cur + 260
   (`covered (SOff 37 252) 8` asks 252 + 8 <= she_hi) *)
Definition hb5_SH : list shent := [mkSHE 33 0 9144; mkSHE 37 0 260].
(* RREF2: every slot chunk of mf_cells but 136(s1), as the caller's slot chunks *)
Definition hb5_slx : list YP09.chunk :=
[YP09.mkChunk 24 (CVal 8 (SOff 33 seg_spec.MC_KNOCK)); YP09.mkChunk 32 (CVal 8 (SOff 33 seg_spec.MC_OVERFLOW));
 YP09.mkChunk 40 (CVal 8 (SOff 33 seg_spec.MC_NKEPT)); YP09.mkChunk 48 (CVal 8 (SOff 33 seg_spec.MC_GEN));
 YP09.mkChunk 56 (CVal 8 (mf_shx 33 seg_spec.MC_GEN)); YP09.mkChunk 64 (CVal 8 (SOff 33 seg_spec.MC_READING));
 YP09.mkChunk 72 (CVal 8 (mf_shx (A_OBJ MF_WORDS_OBJ) 0)); YP09.mkChunk 80 (CVal 8 (SOff (A_OBJ MF_WORDS_OBJ) 0));
 YP09.mkChunk 88 (CVal 8 (SOff 33 seg_spec.MC_N)); YP09.mkChunk 104 (CVal 8 (SOff 34 0));
 YP09.mkChunk 120 (CVal 8 (SOff 36 0)); YP09.mkChunk 128 (CVal 8 (SOff 33 0));
 YP09.mkChunk 152 (CVal 8 (SOff 34 32))].

(* membership of a concrete chunk in a concrete chunk list *)
Ltac hb5_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* every chunk of a concrete list is in the concrete list cs *)
Ltac hb5_incl := let ch := fresh "ch" in let Hch := fresh "Hch" in
  intros ch Hch; unfold hb5_slx in Hch; cbn [In] in Hch;
  repeat (destruct Hch as [<- | Hch]; [hb5_in |]); destruct Hch.

(* ===================================== byte-level helpers ===================================== *)
(* a value read through the ASan reader is a value of the restricted memory, and back *)
Lemma hb5_val_of_sa : forall segs H mem a n z, sa_val (aview segs H mem) a n z -> val_mem segs (mrestrict H mem) a n z.
Proof.
intros segs H mem a n z Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in Hv; [|discriminate].
injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hv. unfold YO0f.le_byte, YG0f.le_byte.
symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. apply Z.mod_pos_bound. lia.
Qed.
Lemma hb5_sa_of_val : forall segs H mem a n z, val_mem segs (mrestrict H mem) a n z -> sa_val (aview segs H mem) a n z.
Proof.
intros segs H mem a n z Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, YG0f.le_byte. apply bv_wrap_small. change (bv_modulus 8) with 256.
apply Z.mod_pos_bound. lia.
Qed.
(* the low word of a sign-extended 32-bit value (lib/Reusable/YI67.v sext32_low, restated) *)
Lemma hb5_sext32_low : forall x, 0 <= x < 2 ^ 32 -> (zcanon (bv_swrap 32 (x mod 2 ^ 32))) mod 2 ^ 32 = x.
Proof.
intros x Hx. unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
cbn -[Z.add Z.mul Z.modulo Z.div Z.sub]. lia.
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* an atom holding x, as a symbolic value *)
Lemma hb5_atom_val : forall E (n : nat) x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
sv_denot E (SOff n k) = Z_to_bv 64 (x + k).
Proof. intros E n x k Hn Hx. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by exact Hx. reflexivity. Qed.
(* the stored word of the JOIN: the low 4 bytes of the sign-extended load of c->gen *)
Lemma hb5_sext_val : forall E (n : nat) g, ew E n = Z_to_bv 64 g -> 0 <= g < 2 ^ 32 ->
bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) mod 2 ^ (8 * Z.of_N 4) = g.
Proof.
intros E n g Hn Hg. change (bv_unsigned (sv_denot E (SExt true 32 (SOff n 0)))) with (U E (SExt true 32 (SOff n 0))).
rewrite U_SExt, (U_atom E n g Hn ltac:(lia)). change (Z.of_N 32) with 32. change (8 * Z.of_N 4) with 32.
apply hb5_sext32_low. exact Hg.
Qed.

Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* the numbers every piece reads: the block below the ceiling, the stack above it, the frame *)
Lemma hb5_geo : forall v lyc Sc Wc memc mdc pos lowsh mcc,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
4096 <= mv_c v /\ mv_c v + seg_spec.SEG_M_SIZE <= alloc_ceiling /\ mv_c v mod 16 = 0 /\
alloc_ceiling + 8560 <= mv_sp v /\ mv_sp v <= 2 ^ 47 /\
mv_sp v - 304 <= mf_s1 (mv_sp v) <= mv_sp v - 288 /\
0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\
4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CX CORE.
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HMP as (_ & Hc16 & _).
destruct (mf_s1_facts B v CX) as (S1 & S2 & S3). destruct (mf_sp0 B v CX) as (P1 & P2 & P3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S3.
pose proof asan_consts as (C1 & _).
repeat split; try lia.
Qed.

(* mf_cells, 112(s1) and 144(s1) read off a slot region that holds the seed's slot chunks, with 136(s1) holding
   e136 = the cursor cur *)
Lemma hb5_slots : forall v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur np xs mem2 cs e136,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_regs_base v regs1 -> 0 <= np < 2 ^ 64 ->
region_ok SEGS (mfE regs1 v lyc pos cur np xs) (mrestrict (w_H Wc) mem2)
  (YP09.mkRegion (Some 2%nat) 24 160 24 160 cs) ->
(forall ch, In ch (mf_chunk112 :: YP09.mkChunk 136 (CVal 8 e136) :: mf_chunk144 :: hb5_slx) -> In ch cs) ->
sv_denot (mfE regs1 v lyc pos cur np xs) e136 = Z_to_bv 64 (mf_cur_ptr (mv_c v) cur) ->
0 <= mf_cur_ptr (mv_c v) cur < 2 ^ 64 ->
mf_cells v lyc pos mem2 Wc cur /\
val_mem SEGS (mrestrict (w_H Wc) mem2) (mf_s1 (mv_sp v) + 112) 8 (frame_addr lyc 1 pos) /\ mf_np v mem2 Wc np.
Proof.
intros v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur np xs mem2 cs e136 CX CORE RB Hnp HR HIN D136 Hcur.
destruct (hb5_geo v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
unfold seg_spec.SEG_M_SIZE in G2.
pose proof RB as (R2 & R8 & R9 & R18).
set (E := mfE regs1 v lyc pos cur np xs) in *.
pose proof (mfE_extra regs1 v lyc pos cur np xs 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos cur np xs 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos cur np xs 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos cur np xs 4 ltac:(unfold A_TEXT; lia)) as E36.
pose proof (mfE_extra regs1 v lyc pos cur np xs 6 ltac:(unfold A_TEXT; lia)) as E38.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36, E38. fold E in E32, E33, E34, E36, E38.
assert (EW : ew E (A_OBJ MF_WORDS_OBJ) = Z_to_bv 64 SegInstA.wordsA).
{ unfold E. rewrite mfE_img by (unfold A_OBJ, MF_WORDS_OBJ, A_TEXT, A_LIM; lia). rewrite (mf_words_obj VOBJS). reflexivity. }
assert (HWv : SegInstA.wordsA = 0xa1880) by reflexivity.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
set (s1 := mf_s1 (mv_sp v)) in *. set (c := mv_c v) in *. set (F := frame_addr lyc 1 pos) in *.
assert (U2 : bv_unsigned (ew E 2) = s1).
{ unfold E. rewrite (mfE_reg regs1 v lyc pos cur np xs 2 2%bv eq_refl), R2. apply mf_w64_u. lia. }
assert (FA : forall off (n : nat) k x, In (YP09.mkChunk off (CVal 8 (SOff n k))) cs -> ew E n = Z_to_bv 64 x ->
  0 <= x < 2 ^ 64 -> 0 <= x + k < 2 ^ 64 -> val_mem SEGS (mrestrict (w_H Wc) mem2) (s1 + off) 8 (x + k)).
{ intros off n k x Hc Hn Hx Hxk.
  exact (field_of_region E _ 2%nat s1 cs 24 160 24 160 off 8%N (SOff n k) (x + k) HR U2 Hc
    (hb5_atom_val E n x k Hn Hx) ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (FS : forall off (n : nat) k x, In (YP09.mkChunk off (CVal 8 (mf_shx n k))) cs -> ew E n = Z_to_bv 64 x ->
  0 <= x < 2 ^ 47 -> 0 <= k -> x + k < 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H Wc) mem2) (s1 + off) 8 (SHADOW_OFF + (x + k) / 8)).
{ intros off n k x Hc Hn Hx Hk Hxk.
  pose proof (Z.div_pos (x + k) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (x + k) 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
  exact (field_of_region E _ 2%nat s1 cs 24 160 24 160 off 8%N (mf_shx n k) (SHADOW_OFF + (x + k) / 8) HR U2 Hc
    (mf_denot_shx E n x k Hn E32 Hx Hk Hxk) ltac:(rewrite HSB; cbn; lia) ltac:(cbn; lia)). }
unfold seg_spec.MC_KNOCK, seg_spec.MC_OVERFLOW, seg_spec.MC_NKEPT, seg_spec.MC_GEN, seg_spec.MC_READING,
  seg_spec.MC_N in *.
split; [|split].
- unfold mf_cells. fold s1 c F.
  unfold seg_spec.MC_KNOCK, seg_spec.MC_OVERFLOW, seg_spec.MC_NKEPT, seg_spec.MC_GEN, seg_spec.MC_READING, seg_spec.MC_N.
  split; [apply (FA 24 33%nat 0x238c c); [apply HIN; hb5_in | exact E33 | lia | lia]|].
  split; [apply (FA 32 33%nat 0x2004 c); [apply HIN; hb5_in | exact E33 | lia | lia]|].
  split; [apply (FA 40 33%nat 0x23ac c); [apply HIN; hb5_in | exact E33 | lia | lia]|].
  split; [apply (FA 48 33%nat 0x23b0 c); [apply HIN; hb5_in | exact E33 | lia | lia]|].
  split; [apply (FS 56 33%nat 0x23b0 c); [apply HIN; hb5_in | exact E33 | lia | lia | lia]|].
  split; [apply (FA 64 33%nat 0x23b4 c); [apply HIN; hb5_in | exact E33 | lia | lia]|].
  split.
  { replace (SHADOW_OFF + SegInstA.wordsA / 8) with (SHADOW_OFF + (SegInstA.wordsA + 0) / 8) by (rewrite Z.add_0_r; reflexivity).
    apply (FS 72 (A_OBJ MF_WORDS_OBJ) 0 SegInstA.wordsA); [apply HIN; hb5_in | exact EW | rewrite HWv; lia | lia | rewrite HWv; lia]. }
  split.
  { replace SegInstA.wordsA with (SegInstA.wordsA + 0) by lia.
    apply (FA 80 (A_OBJ MF_WORDS_OBJ) 0 SegInstA.wordsA); [apply HIN; hb5_in | exact EW | rewrite HWv; lia | rewrite HWv; lia]. }
  split; [apply (FA 88 33%nat 0x2000 c); [apply HIN; hb5_in | exact E33 | lia | lia]|].
  split; [replace F with (F + 0) by lia; apply (FA 104 34%nat 0 F); [apply HIN; hb5_in | exact E34 | lia | lia]|].
  split.
  { replace (SHADOW_OFF + F / 8) with (SHADOW_OFF + F / 8 + 0) by lia.
    pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound F 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
    apply (FA 120 36%nat 0 (SHADOW_OFF + F / 8)); [apply HIN; hb5_in | exact E36 | rewrite HSB; lia | rewrite HSB; lia]. }
  split; [replace c with (c + 0) by lia; apply (FA 128 33%nat 0 c); [apply HIN; hb5_in | exact E33 | lia | lia]|].
  split.
  { exact (field_of_region E _ 2%nat s1 cs 24 160 24 160 136 8%N e136 (mf_cur_ptr c cur) HR U2
      ltac:(apply HIN; hb5_in) D136 ltac:(cbn; lia) ltac:(cbn; lia)). }
  apply (FA 152 34%nat 32 F); [apply HIN; hb5_in | exact E34 | lia | lia].
- replace F with (F + 0) by lia. apply (FA 112 34%nat 0 F); [apply HIN; hb5_in | exact E34 | lia | lia].
- unfold mf_np. fold s1. replace np with (np + 0) by lia.
  apply (FA 144 38%nat 0 np); [apply HIN; hb5_in | exact E38 | lia | lia].
Qed.

(* the awr_ok goal of a run from the seed alone: only the slots are written, inside the frame of 8,560 bytes *)
Lemma hb5_awr_seed : forall E pc cells hnp slx FP bl0 blc fr0 lyc own v,
mf_cx B v -> bv_unsigned (ew E 2) = mf_s1 (mv_sp v) ->
awr_ok SEGS B E (ss_mem (ss_mf pc cells hnp slx false false [] false MF_LOW_OFF)) SegInstA.STK_m_file (mv_sp v)
  FP bl0 blc fr0 lyc own.
Proof.
intros E pc cells hnp slx FP bl0 blc fr0 lyc own v CX U2.
destruct (mf_s1_facts B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK.
unfold ss_mf. cbn [ss_mem]. unfold mf_regions.
apply awr_ok_cons_ro; [unfold mf_r_saved; cbn [YP09.r_wlo YP09.r_whi]; lia|].
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
  [reflexivity | rewrite U2; lia | cbn [mf_r_slots YP09.r_wlo]; lia | cbn [mf_r_slots YP09.r_whi]; lia |].
apply awr_ok_cons_ro; [cbn [mf_r_fh YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbn [mf_r_low YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbn [mf_r_ft YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbn [mf_r_fs YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_nil.
Qed.

(* RREF2's caller slot chunks: every slot of mf_cells but 136(s1) *)
Lemma hb5_slx_ok : forall v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur cur' np xs,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur' np xs) (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))) hb5_slx.
Proof.
intros v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur cur' np xs CX CORE CELLS.
destruct (hb5_geo v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
unfold seg_spec.SEG_M_SIZE in G2.
set (E := mfE regs1 v lyc pos cur' np xs).
pose proof (mfE_extra regs1 v lyc pos cur' np xs 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos cur' np xs 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos cur' np xs 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos cur' np xs 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36. fold E in E32, E33, E34, E36.
assert (EW : ew E (A_OBJ MF_WORDS_OBJ) = Z_to_bv 64 SegInstA.wordsA).
{ unfold E. rewrite mfE_img by (unfold A_OBJ, MF_WORDS_OBJ, A_TEXT, A_LIM; lia). rewrite (mf_words_obj VOBJS). reflexivity. }
assert (HWv : SegInstA.wordsA = 0xa1880) by reflexivity.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
destruct CELLS as (C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C104 & C120 & C128 & C136 & C152).
set (s1 := mf_s1 (mv_sp v)) in *. set (c := mv_c v) in *. set (F := frame_addr lyc 1 pos) in *.
unfold hb5_slx. unfold seg_spec.MC_KNOCK, seg_spec.MC_OVERFLOW, seg_spec.MC_NKEPT, seg_spec.MC_GEN,
  seg_spec.MC_READING, seg_spec.MC_N in *.
repeat apply Forall_cons; try apply Forall_nil.
- apply (mf_chunk_atom E _ s1 24 33 _ c E33); [lia | lia | exact C24].
- apply (mf_chunk_atom E _ s1 32 33 _ c E33); [lia | lia | exact C32].
- apply (mf_chunk_atom E _ s1 40 33 _ c E33); [lia | lia | exact C40].
- apply (mf_chunk_atom E _ s1 48 33 _ c E33); [lia | lia | exact C48].
- apply (chunk_ok_val SEGS E _ s1 56 8 (mf_shx 33 0x23b0) (SHADOW_OFF + (c + 0x23b0) / 8));
    [ apply mf_denot_shx; [exact E33 | exact E32 | lia | lia | lia]
    | pose proof (Z.div_pos (c + 0x23b0) 8 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound (c + 0x23b0) 8 (2 ^ 47) ltac:(lia) ltac:(lia)); rewrite HSB; cbn; lia
    | cbn; lia | exact C56 ].
- apply (mf_chunk_atom E _ s1 64 33 _ c E33); [lia | lia | exact C64].
- apply (chunk_ok_val SEGS E _ s1 72 8 (mf_shx (A_OBJ MF_WORDS_OBJ) 0) (SHADOW_OFF + SegInstA.wordsA / 8));
    [ replace (SHADOW_OFF + SegInstA.wordsA / 8) with (SHADOW_OFF + (SegInstA.wordsA + 0) / 8) by (rewrite Z.add_0_r; reflexivity);
      apply mf_denot_shx; [exact EW | exact E32 | rewrite HWv; lia | lia | rewrite HWv; lia]
    | rewrite HSB, HWv; vm_compute; split; [discriminate | reflexivity] | cbn; lia | exact C72 ].
- apply (mf_chunk_atom E _ s1 80 (A_OBJ MF_WORDS_OBJ) 0 SegInstA.wordsA EW); [rewrite HWv; lia | rewrite HWv; lia | rewrite Z.add_0_r; exact C80].
- apply (mf_chunk_atom E _ s1 88 33 _ c E33); [lia | lia | exact C88].
- apply (mf_chunk_atom E _ s1 104 34 0 F E34); [lia | lia | rewrite Z.add_0_r; exact C104].
- pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound F 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
  apply (mf_chunk_atom E _ s1 120 36 0 (SHADOW_OFF + F / 8) E36); [rewrite HSB; lia | rewrite HSB; lia | rewrite Z.add_0_r; exact C120].
- apply (mf_chunk_atom E _ s1 128 33 0 c E33); [lia | lia | rewrite Z.add_0_r; exact C128].
- apply (mf_chunk_atom E _ s1 152 34 32 F E34); [lia | lia | exact C152].
Qed.

(* the JOIN's symbolic state and its shadow knowledge *)
Lemma hb5_join_seed : forall v lyc Sc Wc regs1 memc mdc pos mcc i np,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc (Some i) ->
mf_regs_base v regs1 -> getr regs1 13 = w64 (mv_c v + seg_spec.MC_GEN) -> mf_np v memc Wc np -> 0 <= np < 2 ^ 64 ->
(i < length (mc_seg mcc))%nat ->
st_ok_pi SEGS VAL (mfE regs1 v lyc pos (Some i) np [mc_gen mcc]) hb5_ss_join
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + MFH_JOIN)) memc (seg_rom SEGS))) /\
sh_ok SEGS (SOff 32 0) hb5_SH (mfE regs1 v lyc pos (Some i) np [mc_gen mcc]) (mrestrict (w_H Wc) memc).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc i np CX CORE CELLS RB R13 NP Hnp Hi.
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & Hmc & Hac & _).
destruct (hb_mconf_bounds _ _ _ Hmc) as (Bn & _ & Bg & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc (Some i) CX CORE Hi) as Hcur.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc (Some i) np [mc_gen mcc] MFH_JOIN
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
destruct (hb5_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbm).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mbc 1 pos HAR Hbc Hin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 1) with 128 in Hsep.
unfold in_app in Hbapp.
pose proof RB as (R2 & R8 & R9 & R18).
set (E := mfE regs1 v lyc pos (Some i) np [mc_gen mcc]) in *.
pose proof (mfE_extra regs1 v lyc pos (Some i) np [mc_gen mcc] 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos (Some i) np [mc_gen mcc] 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos (Some i) np [mc_gen mcc] 4 ltac:(unfold A_TEXT; lia)) as E36.
pose proof (mfE_extra regs1 v lyc pos (Some i) np [mc_gen mcc] 5 ltac:(unfold A_TEXT; lia)) as E37.
pose proof (mfE_xs regs1 v lyc pos (Some i) np [mc_gen mcc] 0 ltac:(unfold A_TEXT; lia)) as E52.
cbn [Nat.add nth mf_extra map app] in E33, E34, E36, E37, E52. fold E in E33, E34, E36, E37, E52.
cbn [mf_cur_ptr] in Hcur, E37.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
set (c := mv_c v) in *. set (F := frame_addr lyc 1 pos) in *. set (sp0 := mv_sp v) in *.
set (s1 := mf_s1 sp0) in *.
set (cur := seg_spec.mseg_addr c i) in *.
assert (Hcur_eq : cur = c + 256 * Z.of_nat i) by (unfold cur, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
unfold seg_spec.SEG_M_SIZE in *.
assert (B33 : base_val E (Some 33%nat) = c) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
assert (B37 : base_val E (Some 37%nat) = cur) by (cbn [base_val]; rewrite E37; apply unsigned_lit_small; lia).
assert (B34 : base_val E (Some 34%nat) = F) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + F / 8)
  by (cbn [base_val]; rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (B2 : base_val E (Some 2%nat) = s1).
{ cbn [base_val]. unfold E. rewrite (mfE_reg regs1 v lyc pos (Some i) np [mc_gen mcc] 2 2%bv eq_refl), R2.
  apply mf_w64_u. lia. }
assert (B8 : base_val E (Some 8%nat) = sp0).
{ cbn [base_val]. unfold E. rewrite (mfE_reg regs1 v lyc pos (Some i) np [mc_gen mcc] 8 8%bv eq_refl), R8.
  apply mf_w64_u. lia. }
(* a3 pinned to &c->gen *)
assert (D13 : sv_denot E (SOff 33 seg_spec.MC_GEN) = getr regs1 13).
{ rewrite (hb5_atom_val E 33 c seg_spec.MC_GEN E33 ltac:(lia)), R13. reflexivity. }
pose proof (ast_ok_pi_set_reg_fp E _ _ (13%bv : bv 5) (SOff 33 seg_spec.MC_GEN) HS0 eq_refl D13) as HS1.
(* the gen cell of the block *)
assert (R33ok : region_ok SEGS E (mrestrict (w_H Wc) memc) hb5_r33).
{ unfold region_ok, hb5_r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B33.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ c 0x23b0 4 (SOff 52 0) (mc_gen mcc));
    [ rewrite (hb5_atom_val E 52 (mc_gen mcc) 0 E52 ltac:(lia)), Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
  change (N.to_nat 4) with 4%nat. apply hb5_val_of_sa. exact (hb_rd_gen _ _ _ Hmc). }
assert (R33dis : all_disjoint E hb5_r33 (mf_regions true true [] false false [] false MF_LOW_OFF)).
{ apply all_disjoint_of_extents. unfold mf_regions, mf_r_saved, mf_r_slots, mf_r_fh, mf_r_low, mf_r_ft, mf_r_fs,
    extent_of_region, hb5_r33.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B33, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. rewrite HSB in *.
  pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ hb5_r33 HS1 ltac:(vm_compute; reflexivity) R33ok R33dis) as HS2.
(* the gen field of the entry *)
assert (R37ok : region_ok SEGS E (mrestrict (w_H Wc) memc) hb5_r37).
{ unfold region_ok, hb5_r37. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B37.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hbpres (cur + o) ltac:(lia))). }
assert (R37dis : all_disjoint E hb5_r37 (hb5_r33 :: mf_regions true true [] false false [] false MF_LOW_OFF)).
{ apply all_disjoint_of_extents. unfold mf_regions, mf_r_saved, mf_r_slots, mf_r_fh, mf_r_low, mf_r_ft, mf_r_fs,
    extent_of_region, hb5_r33, hb5_r37.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B37, B33, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. rewrite HSB in *.
  pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ hb5_r37 HS2 ltac:(vm_compute; reflexivity) R37ok R37dis) as HS3.
(* the fact on atom 37 *)
assert (F37 : afact_ok E 37 (HPTR 4)).
{ unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2]. rewrite E37, unsigned_lit_small by lia.
  split; [lia|]. split; [|lia]. change (2 ^ 4) with 16. rewrite Hcur_eq.
  replace (c + 256 * Z.of_nat i) with ((c / 16 + 16 * Z.of_nat i) * 16) by (pose proof (Z.div_mod c 16 ltac:(lia)); lia).
  apply Z_mod_mult. }
pose proof (st_ok_pi_add_fact E _ _ 37 (HPTR 4) HS3 F37) as HS4.
split; [exact HS4|].
(* the shadow entries *)
unfold hb5_SH, sh_ok. apply Forall_cons.
{ exact (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc (Some i) np [mc_gen mcc] 9144 CX CORE
    ltac:(unfold seg_spec.SEG_M_SIZE; lia)). }
apply Forall_cons; [|apply Forall_nil].
apply (mf_she_at E Wc memc 37 cur 260 (mfE_U32 regs1 v lyc pos (Some i) np [mc_gen mcc]) E37 ltac:(lia) ltac:(lia)).
- destruct (mf_addr_sub _ c 9236 cur 260 Hac ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & _ & HRA & _). exact HRA.
- intros x Hx. apply (mf_blk_app B v CX). unfold seg_spec.SEG_M_SIZE. fold c. lia.
Qed.

(* the JOIN's awr_ok: the entry's gen field (in the footprint and a live block) and the slots *)
Lemma hb5_join_awr : forall v lyc Sc Wc memc mdc pos mcc i regs1 np,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_regs_base v regs1 ->
(i < length (mc_seg (mf_final v)))%nat -> (i < 32)%nat ->
awr_ok SEGS B (mfE regs1 v lyc pos (Some i) np [mc_gen mcc]) (ss_mem hb5_ss_join) SegInstA.STK_m_file (mv_sp v)
  (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (ablocks B (mv_ly v) (mv_S v)) (ablocks B lyc Sc)
  (frames (mv_S v)) lyc [(1, pos)].
Proof.
intros v lyc Sc Wc memc mdc pos mcc i regs1 np CX CORE RB Hfin Hi32.
destruct (hb5_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
pose proof RB as (R2 & _).
set (E := mfE regs1 v lyc pos (Some i) np [mc_gen mcc]).
pose proof (mfE_extra regs1 v lyc pos (Some i) np [mc_gen mcc] 5 ltac:(unfold A_TEXT; lia)) as E37.
cbn [Nat.add nth mf_extra map app mf_cur_ptr] in E37. fold E in E37.
assert (U37 : bv_unsigned (ew E 37) = seg_spec.mseg_addr (mv_c v) i).
{ rewrite E37. apply unsigned_lit_small. unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE in *. lia. }
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v)).
{ unfold E. rewrite (mfE_reg regs1 v lyc pos (Some i) np [mc_gen mcc] 2 2%bv eq_refl), R2. apply mf_w64_u. lia. }
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
change (ss_mem hb5_ss_join) with (hb5_r37 :: hb5_r33 :: mf_regions true true [] false false [] false MF_LOW_OFF).
eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 37%nat (seg_spec.mseg_addr (mv_c v) i));
  [ reflexivity | exact U37
  | intros a Ha; cbn [hb5_r37 YP09.r_wlo YP09.r_whi] in Ha;
    exact (proj1 (hb3_entry_wr B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc i a CX CORE Hfin Hi32 ltac:(lia))) |].
apply awr_ok_cons_ro; [cbn [hb5_r33 YP09.r_wlo YP09.r_whi]; lia|].
unfold mf_regions.
apply awr_ok_cons_ro; [unfold mf_r_saved; cbn [YP09.r_wlo YP09.r_whi]; lia|].
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
  [reflexivity | rewrite U2; lia | cbn [mf_r_slots YP09.r_wlo]; lia | cbn [mf_r_slots YP09.r_whi]; lia |].
apply awr_ok_cons_ro; [cbn [mf_r_fh YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbn [mf_r_low YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbn [mf_r_ft YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbn [mf_r_fs YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_nil.
Qed.

(* the line loop's facts at the next line: the text half from mf_loop_next at the start model mc0, the model half
   from hb4_tail_model *)
Lemma hb5_loop_tail : forall v Wc memc mc0 cur0 mcc cur line p rest,
mf_loop v Wc memc mc0 cur0 line p rest -> hb_mod (mv_k0 v) mc0 mcc cur -> rest <> [] ->
mf_loop v Wc memc mcc cur (line + 1) (mf_next p rest) (mf_rest rest).
Proof.
intros v Wc memc mc0 cur0 mcc cur line p rest LP HM Hne.
pose proof LP as (_ & _ & _ & _ & _ & Hc0 & _).
destruct (mf_loop_next v Wc memc mc0 cur0 line p rest mc0 cur0 LP Hne ltac:(lia) ltac:(lia) ltac:(lia) Hc0)
  as (T1 & T2 & T3 & T4 & T5 & _).
destruct (hb4_tail_model v Wc memc mc0 mcc cur0 cur line p rest LP HM Hne) as (M1 & M2 & M3 & M4 & M5 & M6).
unfold mf_loop. exact (conj T1 (conj T2 (conj T3 (conj T4 (conj T5 (conj M1 (conj M2 (conj M3 (conj M4 (conj M5 M6)))))))))).
Qed.

(* the registers every cut names, from the run's final state: each is its own atom (s1 = atom 2, s2 = atom 32) *)
Lemma hb5_regs_at : forall E v lyc pos cur np xs (regs1 regs2 : bvmap 5 word),
E = mfE regs1 v lyc pos cur np xs -> mf_regs_at B v lyc pos regs1 ->
getr regs2 2 = ew E 2 -> getr regs2 3 = ew E 3 -> getr regs2 4 = ew E 4 -> getr regs2 8 = ew E 8 ->
getr regs2 9 = ew E 2 -> getr regs2 18 = ew E 32 -> getr regs2 19 = ew E 19 -> getr regs2 25 = ew E 25 ->
getr regs2 26 = ew E 26 -> mf_regs_at B v lyc pos regs2.
Proof.
intros E v lyc pos cur np xs regs1 regs2 HE RA Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q25 Q26. subst E.
pose proof RA as (RR2 & _ & _ & _ & RR9 & RR18 & _).
pose proof (mfE_extra regs1 v lyc pos cur np xs 0 ltac:(unfold A_TEXT; lia)) as E32.
cbn [Nat.add nth mf_extra map app] in E32.
apply (mf_regs_at_of B v lyc pos regs1 regs2 RA).
- rewrite Q2. apply mfE_reg. reflexivity.
- rewrite Q3. apply mfE_reg. reflexivity.
- rewrite Q4. apply mfE_reg. reflexivity.
- rewrite Q8. apply mfE_reg. reflexivity.
- rewrite Q9, (mfE_reg regs1 v lyc pos cur np xs 2 2%bv eq_refl), RR2, RR9. reflexivity.
- rewrite Q18, E32, RR18. reflexivity.
- rewrite Q19. apply mfE_reg. reflexivity.
- rewrite Q25. apply mfE_reg. reflexivity.
- rewrite Q26. apply mfE_reg. reflexivity.
Qed.
(* the nine register goals of hb5_regs_at, from the run's final state *)
Ltac hb5_rg HS := let Q := fresh "Q" in
  lazymatch goal with |- getr _ ?r = _ => prreg HS r Q; exact Q end.

(* ===================================== the four pieces at one FP state ===================================== *)
(* RREF1 0x86b18: a3 := 48(s1) = c + 0x23b0, then the join *)
Lemma hb5_rref1_at : forall n, MFH_JOIN_stmt B n -> MFH_RREF1_stmt B n.
Proof.
intros n HJn. unfold MFH_RREF1_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mc0 mcc cur0 line p rest i
  CX LS FRM CORE CELLS RA R24 Hlen Hne LP HM FIN R21 R22 NP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof HM as (Hi & _). unfold mf_cur_ok in Hi.
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc (Some i) CX CORE Hi) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mc0 cur0 line p rest CX CORE LP) as Hnp.
destruct (hb5_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc (Some i) (mf_next p rest) [] MFH_RREF1
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & Hmc & _).
pose proof RB as (R2 & _).
pose proof (mfE_extra regs1 v lyc pos (Some i) (mf_next p rest) [] 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos (Some i) (mf_next p rest) [] 5 ltac:(unfold A_TEXT; lia)) as E37.
cbn [Nat.add nth mf_extra map app] in E33, E37.
assert (U2 : bv_unsigned (ew (mfE regs1 v lyc pos (Some i) (mf_next p rest) []) 2) = mf_s1 (mv_sp v)).
{ rewrite (mfE_reg regs1 v lyc pos (Some i) (mf_next p rest) [] 2 2%bv eq_refl), R2. apply mf_w64_u. lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (mfE regs1 v lyc pos (Some i) (mf_next p rest) []) (mrestrict (w_H Wc) memc))
  by (unfold sh_ok; constructor).
remember (mfE regs1 v lyc pos (Some i) (mf_next p rest) []) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
unfold mf_at.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MFH_JOIN.
{ exact (hb5_awr_seed E MFH_RREF1 true true [] _ _ _ _ _ _ v CX U2). }
(* the bytes outside the slots are kept *)
set (s1 := mf_s1 (mv_sp v)) in *.
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 24 <= a < s1 + 160) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnR.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms) (fun x => s1 + 24 <= x < s1 + 160) HFr _ a Ha HnR).
  intros bb wlo whi x Hin Hr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; first [rewrite U2 in Hr; lia | lia] |]).
  destruct Hin. }
pose proof (st_ok_pi_region_nth E _ (restrict (w_H Wc) ms) 1%nat _ HS eq_refl) as HRS. cbn [restrict ms_mem] in HRS.
destruct (hb5_slots v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc (Some i) (mf_next p rest) [] (ms_mem ms) _ (SOff 37 0)
  CX CORE RB Hnp ltac:(rewrite <- HE; exact HRS) ltac:(hb5_incl)
  ltac:(rewrite <- HE; rewrite (hb5_atom_val _ 37 _ 0 E37 Hcur), Z.add_0_r; reflexivity) Hcur)
  as (CELLS' & V112' & NP').
assert (RWok : forall a, (s1 + 24 <= a < s1 + 160) -> mf_rw v lyc pos a)
  by (intros a Ha; unfold mf_rw; right; right; right; right; right; exact Ha).
unfold seg_spec.SEG_M_SIZE in G2.
assert (VSH' : forall j, 4 <= j < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + j) 1 MF_LOW_OFF).
{ intros j Hj. pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  apply (mf_val_keep Wc Wc memc (ms_mem ms) (fun x => s1 + 24 <= x < s1 + 160) _ 1 _ K);
    [unfold SHADOW_OFF; pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)); lia
    | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia
    | intros k Hk; unfold SHADOW_OFF; lia | exact (VSH j Hj)]. }
assert (MC' : sa_mconf (rdW Wc (ms_mem ms)) (mv_c v) mcc).
{ apply (mf_mconf_keep Wc Wc memc (ms_mem ms) (fun x => s1 + 24 <= x < s1 + 160) _ _ K);
    [lia | unfold seg_spec.SEG_M_SIZE; lia | intros a Ha; unfold seg_spec.SEG_M_SIZE in *; lia | exact Hmc]. }
destruct (mf_keep_run B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc (ms_mem ms) _ (fun x => s1 + 24 <= x < s1 + 160)
  MF_LOW_OFF mcc CX CORE HJ K RWok VSH' V112' MC') as (CORE' & LOOPK).
(* the registers *)
prreg HS (13%bv : bv 5) R13'. prreg HS (21%bv : bv 5) R21'. prreg HS (22%bv : bv 5) R22'.
prreg HS (24%bv : bv 5) R24'.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (hb5_regs_at E v lyc pos (Some i) (mf_next p rest) [] regs1 (ms_regs ms) HE RA); hb5_rg HS. }
pmkst HS.
apply (HJn v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mc0 mcc cur0 line p rest i CX LS FRM CORE' CELLS' RA');
  [ rewrite R24', HE, (mfE_reg regs1 v lyc pos (Some i) (mf_next p rest) [] 24 24%bv eq_refl); exact R24
  | exact Hlen | exact Hne | exact (LOOPK _ _ _ _ _ LP) | exact HM | exact FIN
  | rewrite R13', E33, unsigned_lit_small by lia; reflexivity
  | rewrite R21', HE, (mfE_reg regs1 v lyc pos (Some i) (mf_next p rest) [] 21 21%bv eq_refl); exact R21
  | rewrite R22', HE, (mfE_reg regs1 v lyc pos (Some i) (mf_next p rest) [] 22 22%bv eq_refl); exact R22
  | exact NP' ].
Qed.

(* RMCPY 0x86c48: a3 := 48(s1) = c + 0x23b0, s6 := s7 = line + 1, then the join *)
Lemma hb5_rmcpy_at : forall n, MFH_JOIN_stmt B n -> MFH_RMCPY_stmt B n.
Proof.
intros n HJn. unfold MFH_RMCPY_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mc0 mcc cur0 line p rest i
  CX LS FRM CORE CELLS RA R24 Hlen Hne LP HM FIN R21 R23 NP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof HM as (Hi & _). unfold mf_cur_ok in Hi.
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc (Some i) CX CORE Hi) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mc0 cur0 line p rest CX CORE LP) as Hnp.
destruct (hb5_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc (Some i) (mf_next p rest) [] MFH_RMCPY
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & Hmc & _).
pose proof RB as (R2 & _).
pose proof (mfE_extra regs1 v lyc pos (Some i) (mf_next p rest) [] 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos (Some i) (mf_next p rest) [] 5 ltac:(unfold A_TEXT; lia)) as E37.
cbn [Nat.add nth mf_extra map app] in E33, E37.
assert (U2 : bv_unsigned (ew (mfE regs1 v lyc pos (Some i) (mf_next p rest) []) 2) = mf_s1 (mv_sp v)).
{ rewrite (mfE_reg regs1 v lyc pos (Some i) (mf_next p rest) [] 2 2%bv eq_refl), R2. apply mf_w64_u. lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (mfE regs1 v lyc pos (Some i) (mf_next p rest) []) (mrestrict (w_H Wc) memc))
  by (unfold sh_ok; constructor).
remember (mfE regs1 v lyc pos (Some i) (mf_next p rest) []) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
unfold mf_at.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MFH_JOIN.
{ exact (hb5_awr_seed E MFH_RMCPY true true [] _ _ _ _ _ _ v CX U2). }
set (s1 := mf_s1 (mv_sp v)) in *.
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 24 <= a < s1 + 160) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnR.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms) (fun x => s1 + 24 <= x < s1 + 160) HFr _ a Ha HnR).
  intros bb wlo whi x Hin Hr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; first [rewrite U2 in Hr; lia | lia] |]).
  destruct Hin. }
pose proof (st_ok_pi_region_nth E _ (restrict (w_H Wc) ms) 1%nat _ HS eq_refl) as HRS. cbn [restrict ms_mem] in HRS.
destruct (hb5_slots v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc (Some i) (mf_next p rest) [] (ms_mem ms) _ (SOff 37 0)
  CX CORE RB Hnp ltac:(rewrite <- HE; exact HRS) ltac:(hb5_incl)
  ltac:(rewrite <- HE; rewrite (hb5_atom_val _ 37 _ 0 E37 Hcur), Z.add_0_r; reflexivity) Hcur)
  as (CELLS' & V112' & NP').
assert (RWok : forall a, (s1 + 24 <= a < s1 + 160) -> mf_rw v lyc pos a)
  by (intros a Ha; unfold mf_rw; right; right; right; right; right; exact Ha).
unfold seg_spec.SEG_M_SIZE in G2.
assert (VSH' : forall j, 4 <= j < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + j) 1 MF_LOW_OFF).
{ intros j Hj. pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  apply (mf_val_keep Wc Wc memc (ms_mem ms) (fun x => s1 + 24 <= x < s1 + 160) _ 1 _ K);
    [unfold SHADOW_OFF; pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)); lia
    | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia
    | intros k Hk; unfold SHADOW_OFF; lia | exact (VSH j Hj)]. }
assert (MC' : sa_mconf (rdW Wc (ms_mem ms)) (mv_c v) mcc).
{ apply (mf_mconf_keep Wc Wc memc (ms_mem ms) (fun x => s1 + 24 <= x < s1 + 160) _ _ K);
    [lia | unfold seg_spec.SEG_M_SIZE; lia | intros a Ha; unfold seg_spec.SEG_M_SIZE in *; lia | exact Hmc]. }
destruct (mf_keep_run B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc (ms_mem ms) _ (fun x => s1 + 24 <= x < s1 + 160)
  MF_LOW_OFF mcc CX CORE HJ K RWok VSH' V112' MC') as (CORE' & LOOPK).
prreg HS (13%bv : bv 5) R13'. prreg HS (21%bv : bv 5) R21'. prreg HS (22%bv : bv 5) R22'.
prreg HS (24%bv : bv 5) R24'.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (hb5_regs_at E v lyc pos (Some i) (mf_next p rest) [] regs1 (ms_regs ms) HE RA); hb5_rg HS. }
pmkst HS.
apply (HJn v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mc0 mcc cur0 line p rest i CX LS FRM CORE' CELLS' RA');
  [ rewrite R24', HE, (mfE_reg regs1 v lyc pos (Some i) (mf_next p rest) [] 24 24%bv eq_refl); exact R24
  | exact Hlen | exact Hne | exact (LOOPK _ _ _ _ _ LP) | exact HM | exact FIN
  | rewrite R13', E33, unsigned_lit_small by lia; reflexivity
  | rewrite R21', HE, (mfE_reg regs1 v lyc pos (Some i) (mf_next p rest) [] 21 21%bv eq_refl); exact R21
  | rewrite R22', HE, (mfE_reg regs1 v lyc pos (Some i) (mf_next p rest) [] 23 23%bv eq_refl); exact R23
  | exact NP' ].
Qed.

(* RREF2 0x86bd8: 136(s1) := 0 (cur = NULL), a7 := 144(s1), then the tail *)
Lemma hb5_rref2_at : forall n, MF_TAIL_stmt B n -> MFH_RREF2_stmt B n.
Proof.
intros n HT. unfold MFH_RREF2_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mc0 mcc cur0 line p rest
  CX LS FRM CORE CELLS RA R24 Hlen Hne LP HM FIN R21 R22 NP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mc0 cur0 line p rest CX CORE LP) as Hnp.
destruct (hb5_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc None (mf_next p rest) [] MFH_RREF2
  false true hb5_slx false false [] false CX CORE RB ltac:(discriminate) ltac:(cbn; lia) (fun _ => NP) Hnp
  ltac:(unfold MF_LOW_OFF; lia)
  (hb5_slx_ok v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur0 None (mf_next p rest) [] CX CORE CELLS)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & Hmc & _).
pose proof RB as (R2 & _).
pose proof (mfE_extra regs1 v lyc pos None (mf_next p rest) [] 6 ltac:(unfold A_TEXT; lia)) as E38.
cbn [Nat.add nth mf_extra map app] in E38.
assert (U2 : bv_unsigned (ew (mfE regs1 v lyc pos None (mf_next p rest) []) 2) = mf_s1 (mv_sp v)).
{ rewrite (mfE_reg regs1 v lyc pos None (mf_next p rest) [] 2 2%bv eq_refl), R2. apply mf_w64_u. lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (mfE regs1 v lyc pos None (mf_next p rest) []) (mrestrict (w_H Wc) memc))
  by (unfold sh_ok; constructor).
remember (mfE regs1 v lyc pos None (mf_next p rest) []) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
unfold mf_at.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_TAIL.
{ exact (hb5_awr_seed E MFH_RREF2 false true hb5_slx _ _ _ _ _ _ v CX U2). }
set (s1 := mf_s1 (mv_sp v)) in *.
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 24 <= a < s1 + 160) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnR.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms) (fun x => s1 + 24 <= x < s1 + 160) HFr _ a Ha HnR).
  intros bb wlo whi x Hin Hr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; first [rewrite U2 in Hr; lia | lia] |]).
  destruct Hin. }
pose proof (st_ok_pi_region_nth E _ (restrict (w_H Wc) ms) 1%nat _ HS eq_refl) as HRS. cbn [restrict ms_mem] in HRS.
destruct (hb5_slots v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc None (mf_next p rest) [] (ms_mem ms) _ (SLit 0)
  CX CORE RB Hnp ltac:(rewrite <- HE; exact HRS) ltac:(hb5_incl) ltac:(reflexivity) ltac:(cbn; lia))
  as (CELLS' & V112' & NP').
assert (RWok : forall a, (s1 + 24 <= a < s1 + 160) -> mf_rw v lyc pos a)
  by (intros a Ha; unfold mf_rw; right; right; right; right; right; exact Ha).
unfold seg_spec.SEG_M_SIZE in G2.
assert (VSH' : forall j, 4 <= j < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + j) 1 MF_LOW_OFF).
{ intros j Hj. pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  apply (mf_val_keep Wc Wc memc (ms_mem ms) (fun x => s1 + 24 <= x < s1 + 160) _ 1 _ K);
    [unfold SHADOW_OFF; pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)); lia
    | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia
    | intros k Hk; unfold SHADOW_OFF; lia | exact (VSH j Hj)]. }
assert (MC' : sa_mconf (rdW Wc (ms_mem ms)) (mv_c v) mcc).
{ apply (mf_mconf_keep Wc Wc memc (ms_mem ms) (fun x => s1 + 24 <= x < s1 + 160) _ _ K);
    [lia | unfold seg_spec.SEG_M_SIZE; lia | intros a Ha; unfold seg_spec.SEG_M_SIZE in *; lia | exact Hmc]. }
destruct (mf_keep_run B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc (ms_mem ms) _ (fun x => s1 + 24 <= x < s1 + 160)
  MF_LOW_OFF mcc CX CORE HJ K RWok VSH' V112' MC') as (CORE' & LOOPK).
prreg HS (17%bv : bv 5) R17'. prreg HS (21%bv : bv 5) R21'. prreg HS (22%bv : bv 5) R22'.
prreg HS (24%bv : bv 5) R24'.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (hb5_regs_at E v lyc pos None (mf_next p rest) [] regs1 (ms_regs ms) HE RA); hb5_rg HS. }
pose proof (hb_mf_rest_lt rest Hne) as Hrl.
pmkst HS.
apply (HT v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc None (line + 1) (mf_next p rest) (mf_rest rest)
  CX LS FRM CORE' CELLS' RA');
  [ rewrite R24', HE, (mfE_reg regs1 v lyc pos None (mf_next p rest) [] 24 24%bv eq_refl); exact R24
  | lia | exact (hb5_loop_tail v Wc (ms_mem ms) mc0 cur0 mcc None line p rest (LOOPK _ _ _ _ _ LP) HM Hne)
  | exact FIN
  | rewrite R17', E38; reflexivity
  | rewrite R21', HE, (mfE_reg regs1 v lyc pos None (mf_next p rest) [] 21 21%bv eq_refl); exact R21
  | rewrite R22', HE, (mfE_reg regs1 v lyc pos None (mf_next p rest) [] 22 22%bv eq_refl); exact R22 ].
Qed.

(* JOIN 0x86c50: a7 := 144(s1), the checks of c->gen and cur->gen, cur->gen := c->gen, then the tail *)
Lemma hb5_join_at : forall n, MF_TAIL_stmt B n -> MFH_JOIN_stmt B n.
Proof.
intros n HT. unfold MFH_JOIN_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mc0 mcc cur0 line p rest i
  CX LS FRM CORE CELLS RA R24 Hlen Hne LP HM FIN R13 R21 R22 NP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof HM as (Hi & _). unfold mf_cur_ok in Hi.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mc0 cur0 line p rest CX CORE LP) as Hnp.
destruct (hb5_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & Hmc & _).
destruct (hb_mconf_bounds _ _ _ Hmc) as (Bn & _ & Bg & _).
assert (Hi32 : (i < 32)%nat) by lia.
(* the entry is one of the final model's *)
assert (Hfin : (i < length (mc_seg (mf_final v)))%nat).
{ rewrite <- FIN.
  assert (Hc : mf_cur_ok (m_upd mcc i (ms_with_gen (mc_gen mcc))) (Some i)).
  { unfold mf_cur_ok. rewrite (proj1 (m_upd_sizes mcc i _)), upd_nth_length. exact Hi. }
  destruct (hb_fin_grows (m_upd mcc i (ms_with_gen (mc_gen mcc)), Some i) line rest Hc) as [G _].
  cbn [fst] in G. rewrite (proj1 (m_upd_sizes mcc i _)), upd_nth_length in G. lia. }
destruct (hb5_join_seed v lyc Sc Wc regs1 memc mdc pos mcc i (mf_next p rest) CX CORE CELLS RB R13 NP Hnp Hi)
  as [HS SHOK].
pose proof RB as (R2 & _).
pose proof (mfE_extra regs1 v lyc pos (Some i) (mf_next p rest) [mc_gen mcc] 5 ltac:(unfold A_TEXT; lia)) as E37.
pose proof (mfE_extra regs1 v lyc pos (Some i) (mf_next p rest) [mc_gen mcc] 6 ltac:(unfold A_TEXT; lia)) as E38.
pose proof (mfE_xs regs1 v lyc pos (Some i) (mf_next p rest) [mc_gen mcc] 0 ltac:(unfold A_TEXT; lia)) as E52.
cbn [Nat.add nth mf_extra map app mf_cur_ptr] in E37, E38, E52.
assert (U2 : bv_unsigned (ew (mfE regs1 v lyc pos (Some i) (mf_next p rest) [mc_gen mcc]) 2) = mf_s1 (mv_sp v)).
{ rewrite (mfE_reg regs1 v lyc pos (Some i) (mf_next p rest) [mc_gen mcc] 2 2%bv eq_refl), R2. apply mf_w64_u. lia. }
unfold seg_spec.SEG_M_SIZE in G2.
set (cur := seg_spec.mseg_addr (mv_c v) i) in *.
assert (Hcur_eq : cur = mv_c v + 256 * Z.of_nat i) by (unfold cur, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
assert (U37 : bv_unsigned (ew (mfE regs1 v lyc pos (Some i) (mf_next p rest) [mc_gen mcc]) 37) = cur)
  by (rewrite E37; apply unsigned_lit_small; lia).
remember (mfE regs1 v lyc pos (Some i) (mf_next p rest) [mc_gen mcc]) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
unfold mf_at.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_TAIL.
{ rewrite HE. exact (hb5_join_awr v lyc Sc Wc memc mdc pos mcc i regs1 (mf_next p rest) CX CORE RB Hfin Hi32). }
(* the bytes outside the slots and the entry's gen field are kept *)
set (s1 := mf_s1 (mv_sp v)) in *.
set (RW := fun x => (s1 + 24 <= x < s1 + 160) \/ (cur + 252 <= x < cur + 256)).
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnR.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms) RW HFr _ a Ha HnR).
  intros bb wlo whi x Hin Hr. unfold RW. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hr;
     first [rewrite U2 in Hr; left; lia | rewrite U37 in Hr; right; lia | lia] |]).
  destruct Hin. }
(* the stored word: c->gen *)
pose proof (st_ok_pi_region_nth E _ (restrict (w_H Wc) ms) 0%nat _ HS eq_refl) as HR37. cbn [restrict ms_mem] in HR37.
pose proof (field_of_region_any E _ 37%nat cur _ 252 256 252 256 252 4%N (SExt true 32 (SOff 52 0)) HR37 U37
  ltac:(hb5_in) ltac:(cbn; lia)) as V252.
rewrite (hb5_sext_val E 52 (mc_gen mcc) E52 Bg) in V252. change (N.to_nat 4) with 4%nat in V252.
(* the slots *)
pose proof (st_ok_pi_region_nth E _ (restrict (w_H Wc) ms) 3%nat _ HS eq_refl) as HRS. cbn [restrict ms_mem] in HRS.
assert (Hcur : 0 <= mf_cur_ptr (mv_c v) (Some i) < 2 ^ 64) by (cbn [mf_cur_ptr]; fold cur; lia).
destruct (hb5_slots v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc (Some i) (mf_next p rest) [mc_gen mcc] (ms_mem ms) _
  (SOff 37 0) CX CORE RB Hnp ltac:(rewrite <- HE; exact HRS) ltac:(hb5_incl)
  ltac:(rewrite <- HE; rewrite (hb5_atom_val _ 37 _ 0 E37 ltac:(lia)), Z.add_0_r; reflexivity) Hcur)
  as (CELLS' & V112' & NP').
assert (RWok : forall a, RW a -> mf_rw v lyc pos a).
{ intros a [Ha | Ha]; unfold mf_rw;
    [right; right; right; right; right; exact Ha | right; left; unfold seg_spec.SEG_M_SIZE; lia]. }
assert (VSH' : forall j, 4 <= j < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + j) 1 MF_LOW_OFF).
{ intros j Hj. pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 44 - 2 ^ 20) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)).
  apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 1 _ K);
    [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH j Hj)].
  intros k Hk [HR | HR]; [unfold SHADOW_OFF in HR; lia|].
  apply (mf_blk_app B v CX (SHADOW_OFF + frame_addr lyc 1 pos / 8 + j + k));
    [unfold seg_spec.SEG_M_SIZE; lia | unfold SHADOW_OFF; lia]. }
(* the block holds the model with cur->gen = c->gen *)
assert (MC' : sa_mconf (rdW Wc (ms_mem ms)) (mv_c v) (m_upd mcc i (ms_with_gen (mc_gen mcc)))).
{ destruct Hmc as (bs & Hbs & Henc).
  destruct (mconf_enc_bounds _ _ _ Henc) as (Hlbs & _).
  assert (H9 : Z.of_nat (length bs) = 9236) by (rewrite Hlbs; reflexivity).
  exists (Mem.upd_bytes bs (256 * i + Z.to_nat seg_spec.MS_GEN) (Mem.le4 (Z_to_bv 64 (mc_gen mcc)))).
  split.
  - apply (hb_bytes_upd (rdW Wc memc) (rdW Wc (ms_mem ms)) (mv_c v) bs (256 * i + Z.to_nat seg_spec.MS_GEN)
      (Mem.le4 (Z_to_bv 64 (mc_gen mcc))) Hbs).
    + replace (mv_c v + Z.of_nat (256 * i + Z.to_nat seg_spec.MS_GEN)) with (cur + 252)
        by (rewrite Hcur_eq; unfold seg_spec.MS_GEN; lia).
      apply hb_bytes_of_val; [exact Bg|]. apply hb5_sa_of_val. exact V252.
    + rewrite Mem.length_le4. change (Z.to_nat seg_spec.MS_GEN) with 252%nat. lia.
    + intros a Ha Hna. rewrite H9 in Ha. rewrite Mem.length_le4 in Hna.
      change (Z.to_nat seg_spec.MS_GEN) with 252%nat in Hna.
      apply K; [lia|]. intros [HR | HR]; [lia|]. apply Hna. rewrite Hcur_eq in HR. lia.
  - apply (mconf_enc_seg false mcc bs i (ms_with_gen (mc_gen mcc)) (Z.to_nat seg_spec.MS_GEN)
      (Mem.le4 (Z_to_bv 64 (mc_gen mcc))) Henc Hi).
    + rewrite Mem.length_le4. change (Z.to_nat seg_spec.MS_GEN) with 252%nat. lia.
    + intros fb Hfb. apply mseg_enc_gen; [exact Hfb | exact Bg]. }
destruct (mf_keep_run B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc (ms_mem ms) _ RW
  MF_LOW_OFF (m_upd mcc i (ms_with_gen (mc_gen mcc))) CX CORE HJ K RWok VSH' V112' MC') as (CORE' & LOOPK).
prreg HS (17%bv : bv 5) R17'. prreg HS (21%bv : bv 5) R21'. prreg HS (22%bv : bv 5) R22'.
prreg HS (24%bv : bv 5) R24'.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (hb5_regs_at E v lyc pos (Some i) (mf_next p rest) [mc_gen mcc] regs1 (ms_regs ms) HE RA); hb5_rg HS. }
pose proof (hb_mf_rest_lt rest Hne) as Hrl.
pmkst HS.
apply (HT v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos (m_upd mcc i (ms_with_gen (mc_gen mcc))) (Some i) (line + 1)
  (mf_next p rest) (mf_rest rest) CX LS FRM CORE' CELLS' RA');
  [ rewrite R24', HE, (mfE_reg regs1 v lyc pos (Some i) (mf_next p rest) [mc_gen mcc] 24 24%bv eq_refl); exact R24
  | lia
  | exact (hb5_loop_tail v Wc (ms_mem ms) mc0 cur0 (m_upd mcc i (ms_with_gen (mc_gen mcc))) (Some i) line p rest
      (LOOPK _ _ _ _ _ LP) (hb4_mod_upd (mv_k0 v) mc0 mcc i (ms_with_gen (mc_gen mcc)) HM) Hne)
  | exact FIN
  | rewrite R17', E38; reflexivity
  | rewrite R21', HE, (mfE_reg regs1 v lyc pos (Some i) (mf_next p rest) [mc_gen mcc] 21 21%bv eq_refl); exact R21
  | rewrite R22', HE, (mfE_reg regs1 v lyc pos (Some i) (mf_next p rest) [mc_gen mcc] 22 22%bv eq_refl); exact R22 ].
Qed.

End e.
End f.
End d.

(* ============================ the four pieces at every FP state (the _F forms) ============================ *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Lemma hb5_join : forall n, MF_TAIL_F B n -> MFH_JOIN_F B n.
Proof. intros n HT fx0. exact (hb5_join_at (fx := fx0) B VOBJS n (HT fx0)). Qed.
Lemma hb5_rref1 : forall n, MFH_JOIN_F B n -> MFH_RREF1_F B n.
Proof. intros n HJn fx0. exact (hb5_rref1_at (fx := fx0) B VOBJS n (HJn fx0)). Qed.
Lemma hb5_rref2 : forall n, MF_TAIL_F B n -> MFH_RREF2_F B n.
Proof. intros n HT fx0. exact (hb5_rref2_at (fx := fx0) B VOBJS n (HT fx0)). Qed.
Lemma hb5_rmcpy : forall n, MFH_JOIN_F B n -> MFH_RMCPY_F B n.
Proof. intros n HJn fx0. exact (hb5_rmcpy_at (fx := fx0) B VOBJS n (HJn fx0)). Qed.
End i.
End h.
End g.
About hb5_join.
About hb5_rref1.
About hb5_rref2.
About hb5_rmcpy.
Print Assumptions hb5_join.
Print Assumptions hb5_rref1.
Print Assumptions hb5_rref2.
Print Assumptions hb5_rmcpy.
