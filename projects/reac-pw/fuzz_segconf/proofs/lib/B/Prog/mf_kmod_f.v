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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 248 of its 306 lines of code are new or changed and 395 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_KMOD: its piece f, from the
   cut MK_FRET 0x86870 (fold's return, lib/B/Prog/mf_kmod_m.v MK_FRET_stmt) to MK_RRET 0x86880 (fuzz_catalogue_row's
   return, MK_RRET_stmt). A sub-lane of a walk lane of the image-B m_file-family owner's G2B. proves no function (kind: segment lemma of
   m_file's image-B walk, S_MF_KMOD piece f: MK_FRET 0x86870 to MK_RRET).
   Adapted from image A's lib/A/Prog/m_file_s_kmod_b.v (a working branch: mkb_frame, mkb_low_addr, the
   call of fuzz_catalogue_row in mkb_call) and image B's lib/B/Prog/mf_krole_d.v (commit
   49f97829985c: the seed with its regions dropped, the run to a program call, kd_st_reg, kd_bytes_of_zs).

   THE CODE (listing m_file.fuzz_segconf.asan-ubsan.s lines 462-465):
     86870 mv s5,a0                 s5 = ln = |h_fold v 24| (fold's answer)
     86874 mv a0,s4                 a0 = low = FB + 32 (s4 = 144(s1), set at 0x86864)
     86878 mv a1,s5                 a1 = ln
     8687c jal fuzz_catalogue_row   a0 = cat_ptr catA (cat_row (h_fold v 24)), back at 0x86880 = MK_RRET
   No instruction reads or writes memory, so the run starts from m_file_sd.v's seed with its regions dropped
   (st_ok_pi_submem) and the memory at the jal is the cut's (m_file_k.v mf_keep_run0). No UBSan trap branch and no
   instrumented check in this code. The call goes through PaCall.cl_callS with fuzz_catalogue_row's contract
   (lib/B/Prog/fuzz_catalogue_row_c.v at BASE + AF_fuzz_catalogue_row = SIGMA SS_fuzz_catalogue_row by SIGP,
   SegInstB.STK_fuzz_catalogue_row = 8,256, footprint []); its premises: arodata_okP (m_file_k.v mf_rod_now), the
   bytes sb = zb (h_fold v 24) at low (from the cut's sa_zs; zs (zb l) = l), n = ln, sa_addr of low.i's first ln
   bytes (its shadow bytes 0 at the K cuts, the frame's 16 shadow bytes present: mkf_low_addr), sa_loc = the frame
   arm (m_file_sd.v mf_low_addr), sa_cat (mf_cat_now), the event budget (mf_nev). After the call m_file_k.v
   mf_keep_call0 carries every cut fact; low.i lies below the callee window [s1 - 8,256, s1) (the frame is below the
   allocator ceiling, s1 - 8,256 is above it), so its bytes and NUL are kept.
   POSITIONAL NAMES checked against image B's listing and lib/B/Prog/m_file_m.v by what they are: 9 (MK_FRET =
   AF_m_file + 0x730 = 0x86870, MK_RRET = AF_m_file + 0x740 = 0x86880 the return address of the jal at 0x8687c, x20 =
   s4 = low, x21 = s5, x10 = a0, x11 = a1, x27 = s11 = line + 1, low = FB + 32 the 144(s1) cell, catA = 0xa20a0 =
   fuzz_catalogue in the B nm, AF_fuzz_catalogue_row = 0x5a18 = 0x8a7d8 - 0x84dc0); 0 point elsewhere. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import fuzz_catalogue_row_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k m_file_iq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kmod_t mf_kmod_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the call's bytes: the list Z read at a through an ASan reader, as list byte, and back (mf_krole_d.v
   kd_bytes_of_zs) *)
Lemma mkf_bytes_of_zs : forall segs H mem a (l : list Z), sa_zs (aview segs H mem) a l ->
  sa_bytes (aview segs H mem) a (seg_spec.zb l) /\ seg_spec.zs (seg_spec.zb l) = l.
Proof.
intros segs H mem a l HZ.
assert (HR : Forall (fun z => 0 <= z < 256) l).
{ apply Forall_forall. intros z Hz. apply In_nth with (d := 0) in Hz as (i & Hi & <-).
  exact (sa_aview_rng segs H mem _ _ (HZ i Hi)). }
split; [|exact (sa_zs_zb l HR)].
intros i Hi. unfold seg_spec.zb in Hi. rewrite length_map in Hi. rewrite (HZ i Hi). f_equal.
unfold seg_spec.zb. rewrite (nth_indep _ ZB0 (Z_to_bv 8 0)) by (rewrite length_map; exact Hi).
rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
symmetry. apply Z.mod_small. exact (proj1 (Forall_forall _ _) HR _ (nth_In _ _ Hi)).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a register the symbolic state still names by an atom (mf_krole_d.v kd_st_reg) *)
Lemma mkf_st_reg : forall segs E ss (H : word -> bool) ms (r : bv 5) (n : nat),
  st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros segs E ss H ms r n HS Hr. rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the shared Section hypotheses (the KMOD piece plan) this piece uses *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis ROW : forall fx0 : YK11.FPState, fuzz_catalogue_row_contract (fx := fx0) SEGS B (BASE + AF_fuzz_catalogue_row) SegInstB.STK_fuzz_catalogue_row SegInstB.RLO_A SegInstB.RHI_A SegInstB.catA.
Let RUN := paj_run B LAWS.

(* =============================== the frame and the low buffer =============================== *)
(* what AR gives about the walk's own side-stack frame at a mid-walk state (image A's mkb_frame) *)
Lemma mkf_frame : forall v lyc Sc Wc memc mdc pos lowsh mcc,
mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
In (1, pos) (frames Sc) /\ frame_addr lyc 1 pos mod 32 = 0 /\ 4096 <= frame_addr lyc 1 pos /\
frame_addr lyc 1 pos + 128 <= alloc_ceiling /\ in_app (frame_addr lyc 1 pos) 128 /\
(forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 -> apresent (w_H Wc) memc a) /\
(forall i, 0 <= i < 16 -> apresent (w_H Wc) memc (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i)).
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CORE.
pose proof CORE as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFapp, HFceil, HFpres, HFSpres.
split; [exact Hfin|]. split; [exact HFal|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [exact HFapp|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
intros i Hi. unfold shadow_addr in HFSpres.
exact (proj1 (HFSpres i ltac:(change (128 / 8) with 16; lia))).
Qed.

(* low.i's first n <= 64 bytes are addressable: their shadow bytes are 0 at the K cuts (MF_LOW_ON; m_file_sd.v
   mf_low_addr), and the frame's 16 shadow bytes, which hold the shadow hull, are present (image A's mkb_low_addr) *)
Lemma mkf_low_addr : forall v lyc Sc Wc memc mdc pos mcc n,
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> 0 <= n <= 64 ->
sa_addr (rdW Wc memc) (frame_addr lyc 1 pos + 32) n.
Proof.
intros v lyc Sc Wc memc mdc pos mcc n CORE Hn.
destruct (mkf_frame v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE)
  as (Hfin & HFal & HF4096 & HFceil & HFapp & HFpres & HFSpres).
pose proof (proj1 (mf_low_addr B v lyc Sc Wc memc mdc pos mcc n CORE Hn)) as HRA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (F := frame_addr lyc 1 pos) in *.
assert (HSB : SHADOW_OFF = 2147450880) by reflexivity.
assert (Hq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (Hq0 : 0 <= F / 32) by (apply Z.div_pos; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
unfold sa_addr, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
split; [lia|]. split; [lia|]. split; [lia|].
split; [exact HRA|].
intros Hn0 s Hs. unfold shadow_addr in Hs.
replace (F + 32) with (F + 4 * 8) in Hs by lia. rewrite (Z.div_add F 4 8 ltac:(lia)) in Hs.
replace (F + 4 * 8 + n - 1) with (4 * (F / 32) * 8 + (31 + n)) in Hs by lia.
rewrite (Z.div_add_l (4 * (F / 32)) 8 (31 + n) ltac:(lia)) in Hs.
assert (H8 : F / 8 = 4 * (F / 32)).
{ rewrite Hq at 1. replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia. apply Z.div_mul. lia. }
assert (Hk : 4 <= (31 + n) / 8 <= 11).
{ pose proof (Z.div_mod (31 + n) 8 ltac:(lia)) as Hd31.
  pose proof (Z.mod_pos_bound (31 + n) 8 ltac:(lia)) as Hm31. lia. }
set (k := (31 + n) / 8) in *.
assert (Hs2 : SHADOW_OFF + F / 8 <= s < SHADOW_OFF + F / 8 + 16).
{ pose proof (Z.div_mod (F / 32) 2 ltac:(lia)).
  pose proof (Z.mod_pos_bound (F / 32) 2 ltac:(lia)).
  pose proof (Z.div_mod (SHADOW_OFF + (F / 8 + 4)) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (F / 8 + 4)) 8 ltac:(lia)).
  pose proof (Z.div_mod (SHADOW_OFF + (4 * (F / 32) + k)) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (4 * (F / 32) + k)) 8 ltac:(lia)).
  rewrite HSB in *. lia. }
apply (aview_some_of_apresent SEGS (w_H Wc) memc s).
replace s with (SHADOW_OFF + F / 8 + (s - (SHADOW_OFF + F / 8))) by lia.
apply HFSpres. lia.
Qed.

(* the seed at a K cut's pc with its regions dropped (a run that touches no memory; mf_krole_d.v kd_seed0) *)
Lemma mkf_seed0 : forall v lyc Sc Wc regs1 memc mdc pos mcc pc,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_regs_at B v lyc pos regs1 ->
  st_ok_pi SEGS VAL (mfE regs1 v lyc pos None 0 []) (mkSS pc sr_mf [] None mf_facts)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc pc CX CORE RA.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc None 0 [] pc false false [] false false []
  false CX CORE RB ltac:(intros Hf; discriminate Hf) ltac:(cbn [mf_cur_ptr]; lia) ltac:(intros Hf; discriminate Hf)
  ltac:(lia) ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
exact (st_ok_pi_submem _ (ss_mf pc false false [] false false [] false MF_LOW_ON) _ [] HS0 (submem_nil _) eq_refl).
Qed.

(* a register the run left at its own atom k keeps the cut's value *)
Lemma mkf_reg_keep : forall (H : word -> bool) ss ms regs1 v lyc pos (r : bv 5) (k : nat),
  st_ok SEGS (mfE regs1 v lyc pos None 0 []) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff k 0 -> Z.of_nat k = bv_unsigned r ->
  getr (ms_regs ms) r = getr regs1 r.
Proof.
intros H ss ms regs1 v lyc pos r k HS Hr Hk.
rewrite (mkf_st_reg SEGS _ ss H ms r k HS Hr). apply mfE_reg. exact Hk.
Qed.

(* ============================ 0x86870 .. 0x8687c: the call of fuzz_catalogue_row ============================ *)
Lemma mk_fret_ok : forall n, MK_RRET_stmt B n -> MK_FRET_stmt B n.
Proof.
intros n RRET. unfold MK_FRET_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest vv MB FIN NZ RNG ZS R10 R20.
pose proof MB as (CX & LS & FRM & CORE & CELLS & RA & LEN & NE & LOOP & NP & R27).
unfold mf_at.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBASE2.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
assert (HLN : Z.of_nat (length (h_fold vv 24)) <= 23) by (rewrite mkt_hfold_len; lia).
destruct (mkf_frame v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE)
  as (Hfin & HFal & HF4096 & HFceil & HFapp & HFpres & HFSpres).
destruct (mf_sp0 B v CX) as (S1 & S47 & S16).
destruct (mf_s1_facts B v CX) as (H1 & _ & _).
destruct (iq_s1 (mv_sp v) S16) as (_ & Ho16).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
assert (HSTK1 : SegInstB.STK_fuzz_catalogue_row = 8256) by (vm_compute; reflexivity).
rewrite HSTK in S1.
(* the seed at 0x86870, every region dropped *)
pose proof (mkf_seed0 v lyc Sc Wc regs1 memc mdc pos mcc MK_FRET CX CORE RA) as HS.
set (E := mfE regs1 v lyc pos None 0 []) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof (mfE_extra regs1 v lyc pos None 0 [] 0 ltac:(unfold A_TEXT; lia)) as E32.
cbn [Nat.add nth mf_extra map app] in E32. fold E in E32.
pose proof CORE as (HJ & _).
(* 0x86870-0x8687c: s5 = a0, a0 = s4, a1 = s5; the jal to fuzz_catalogue_row *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
(* the registers at the jal: the cut's on the registers the run did not touch, a0 = low, a1 = s5 = ln,
   ra = MK_RRET *)
assert (Q2 : getr (ms_regs ms) 2 = getr regs1 2)
  by (apply (mkf_reg_keep (w_H Wc) _ ms regs1 v lyc pos 2%bv 2%nat HS); vm_compute; reflexivity).
assert (Q3 : getr (ms_regs ms) 3 = getr regs1 3)
  by (apply (mkf_reg_keep (w_H Wc) _ ms regs1 v lyc pos 3%bv 3%nat HS); vm_compute; reflexivity).
assert (Q4 : getr (ms_regs ms) 4 = getr regs1 4)
  by (apply (mkf_reg_keep (w_H Wc) _ ms regs1 v lyc pos 4%bv 4%nat HS); vm_compute; reflexivity).
assert (Q8 : getr (ms_regs ms) 8 = getr regs1 8)
  by (apply (mkf_reg_keep (w_H Wc) _ ms regs1 v lyc pos 8%bv 8%nat HS); vm_compute; reflexivity).
assert (Q19 : getr (ms_regs ms) 19 = getr regs1 19)
  by (apply (mkf_reg_keep (w_H Wc) _ ms regs1 v lyc pos 19%bv 19%nat HS); vm_compute; reflexivity).
assert (Q22 : getr (ms_regs ms) 22 = getr regs1 22)
  by (apply (mkf_reg_keep (w_H Wc) _ ms regs1 v lyc pos 22%bv 22%nat HS); vm_compute; reflexivity).
assert (Q23 : getr (ms_regs ms) 23 = getr regs1 23)
  by (apply (mkf_reg_keep (w_H Wc) _ ms regs1 v lyc pos 23%bv 23%nat HS); vm_compute; reflexivity).
assert (Q24 : getr (ms_regs ms) 24 = getr regs1 24)
  by (apply (mkf_reg_keep (w_H Wc) _ ms regs1 v lyc pos 24%bv 24%nat HS); vm_compute; reflexivity).
assert (Q25 : getr (ms_regs ms) 25 = getr regs1 25)
  by (apply (mkf_reg_keep (w_H Wc) _ ms regs1 v lyc pos 25%bv 25%nat HS); vm_compute; reflexivity).
assert (Q27 : getr (ms_regs ms) 27 = getr regs1 27)
  by (apply (mkf_reg_keep (w_H Wc) _ ms regs1 v lyc pos 27%bv 27%nat HS); vm_compute; reflexivity).
assert (Q9 : getr (ms_regs ms) 9 = getr regs1 9).
{ rewrite (mkf_st_reg SEGS _ _ _ _ 9%bv 2%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos None 0 [] 2 (Z_to_bv 5 2) eq_refl).
  transitivity (w64 (mf_s1 (mv_sp v))); [exact R2 | symmetry; exact R9]. }
assert (Q18 : getr (ms_regs ms) 18 = getr regs1 18).
{ rewrite (mkf_st_reg SEGS _ _ _ _ 18%bv 32%nat HS) by (vm_compute; reflexivity).
  rewrite E32. symmetry. exact R18. }
assert (Q10 : getr (ms_regs ms) 10 = w64 (frame_addr lyc 1 pos + 32)).
{ rewrite (mkf_st_reg SEGS _ _ _ _ 10%bv 20%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos None 0 [] 20 (Z_to_bv 5 20) eq_refl). exact R20. }
assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat (length (h_fold vv 24)))).
{ rewrite (mkf_st_reg SEGS _ _ _ _ 11%bv 10%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos None 0 [] 10 (Z_to_bv 5 10) eq_refl). exact R10. }
assert (Q21 : getr (ms_regs ms) 21 = w64 (Z.of_nat (length (h_fold vv 24)))).
{ rewrite (mkf_st_reg SEGS _ _ _ _ 21%bv 10%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos None 0 [] 10 (Z_to_bv 5 10) eq_refl). exact R10. }
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + MK_RRET)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
    transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
  exact (codeptr_val E MK_RRET HEI). }
(* the jal's target *)
rewrite (SIGP SS_fuzz_catalogue_row ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_fuzz_catalogue_row) with AF_fuzz_catalogue_row by (vm_compute; reflexivity).
(* the cut's facts at the jal's memory (the run changed no byte) *)
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
  as (CORE' & CELLS' & NPk & LPk).
pose proof (NPk _ NP) as NP'. pose proof (LPk mcc (Some gi) line p rest LOOP) as LOOP'.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms))
  by exact (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q24 Q19 Q22 Q25).
pose proof (mf_sp_at B v lyc pos (ms_regs ms) CX RA') as Hsp1.
assert (Hsp : spZ (ms_regs ms) = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) by (rewrite Hsp1; lia).
destruct (mf_chain_at B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc (ms_regs ms) CX CORE' RA') as (ch1 & CH).
(* low.i's bytes at the jal: h_fold v 24 and its NUL *)
assert (HF64 : 0 <= frame_addr lyc 1 pos + 32 + 24 < 2 ^ 64) by lia.
assert (ZS' : sa_zs (rdW Wc (ms_mem ms)) (frame_addr lyc 1 pos + 32) (h_fold vv 24 ++ [0])).
{ apply (iq_zs_keep (rdW Wc memc)); [|exact ZS].
  intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply EQV. lia. }
assert (ZS0 : sa_zs (rdW Wc (ms_mem ms)) (frame_addr lyc 1 pos + 32) (h_fold vv 24)).
{ intros i Hi. rewrite <- (app_nth1 (h_fold vv 24) [0] 0 Hi). apply ZS'. rewrite length_app. cbn [length]. lia. }
destruct (mkf_bytes_of_zs SEGS (w_H Wc) (ms_mem ms) _ _ ZS0) as (HSB & HZB).
assert (HLB : Z.of_nat (length (h_fold vv 24)) = Z.of_nat (length (seg_spec.zb (h_fold vv 24))))
  by (unfold seg_spec.zb; rewrite length_map; reflexivity).
assert (Hn64 : 0 <= Z.of_nat (length (h_fold vv 24)) <= 64) by lia.
eapply SRr_bind.
{ apply (cl_callS B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_fuzz_catalogue_row))
    SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v)
    (mv_mem v) (mv_md v) [(1, pos)] lyc Sc mdq 0 SegInstB.STK_fuzz_catalogue_row [] EV_fuzz_catalogue_row
    (mf_s1 (mv_sp v) - mv_sp v) (Z_to_bv 64 (BASE + MK_RRET)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       getr regs2 10 = w64 (seg_spec.cat_ptr SegInstB.catA
         (cat_row (seg_spec.zs (seg_spec.zb (h_fold vv 24))))) /\
       sa_kept SEGS Wc (ms_mem ms) W2 mem2 (ms_regs ms) SegInstB.STK_fuzz_catalogue_row (fun _ => False) /\
       sa_noalloc B lyc Sc ly2 S2)
    HJ Hsp Ho16).
  - destruct H1 as [H1 | H1]; rewrite H1; lia.
  - rewrite HSTK1; lia.
  - rewrite HSTK, HSTK1. destruct H1 as [H1 | H1]; rewrite H1; lia.
  - rewrite Q3; exact R3.
  - rewrite Q4; exact R4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold MK_RRET, AF_m_file; lia | unfold MK_RRET, AF_m_file; reflexivity].
  - rewrite unsigned_lit_small by (unfold MK_RRET, AF_m_file; lia). unfold MK_RRET, AF_m_file; lia.
  - rewrite <- Hsp. exact CH.
  - intros HPRE1. eapply SRr_mono.
    + apply (ROW fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq ch1 (frame_addr lyc 1 pos + 32)
        (Z.of_nat (length (h_fold vv 24))) (seg_spec.zb (h_fold vv 24)) HPRE1
        (mf_rod_now B RELRO v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc CX CORE')
        Q10 ltac:(lia) Q11 ltac:(lia) HSB HLB
        (mkf_low_addr v lyc Sc Wc (ms_mem ms) mdq pos mcc _ CORE' Hn64)
        (or_intror (or_introl (proj2 (mf_low_addr B v lyc Sc Wc (ms_mem ms) mdq pos mcc _ CORE' Hn64))))
        (mf_cat_now B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc CX CORE')).
      pose proof (mf_nev B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc CX CORE').
      unfold EV_fuzz_catalogue_row. lia.
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJc & HPr & HK2).
      exists ly2, S2, regs2, mem2, md2. split; [rewrite Hc2, Q1; reflexivity|].
      split; [exact HJc|]. split; [exact HPr | exact HK2].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo & HJi & HP3 & (A0 & KEPT & NOAL)).
rewrite HZB in A0.
destruct (mf_keep_call0 B v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi)
  ly3 S3 W3 regs3 mem3 md3 (0 + EV_fuzz_catalogue_row) SegInstB.STK_fuzz_catalogue_row
  CX CORE' CELLS' RA' HJo ltac:(reflexivity) HP3 NOAL ltac:(rewrite HSTK1; lia) KEPT)
  as (Ely3 & HLS3 & CORE3 & CELLS3 & RAT3 & NPK & LOOPK).
subst ly3.
(* low.i lies below the callee window [s1 - 8,256, s1): its bytes are kept *)
assert (ZS3 : sa_zs (rdW W3 mem3) (frame_addr lyc 1 pos + 32) (h_fold vv 24 ++ [0])).
{ apply (iq_zs_keep (rdW Wc (ms_mem ms))); [|exact ZS'].
  intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
  apply KEPT; [lia | rewrite Hsp1, HSTK1; destruct H1 as [H1 | H1]; rewrite H1; lia | intros []]. }
apply (RRET v lyc S3 W3 regs3 mem3 md3 pos mcc gi line p rest vv).
- unfold mk_base.
  split; [exact CX|]. split; [exact (HLS3 LS)|]. split; [exact FRM|]. split; [exact CORE3|].
  split; [exact CELLS3|]. split; [exact RAT3|]. split; [exact LEN|]. split; [exact NE|].
  split; [exact (LOOPK _ _ _ _ _ LOOP')|]. split; [exact (NPK _ NP')|].
  transitivity (getr (ms_regs ms) 27); [exact (HP3 27 ltac:(unfold acallee_saved; lia)) | rewrite Q27; exact R27].
- exact FIN.
- exact NZ.
- exact RNG.
- exact ZS3.
- transitivity (getr (ms_regs ms) 21); [exact (HP3 21 ltac:(unfold acallee_saved; lia)) | exact Q21].
- exact A0.
Qed.
End e.
End f.
End d.

About mk_fret_ok.
Print Assumptions mk_fret_ok.
