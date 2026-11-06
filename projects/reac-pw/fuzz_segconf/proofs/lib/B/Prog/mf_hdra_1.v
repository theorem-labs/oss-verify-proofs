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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 189 of its 238 lines of code are new or changed and 404 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_HDRA, point walk 1 (hda_hdr): the walk
   of HDR 0x864f4 (MF_HDR, a header line) to RMC 0x86500 (HDA_RMC, memchr's return). proves no function (kind:
   segment lemma of m_file's image-B walk: the point HDR -> RMC of segment S_MF_HDRA).
   The code (the neutral listing of m_file in image B lines 239-242): 0x864f4 `li a1,93`,
   0x864f8 `mv a0,s10`, 0x864fc `jal` the memchr wrapper (SegList.v's PCall SS___interceptor_trampoline_memchr,
   SegAddr.v 0x43ac8 = wrapper_memchr), with a2 = e - s already set at 0x864e8; so memchr(s, ']', j - i) over the
   stripped line sl = slice i j (mf_line rest) = hda_sl rest i j at s = p + i (s10). No store, no instrumented
   check and no UBSan trap branch lies in this piece (the traps 0x86508 / 0x86518 / 0x86568 are after RMC).
   The seed is m_file_sd.v's mf_seed at MF_HDR (cells = true, hnp = true: the next line's address in 152(s1), no
   slx) with its frame-cell region [s1 + 16, s1 + 216) (region index 1) narrowed to read-only (set_window 0 0), so
   the token run to the jal changes no byte (hd1_frame_ro) and m_file_k.v's mf_keep_run0 carries every cut fact.
   The call is m_file_memchr.v's aj_memchr_atM (memchr writes only its window [s1 - ESTACK, s1)) under the row-20
   hypothesis AMEMCHR (MemchrDef.amemchr_realizesM at SegInstB.memchr_loA .. memchr_hiA) and the image fact MCROM;
   its premises come from the cut: the bytes [s, s + (j - i)) lie in the text left (mf_loop's sa_str), are
   addressable (mf_loop's sa_addr, m_file_k.v mf_addr_sub), are heap bytes below every callee window (m_file_sd.v
   mf_txt_heap_now / mf_heap_below_stack), and the read-only window from m_file_k.v's mf_rod_now (RELRO). memchr's
   answer kk (first_byte) is the model's memchr of sl (hd1_memchr_of_fb over mf_hdra_t.v's hd_memchr_of_first,
   hd_slice_length, hd_slice_nth, hd_line_nth, hd_line_le); m_file_k.v's mf_keep_art0 carries every cut fact and
   mf_regs_at across the call; s10 (x26), s4 (x20), s5 (x21), s11 (x27) are callee-saved.
   ADAPTED from image A's lib/A/Prog/m_file_s_hdra_11.v (a working branch) with its glue
   (m_file_s_hdra_w.v hda_frame_ro / hda_awr_ro / hda_np64 / hda_rg, m_file_s_hdra_e.v hda_txt_byte /
   hda_memchr_of_fb), renamed hd1_, at image B's numbers: frame cells [16, 216) (A [24, 160)), s1 = (sp0 - 320) & -32,
   STK_m_file = 8,592, mf_regs_at's eleven registers through m_file_k.v's mf_regs_at_of, s = s10 (A s11), e = s4
   (A s7). POSITIONAL NAMES checked against image B's listing by what they are: 14 (MF_HDR = AF_m_file + 0x3b4 =
   0x864f4, HDA_RMC = + 0x3c0 = 0x86500, AF_m_file = 0x1380 (SegList.v:12, BASE + AF_m_file = 0x86140), region 1 =
   mf_r_slots [16, 216), memchr's pc SIGMA SS___interceptor_trampoline_memchr = 0x43ac8, x10 a0 = s, x11 a1 = ']',
   x12 a2 = j - i, x1 ra, x26 s10 = s, x20 s4 = e, x21 s5 = 0x20, x27 s11 = line + 1, SegInstB.memchr_loA / hiA);
   4 point elsewhere than image A's same name (s = x26 not x27, e = x20 not x23, s5 = x21 not x22 / x17, the frame
   region [16, 216) not [24, 160)). A walk lane of the image-B m_file-family owner's G2B, point walk 1
   (a working branch). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k m_file_memchr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_hdra_t mf_hdra_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the write-permission goal of a run whose regions are all read-only (image A's hda_awr_ro) *)
Ltac hd1_awr_ro :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* a register the run left alone (the state holds its own atom k): its value at the seed, through EE (image A's
   hda_rg); a token run extends the environment with fresh atoms (ewset), which do not touch atom k *)
Ltac hd1_rg HS EE k r :=
  let Q := fresh "Q" in prreg HS r Q; repeat (rewrite ew_ewset_other in Q by lia); rewrite Q; exact (EE k r eq_refl).

(* byte x of the text left rest at p (its NUL at x = |rest|) (image A's hda_txt_byte) *)
Lemma hd1_txt_byte : forall rd p rest x, sa_str rd p rest -> (x <= length rest)%nat ->
  rd (p + Z.of_nat x) = Some (nth x rest 0).
Proof.
  intros rd p rest x ((HZ & _) & _) Hx.
  rewrite (HZ x ltac:(rewrite length_app; cbn [length]; lia)).
  destruct (Nat.eq_dec x (length rest)) as [->|Hne].
  - rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. rewrite nth_overflow by lia. reflexivity.
  - rewrite app_nth1 by lia. reflexivity.
Qed.

Section fb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* memchr(s, c, j - i) over the stripped line sl = hda_sl rest i j at s = p + i: the wrapper's answer kk
   (MemchrDef's first_byte) is the model's memchr of sl (image A's hda_memchr_of_fb, its length written j - i) *)
Lemma hd1_memchr_of_fb : forall segs (W : world segs) mem p rest i j c kk,
  sa_str (aview segs (w_H W) mem) p rest -> (i <= j <= length (mf_line rest))%nat ->
  first_byte segs W mem (p + Z.of_nat i) (Z.of_nat (j - i)) c kk ->
  exists k : nat, kk = Z.of_nat k /\ (k <= j - i)%nat /\
  memchr (hda_sl rest i j) c = (if (k <? j - i)%nat then Some k else None).
Proof.
  intros segs W mem p rest i j c kk HS Hij (Hk & Hne & Heq).
  pose proof (hd_line_le rest) as HL.
  assert (Lsl : length (hda_sl rest i j) = (j - i)%nat) by (unfold hda_sl; apply hd_slice_length; lia).
  assert (Hb : forall x, (x < j - i)%nat ->
    aview segs (w_H W) mem (p + Z.of_nat i + Z.of_nat x) = Some (nth x (hda_sl rest i j) 0)).
  { intros x Hx. unfold hda_sl. rewrite hd_slice_nth by lia. rewrite <- hd_line_nth by lia.
    replace (p + Z.of_nat i + Z.of_nat x) with (p + Z.of_nat (i + x)) by lia.
    apply hd1_txt_byte; [exact HS | lia]. }
  exists (Z.to_nat kk). split; [lia|]. split; [lia|].
  pose proof (hd_memchr_of_first (hda_sl rest i j) c (Z.to_nat kk)) as HM. rewrite Lsl in HM. apply HM.
  - lia.
  - intros x Hx Ex. destruct (Hne (Z.of_nat x) ltac:(lia)) as (b & Hb1 & Hb2).
    rewrite (Hb x ltac:(lia)) in Hb1. injection Hb1 as <-. exact (Hb2 Ex).
  - intros Hx. pose proof (Heq ltac:(lia)) as H1.
    replace kk with (Z.of_nat (Z.to_nat kk)) in H1 by lia.
    rewrite (Hb (Z.to_nat kk) Hx) in H1. injection H1 as H1. exact H1.
Qed.
End fb.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a run over a state whose regions are all read-only changed no byte (image A's hda_frame_ro) *)
Lemma hd1_frame_ro : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hro a. unfold aview, mbyte. rewrite HF; [reflexivity|].
intros (r & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.
(* the seed's range for the next line's address (image A's hda_np64) *)
Lemma hd1_np64 : forall v Wc memc mcc cur line p rest,
  mf_loop v Wc memc mcc cur line p rest -> 0 <= mf_next p rest < 2 ^ 64.
Proof.
intros v Wc memc mcc cur line p rest (_ & _ & _ & _ & (Hp0 & Hp1 & _) & _).
unfold mf_next. pose proof (Nat.le_sub_l (length rest) (length (mf_rest rest))). lia.
Qed.

Section e.
Variable B : asyms.
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  @MemchrDef.amemchr_realizesM fx0 rc SEGS B SegInstB.memchr_loA SegInstB.memchr_hiA (SIGMA SS___interceptor_trampoline_memchr).
Hypothesis MCROM : memchr_rom_fact SEGS B.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.

Lemma hda_hdr : forall n, HDA_RMC_stmt B n -> MF_HDR_stmt B n.
Proof.
intros n RMC. unfold MF_HDR_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j CX LS FRM CORE CELLS HR Hn Hr LOOP
  HL512 Hij HjL HSL HLB HFIN R26 R20 R12 R21 NP R27.
pose proof HR as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (_ & _ & _ & _ & _ & HCOK & _).
(* the seed at HDR, its frame cells read-only *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] MF_HDR
  true true [] false false [] false CX CORE (mf_regs_base_of B v lyc pos regs1 HR) (fun _ => CELLS)
  (mf_cur_range B _ _ _ _ _ _ _ _ _ _ CX CORE HCOK) (fun _ => NP) (hd1_np64 _ _ _ _ _ _ _ _ LOOP)
  ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_region_nth _ _ _ 1 (mf_r_slots true true []) HS0 ltac:(vm_compute; reflexivity)) as HR1.
pose proof (ast_ok_pi_set_region _ _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 0 0) HS0
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ _ _ _ 0 0 HR1 ltac:(intros o Ho; lia))) as HS.
clear HS0 HR1.
pose proof CORE as (HJ & _).
set (E := mfE regs1 v lyc pos cur (mf_next p rest) []) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew E k0 = getr regs1 r)
  by (intros k0 r Hk0; subst E; apply mfE_reg; exact Hk0).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF).
{ subst E. pose proof (mfE_extra regs1 v lyc pos cur (mf_next p rest) [] 0 ltac:(unfold A_TEXT; lia)) as X.
  cbn [Nat.add nth mf_extra map app] in X. exact X. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
unfold mf_at.
(* li a1,93; mv a0,s10; jal: the run stops at memchr's trampoline *)
paj_run_tok RUN HS HJ SHOK Bspan; [hd1_awr_ro|].
(* the run wrote no byte: every cut fact at the call's memory *)
pose proof (hd1_frame_ro _ _ (w_H Wc) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms) _ CX CORE CELLS HJ (fun a _ => KA a))
  as (CORE1 & CELLS1 & NPf1 & LPf1).
pose proof (LPf1 _ _ _ _ _ LOOP) as LOOP1. pose proof (NPf1 _ NP) as NP1. clear NPf1 LPf1.
(* the registers at the call: the cut's registers kept, a0 = s, a1 = ']', a2 = j - i, ra = RMC *)
assert (G2 : getr (ms_regs ms) 2 = getr regs1 2) by hd1_rg HS EE 2%nat (2%bv : bv 5).
assert (G3 : getr (ms_regs ms) 3 = getr regs1 3) by hd1_rg HS EE 3%nat (3%bv : bv 5).
assert (G4 : getr (ms_regs ms) 4 = getr regs1 4) by hd1_rg HS EE 4%nat (4%bv : bv 5).
assert (G8 : getr (ms_regs ms) 8 = getr regs1 8) by hd1_rg HS EE 8%nat (8%bv : bv 5).
assert (G9 : getr (ms_regs ms) 9 = getr regs1 9).
{ let Q := fresh "Q" in prreg HS (9%bv : bv 5) Q; repeat (rewrite ew_ewset_other in Q by lia);
  rewrite Q, (EE 2%nat 2%bv eq_refl), R2, R9; reflexivity. }
assert (G18 : getr (ms_regs ms) 18 = getr regs1 18).
{ let Q := fresh "Q" in prreg HS (18%bv : bv 5) Q; repeat (rewrite ew_ewset_other in Q by lia);
  rewrite Q, E32, R18; reflexivity. }
assert (G23 : getr (ms_regs ms) 23 = getr regs1 23) by hd1_rg HS EE 23%nat (23%bv : bv 5).
assert (G24 : getr (ms_regs ms) 24 = getr regs1 24) by hd1_rg HS EE 24%nat (24%bv : bv 5).
assert (G19 : getr (ms_regs ms) 19 = getr regs1 19) by hd1_rg HS EE 19%nat (19%bv : bv 5).
assert (G22 : getr (ms_regs ms) 22 = getr regs1 22) by hd1_rg HS EE 22%nat (22%bv : bv 5).
assert (G25 : getr (ms_regs ms) 25 = getr regs1 25) by hd1_rg HS EE 25%nat (25%bv : bv 5).
assert (G26 : getr (ms_regs ms) 26 = getr regs1 26) by hd1_rg HS EE 26%nat (26%bv : bv 5).
assert (G20 : getr (ms_regs ms) 20 = getr regs1 20) by hd1_rg HS EE 20%nat (20%bv : bv 5).
assert (G21 : getr (ms_regs ms) 21 = getr regs1 21) by hd1_rg HS EE 21%nat (21%bv : bv 5).
assert (G27 : getr (ms_regs ms) 27 = getr regs1 27) by hd1_rg HS EE 27%nat (27%bv : bv 5).
pose proof (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) HR G2 G3 G4 G8 G9 G18 G23 G24 G19 G22 G25) as RAg.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
repeat (rewrite ew_ewset_other in Q10 by lia). repeat (rewrite ew_ewset_other in Q12 by lia).
rewrite (EE 26%nat 26%bv eq_refl), R26 in Q10. rewrite (EE 12%nat 12%bv eq_refl), R12 in Q12.
pmkst HS.
(* the numbers memchr's row asks *)
pose proof RAg as ((_ & G3' & G4' & _) & _).
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ht0 & _ & _ & _ & (Ht00 & _) & _).
pose proof LOOP1 as (LP1 & LP2 & LP3 & LSTR & LADDR & _).
pose proof LADDR as (Hp0 & Hp63 & _).
pose proof (hd_line_le rest) as HLr.
destruct (mf_s1_facts B v CX) as (Hs1 & _ & _).
assert (Hs1m : (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0)
  by (destruct Hs1 as [E1 | E1]; rewrite E1; [replace (mv_sp v - 320 - mv_sp v) with (-320) by lia
      | replace (mv_sp v - 336 - mv_sp v) with (-336) by lia]; reflexivity).
assert (Hs1b : mf_s1 (mv_sp v) + 320 <= mv_sp v <= mf_s1 (mv_sp v) + 336) by (destruct Hs1 as [E1 | E1]; lia).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof (mf_sp_at B v lyc pos (ms_regs ms) CX RAg) as Usp.
assert (HBS : forall a, p <= a < p + Z.of_nat (length rest) + 1 -> a < mf_s1 (mv_sp v) - 2 * ESTACK).
{ intros a Ha. pose proof (mf_txt_heap_now B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as HTH.
  apply (mf_heap_below_stack B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc _ _ CX CORE HTH). rewrite LP3 in Ha. lia. }
assert (Hx0 : 0 < p + Z.of_nat i) by lia.
pose proof (mf_addr_sub _ p (Z.of_nat (length rest) + 1) (p + Z.of_nat i) (Z.of_nat (j - i)) LADDR
  ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & XAM & XRA & XHULL).
assert (Q1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + HDA_RMC)) by exact Q1.
(* memchr(s, ']', j - i) *)
eapply SRr_bind.
{ apply (aj_memchr_atM SEGS B LAWS pa_segs_low (SIGMA SS___interceptor_trampoline_memchr) SegInstB.RLO_A SegInstB.RHI_A
    (AMEMCHR fx) MCROM Wc (ms_regs ms) (ms_mem ms) SegInstB.STK_m_file (mv_sp v)
    (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc _ 0
    (p + Z.of_nat i) 93 (Z.of_nat (j - i)) (mf_s1 (mv_sp v) - mv_sp v) (Z_to_bv 64 (BASE + HDA_RMC)) HJ).
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - lia.
  - lia.
  - exact Hx0.
  - lia.
  - rewrite Usp. lia.
  - exact Hs1m.
  - lia.
  - rewrite HES, HSTK. lia.
  - exact G3'.
  - exact G4'.
  - exact Q1'.
  - apply ret_ok_codeptr_v; [unfold HDA_RMC, AF_m_file; lia | vm_compute; reflexivity].
  - intros a Ha. rewrite Usp. split.
    + replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
      rewrite (hd1_txt_byte _ p rest (Z.to_nat (a - p)) LSTR) by lia. discriminate.
    + pose proof (HBS a ltac:(lia)). rewrite HES in *. lia.
  - exact XAM.
  - exact XRA.
  - exact XHULL.
  - exact (mf_rod_now B RELRO v lyc Sc Wc (ms_mem ms) _ pos MF_LOW_OFF mcc CX CORE1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & kk & -> & HJ2 & HP2 & HFB & HRES & HK2 & HPR2).
replace (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) with (mf_s1 (mv_sp v)) in HK2 by lia.
(* every cut fact at memchr's return: memchr wrote only [s1 - ESTACK, s1) *)
destruct (mf_keep_art0 B v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos MF_LOW_OFF mcc cur regs2 mem2 md2
  (mf_s1 (mv_sp v) - ESTACK) (mf_s1 (mv_sp v)) CX CORE1 CELLS1 RAg HJ2 HP2
  ltac:(rewrite HES, HSTK; lia) ltac:(lia) HK2)
  as (CORE2 & CELLS2 & RA2 & NPf2 & LPf2).
(* memchr's answer kk is the model's memchr of sl *)
destruct (hd1_memchr_of_fb SEGS Wc (ms_mem ms) p rest i j 93 kk LSTR ltac:(lia) HFB) as (k & Ekk & Hk & HMC).
apply (RMC v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest i j k).
- exact (conj CX (conj LS (conj FRM (conj CORE2 (conj CELLS2 (conj Hn (conj Hr
    (conj (LPf2 _ _ _ _ _ LOOP1) (NPf2 _ NP1))))))))).
- exact RA2.
- unfold hda_hdr, hda_sl. split; [exact HL512|]. split; [exact Hij|]. split; [exact HjL|]. split; [exact HSL|].
  split; [exact HLB|]. rewrite HSL. exact HFIN.
- exact Hk.
- exact HMC.
- rewrite HRES, Ekk.
  destruct (Nat.ltb_spec k (j - i)) as [Hlt | Hge];
    destruct (Z.ltb_spec (Z.of_nat k) (Z.of_nat (j - i))) as [Hlt' | Hge']; try lia.
  + f_equal. lia.
  + reflexivity.
- transitivity (getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | rewrite G26; exact R26].
- transitivity (getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | rewrite G20; exact R20].
- transitivity (getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | rewrite G21; exact R21].
- transitivity (getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | rewrite G27; exact R27].
Qed.
End e.
End f.
End d.
About hda_hdr. Print Assumptions hda_hdr.
