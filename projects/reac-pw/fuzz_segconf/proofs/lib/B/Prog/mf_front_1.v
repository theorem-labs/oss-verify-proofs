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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 155 of its 203 lines of code are new or changed and 405 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_FRONT, piece 1 (fr_hd): the walk of
   HEAD 0x86378 to FR_SC 0x86384. The code (the neutral listing of m_file in image B lines
   144-146): 0x86378 `li a1,10`, 0x8637c `mv a0,s10`, 0x86380 `jal` the strchr trampoline (SegList.v's
   PCall SS___interceptor_trampoline_strchr), so strchr(p, '\n') over the text left rest at p; it returns to
   0x86384 = FR_SC (mf_front_m.v) with a0 = fr_nl p rest. No store, no instrumented check and no UBSan trap branch
   lies before the call.
   The seed is m_file_sd.v's mf_seed at MF_HEAD (cells = true, hnp = false, no slx) with its frame-cell region made
   read-only (no byte is written), so the token run to the jal keeps every byte (fr1_frame_ro) and m_file_k.v's
   mf_keep_run0 carries every cut fact. The call is mf_front_art.v's fr_art_at (PaArt.v's aj_art_at with no cells
   and without api_env) applied to the strchr row RtSeg.astrchr_realizes at the 2 * ESTACK window below s1, whose
   premises come from the cut: the text left is a C string with its slack (mf_loop's sa_str: SegABase.v
   sa_strz_bytes gives astr_at at seg_spec.zb rest, and zs (zb rest) = rest), addressable (mf_loop's sa_addr), in
   the text's heap block below every callee window (m_file_sd.v mf_heap_below_stack), its band room from the
   block's in_app (SegABase.v a3_amem_slack), and the ROM view (m_file_k.v mf_rom_now). strchr writes only its
   window [s1 - 2 * ESTACK, s1), so m_file_k.v's mf_keep_art0 carries every cut fact and mf_regs_at across it; s10,
   s5, s4 are callee-saved. The answer (no '\n': 0; else p + j at the first '\n' j) is fr_nl p rest by
   mf_front_mdl.v's fr_noNL / fr_firstNL.
   ADAPTED from image A's lib/A/Prog/m_file_s_hdra_11.v (a working branch: run to the jal, mf_keep_run0,
   the call, mf_keep_art0, the next point statement) and m_file_s_hdra_w.v (hda_ro_slots, hda_frame_ro,
   hda_awr_ro), at image B's numbers. A walk lane of the image-B m_file-family owner's G2B, piece 1
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_front_mdl mf_front_m mf_front_art.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the write-permission goal of a run whose regions are all read-only (image A's hda_awr_ro) *)
Ltac fr1_awr_ro :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* a register the run left alone (the state holds its own atom k): its value at the seed, through EE *)
Ltac fr1_rg HS EE k r :=
  let Q := fresh "Q" in prreg HS r Q; repeat (rewrite ew_ewset_other in Q by lia); rewrite Q; exact (EE k r eq_refl).

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
Lemma fr1_frame_ro : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hro a. unfold aview, mbyte. rewrite HF; [reflexivity|].
intros (r & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.

Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis STRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strchr).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.

Lemma fr_hd : forall n, FR_SC_stmt B n -> MF_HEAD_stmt B (S n).
Proof.
intros n SC. unfold MF_HEAD_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS HR Hn Hr LOOP HFIN R26 R21 R20.
pose proof HR as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (_ & _ & _ & _ & _ & HCOK & _).
(* the seed at HEAD, its frame cells read-only *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur 0 [] MF_HEAD true false [] false false []
  false CX CORE (mf_regs_base_of B v lyc pos regs1 HR) (fun _ => CELLS)
  (mf_cur_range B _ _ _ _ _ _ _ _ _ _ CX CORE HCOK) (fun H => False_ind _ (diff_false_true H)) ltac:(lia)
  ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_region_nth _ _ _ 1 (mf_r_slots true false []) HS0 ltac:(vm_compute; reflexivity)) as HR1.
pose proof (ast_ok_pi_set_region _ _ _ 1 (mf_r_slots true false []) (set_window (mf_r_slots true false []) 0 0) HS0
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ _ _ _ 0 0 HR1 ltac:(intros o Ho; lia))) as HS.
clear HS0 HR1.
pose proof CORE as (HJ & _).
set (E := mfE regs1 v lyc pos cur 0 []) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew E k0 = getr regs1 r)
  by (intros k0 r Hk0; subst E; apply mfE_reg; exact Hk0).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF).
{ subst E. pose proof (mfE_extra regs1 v lyc pos cur 0 [] 0 ltac:(unfold A_TEXT; lia)) as X.
  cbn [Nat.add nth mf_extra map app] in X. exact X. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
unfold mf_at.
(* li a1,10; mv a0,s10; jal: the run stops at strchr's trampoline *)
paj_run_tok RUN HS HJ SHOK Bspan; [fr1_awr_ro|].
(* the run wrote no byte: every cut fact at the call's memory *)
pose proof (fr1_frame_ro _ _ (w_H Wc) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms) _ CX CORE CELLS HJ (fun a _ => KA a))
  as (CORE1 & CELLS1 & NPf1 & LPf1).
pose proof (LPf1 _ _ _ _ _ LOOP) as LOOP1. clear NPf1 LPf1.
(* the registers at the call: the cut's registers kept, a0 = p, a1 = '\n', ra = FR_SC *)
assert (G2 : getr (ms_regs ms) 2 = getr regs1 2) by fr1_rg HS EE 2%nat (2%bv : bv 5).
assert (G3 : getr (ms_regs ms) 3 = getr regs1 3) by fr1_rg HS EE 3%nat (3%bv : bv 5).
assert (G4 : getr (ms_regs ms) 4 = getr regs1 4) by fr1_rg HS EE 4%nat (4%bv : bv 5).
assert (G8 : getr (ms_regs ms) 8 = getr regs1 8) by fr1_rg HS EE 8%nat (8%bv : bv 5).
assert (G9 : getr (ms_regs ms) 9 = getr regs1 9).
{ let Q := fresh "Q" in prreg HS (9%bv : bv 5) Q; repeat (rewrite ew_ewset_other in Q by lia);
  rewrite Q, (EE 2%nat 2%bv eq_refl), R2, R9; reflexivity. }
assert (G18 : getr (ms_regs ms) 18 = getr regs1 18).
{ let Q := fresh "Q" in prreg HS (18%bv : bv 5) Q; repeat (rewrite ew_ewset_other in Q by lia);
  rewrite Q, E32, R18; reflexivity. }
assert (G23 : getr (ms_regs ms) 23 = getr regs1 23) by fr1_rg HS EE 23%nat (23%bv : bv 5).
assert (G24 : getr (ms_regs ms) 24 = getr regs1 24) by fr1_rg HS EE 24%nat (24%bv : bv 5).
assert (G19 : getr (ms_regs ms) 19 = getr regs1 19) by fr1_rg HS EE 19%nat (19%bv : bv 5).
assert (G22 : getr (ms_regs ms) 22 = getr regs1 22) by fr1_rg HS EE 22%nat (22%bv : bv 5).
assert (G25 : getr (ms_regs ms) 25 = getr regs1 25) by fr1_rg HS EE 25%nat (25%bv : bv 5).
assert (G26 : getr (ms_regs ms) 26 = getr regs1 26) by fr1_rg HS EE 26%nat (26%bv : bv 5).
assert (G21 : getr (ms_regs ms) 21 = getr regs1 21) by fr1_rg HS EE 21%nat (21%bv : bv 5).
assert (G20 : getr (ms_regs ms) 20 = getr regs1 20) by fr1_rg HS EE 20%nat (20%bv : bv 5).
pose proof (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) HR G2 G3 G4 G8 G9 G18 G23 G24 G19 G22 G25) as RAg.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1.
repeat (rewrite ew_ewset_other in Q10 by lia).
rewrite (EE 26%nat 26%bv eq_refl), R26 in Q10.
pmkst HS.
(* the numbers strchr's row asks *)
pose proof RAg as ((_ & G3' & G4' & _) & _).
pose proof LOOP1 as (LP1 & LP2 & LP3 & LSTR1 & LADDR1 & _ & _ & Hl0 & Hl1 & _).
pose proof LSTR1 as ((HZ1 & Hn01) & HT1).
pose proof LADDR1 as (A0 & A1 & A2 & A3 & A4).
destruct (mf_s1_facts B v CX) as (Hs1 & _ & Hceil).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hs1m : (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0)
  by (destruct Hs1 as [E1 | E1]; rewrite E1; [replace (mv_sp v - 320 - mv_sp v) with (-320) by lia
      | replace (mv_sp v - 336 - mv_sp v) with (-336) by lia]; reflexivity).
assert (Hs1b : mf_s1 (mv_sp v) + 320 <= mv_sp v <= mf_s1 (mv_sp v) + 336) by (destruct Hs1 as [E1 | E1]; lia).
pose proof (mf_sp_at B v lyc pos (ms_regs ms) CX RAg) as Usp.
assert (HBS : forall a, p <= a < p + Z.of_nat (length rest) + 1 -> a < mf_s1 (mv_sp v) - 2 * ESTACK).
{ intros a Ha. pose proof (mf_txt_heap_now B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as HTH.
  apply (mf_heap_below_stack B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc _ _ CX CORE HTH). rewrite LP3 in Ha. lia. }
(* the text's heap block at the call: 4096 <= its base <= p, in_app *)
destruct (mf_txt_blk B v Wc memc mcc cur line p rest CX LOOP) as (bb & bm & Hbin0 & Hb1 & Hb2).
pose proof CORE as (_ & HPerm & _).
assert (Hbin : In (bb, bm) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbin0).
pose proof HJ as (HAR1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HAR1 Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbm).
pose proof (req_size_pos bm ltac:(lia)) as [_ Hreq].
assert (Hp0 : 0 < p) by lia.
(* the C string, its read range, its band room, its tail, the ROM view *)
assert (HLz : astr_len (seg_spec.zb rest) = Z.of_nat (length rest))
  by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
destruct (sa_strz_bytes SEGS (w_H Wc) (ms_mem ms) p rest (conj HZ1 Hn01)) as (HBy & HN & HZS).
assert (STRa : astr_at SEGS Wc (ms_mem ms) p (seg_spec.zb rest)) by exact (conj HBy HN).
assert (RDa : aread_ok SEGS (2 * ESTACK) Wc (ms_regs ms) (ms_mem ms) p (astr_len (seg_spec.zb rest) + 1)).
{ rewrite HLz.
  split; [exact A0|]. split; [exact A1|]. split; [lia|].
  split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
  intros a Ha. split.
  - replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
    rewrite (HZ1 (Z.to_nat (a - p))) by (rewrite length_app; cbn [length]; lia). discriminate.
  - unfold ascratch_stk. rewrite Usp. pose proof (HBS a ltac:(lia)). lia. }
assert (AMa : amem_range p (astr_len (seg_spec.zb rest) + 8)).
{ rewrite HLz. apply (a3_amem_slack bb (req_size bm) p _ Hbapp); lia. }
assert (TLa : atail_vis SEGS Wc (ms_mem ms) (p + astr_len (seg_spec.zb rest))) by (rewrite HLz; exact HT1).
pose proof (mf_rom_now B v lyc Sc Wc (ms_mem ms) _ pos MF_LOW_OFF mcc CX CORE1) as ROMa.
assert (Q1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + FR_SC)) by exact Q1.
assert (Hra : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite Q1'; apply ret_ok_codeptr_v; [unfold FR_SC, AF_m_file; lia | vm_compute; reflexivity]).
assert (Hsp' : spZ (ms_regs ms) = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) by (rewrite Usp; lia).
assert (Hneg' : mf_s1 (mv_sp v) - mv_sp v <= 0) by lia.
assert (Hbud' : 2 * ESTACK - (mf_s1 (mv_sp v) - mv_sp v) <= SegInstB.STK_m_file) by (rewrite HES, HSTK; lia).
(* strchr(p, '\n') *)
eapply SRr_bind.
{ eapply (fr_art_at SEGS B LAWS pa_segs_low (2 * ESTACK) (SIGMA SS___interceptor_trampoline_strchr) Wc (ms_regs ms)
    (ms_mem ms) SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v)
    (mv_mem v) (mv_md v) [(1, pos)] lyc Sc _ 0 (mf_s1 (mv_sp v) - mv_sp v) (Z_to_bv 64 (BASE + FR_SC)) _ HJ Hsp' Hs1m
    Hneg' ltac:(rewrite HES; lia) Hbud' Q1').
  apply (STRCHR fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ p 10 (seg_spec.zb rest)).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v))
      (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc (ms_mem ms) _ 0 (ms_regs ms)
      (mf_s1 (mv_sp v) - mv_sp v) HJ Hsp' Hs1m Hneg' ltac:(rewrite HES; lia) Hbud' Hra G3' G4').
  - exact Q10.
  - exact Q11.
  - lia.
  - exact Hp0.
  - exact STRa.
  - exact RDa.
  - exact AMa.
  - exact TLa.
  - exact ROMa. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
replace (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) with (mf_s1 (mv_sp v)) in HK2 by lia.
(* every cut fact at strchr's return: strchr wrote only [s1 - 2 * ESTACK, s1) *)
destruct (mf_keep_art0 B v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos MF_LOW_OFF mcc cur regs2 mem2 md2
  (mf_s1 (mv_sp v) - 2 * ESTACK) (mf_s1 (mv_sp v)) CX CORE1 CELLS1 RAg HJ2 HP2
  ltac:(rewrite HES, HSTK; lia) ltac:(lia) HK2)
  as (CORE2 & CELLS2 & RA2 & _ & LPf2).
(* strchr's answer is fr_nl p rest *)
assert (HZS2 : map (fun b : byte => bv_unsigned b) (seg_spec.zb rest) = rest) by exact HZS.
assert (HA0 : getr regs2 10 = w64 (fr_nl p rest)).
{ unfold fr_nl. destruct HQ2 as [[H0 Hn0] | (j & Hfa & Hj0)].
  - rewrite HZS2 in Hn0. destruct (fr_noNL rest Hn0) as (_ & _ & Eex). rewrite Eex. exact H0.
  - rewrite HZS2 in Hfa. destruct Hfa as (Hj & Hnj & Hfj).
    destruct (fr_firstNL rest j Hj Hnj Hfj) as (_ & _ & Elen & Eex). rewrite Eex, Elen. exact Hj0. }
apply (SC v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest).
- unfold fr_ctx. refine (conj CX (conj LS (conj FRM (conj CORE2 (conj CELLS2 (conj RA2 (conj _ (conj Hr
    (conj (LPf2 _ _ _ _ _ LOOP1) HFIN))))))))).
  lia.
- transitivity (getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | rewrite G26; exact R26].
- transitivity (getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | rewrite G21; exact R21].
- transitivity (getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | rewrite G20; exact R20].
- exact HA0.
Qed.
End e.
End f.
End d.
